import Lean.Elab.PreDefinition.Main
import Lean.Elab.Quotation

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab WF

namespace Derec

def naryVarNames (preDef : PreDefinition) : TermElabM (Array Name):= do
  -- TODO: Pretty names when no user name is available?
  lambdaTelescope preDef.value fun xs _ => do
    xs.mapM fun x => x.fvarId!.getUserName

/-- Given
  - matcherApp `match_i As (fun xs => motive[xs]) discrs (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining`, and
  - expression `e : B[discrs]`,
  returns the expressions `B[C_1[ys_1]])  ... B[C_n[ys_n]]`.
  (with `ys_i` as loose bound variable, ready to be `.instantiate`d)
  Cf. `MatcherApp.addArg`.
-/
def _root_.Lean.Meta.MatcherApp.transform (matcherApp : MatcherApp) (e : Expr) : MetaM (Array Expr) :=
  lambdaTelescope matcherApp.motive fun motiveArgs motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      -- This error can only happen if someone implemented a transformation that rewrites the motive created by `mkMatcher`.
      throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"

    let eAbst ← matcherApp.discrs.size.foldRevM (init := e) fun i eAbst => do
      let motiveArg := motiveArgs[i]!
      let discr     := matcherApp.discrs[i]!
      let eTypeAbst ← kabstract eAbst discr
      return eTypeAbst.instantiate1 motiveArg
    let eEq ← mkEq eAbst eAbst

    let matcherLevels ← match matcherApp.uElimPos? with
      | none     => pure matcherApp.matcherLevels
      | some pos =>
        pure <| matcherApp.matcherLevels.set! pos levelZero
    let motive ← mkLambdaFVars motiveArgs eEq
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
    let aux := mkApp aux motive
    let aux := mkAppN aux matcherApp.discrs
    unless (← isTypeCorrect aux) do
      throwError "failed to add argument to matcher application, type error when constructing the new motive"
    let auxType ← inferType aux
    let (altAuxs, _, _) ← Lean.Meta.forallMetaTelescope auxType
    let altAuxTys ← altAuxs.mapM inferType
    let res ← altAuxTys.mapM fun altAux => do
      let (fvs, _, body) ← Lean.Meta.forallMetaTelescope altAux
      let body := body.getArg! 2
      -- and abstract over the parameters of the alternative again
      Expr.abstractM body fvs
    return res

/--
  Given a `casesOn` application `c` of the form
  ```
  casesOn As (fun is x => motive[i, xs]) is major  (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining
  ```
  and a type `e : B[is, major]`, for every alternative `i`, construct the type
  ```
  B[C_i[ys_i]]
  ```
  (with `ys_i` as loose bound variable, ready to be `.instantiate`d)
-/
def _root_.Lean.Meta.CasesOnApp.transform (c : CasesOnApp) (e : Expr) : MetaM (Array Expr) :=
  lambdaTelescope c.motive fun motiveArgs _motiveBody => do
    unless motiveArgs.size == c.indices.size + 1 do
      throwError "failed to add argument to `casesOn` application, motive must be lambda expression with #{c.indices.size + 1} binders"
    let discrs := c.indices ++ #[c.major]
    let mut eAbst := e
    for motiveArg in motiveArgs.reverse, discr in discrs.reverse do
      eAbst := (← kabstract eAbst discr).instantiate1 motiveArg
    -- Up to this point, this is cargo-culted from `CasesOn.App.addArg`
    -- Let's create something Prop-typed that mentions `e`, by writing `e = e`.
    let eEq ← mkEq eAbst eAbst
    let motive ← mkLambdaFVars motiveArgs eEq
    let us := if c.propOnly then c.us else levelZero :: c.us.tail!
    -- Now instantiate the casesOn wth this synthetic motive
    let aux := mkAppN (mkConst c.declName us) c.params
    let aux := mkApp aux motive
    let aux := mkAppN aux discrs
    check aux
    let auxType ← inferType aux
    -- The type of the remaining arguments will mention `e` instantiated for each arg
    -- so extract them
    let (altAuxs, _, _) ← Lean.Meta.forallMetaTelescope auxType
    let altAuxTys ← altAuxs.mapM inferType
    let res ← altAuxTys.mapM fun altAux => do
      let (fvs, _, body) ← Lean.Meta.forallMetaTelescope altAux
      let body := body.getArg! 2
      -- and abstract over the parameters of the alternative again
      Expr.abstractM body fvs
    return res

@[reducible]
def M (recFnName : Name) (α β : Type) : Type :=
  StateRefT (Array α) (StateRefT (HasConstCache recFnName) TermElabM) β

partial def withRecApps {α} (recFnName : Name) (fixedPrefixSize : Nat) (e : Expr) (scrut : Expr)
    (k : Expr → Array Expr → TermElabM α) : TermElabM (Array α) := do
  trace[Elab.definition.wf] "withRecApps: {indentExpr e}"
  let (_, as) ← loop scrut e |>.run #[] |>.run' {}
  return as
where
  processRec (scrut : Expr) (e : Expr) : M recFnName α Unit := do
    if e.getAppNumArgs < fixedPrefixSize + 1 then
      loop scrut (← etaExpand e)
    else
      let a ← k scrut e.getAppArgs
      modifyThe (Array α) (·.push a)

  processApp (scrut : Expr) (e : Expr) : M recFnName α Unit := do
    e.withApp fun f args => do
      args.forM (loop scrut)
      if f.isConstOf recFnName then
        processRec scrut e
      else
        loop scrut f

  containsRecFn (e : Expr) : M recFnName α Bool := do
    modifyGetThe (HasConstCache recFnName) (·.contains e)

  loop (scrut : Expr) (e : Expr) : M recFnName α Unit := do
    if !(← containsRecFn e) then
      return
    -- trace[Elab.definition.wf] "loop: {indentExpr scrut}{indentExpr e}"
    match e with
    | Expr.lam n d b c =>
      loop scrut d
      withLocalDecl n c d fun x => do
        loop scrut (b.instantiate1 x)
    | Expr.forallE n d b c =>
      loop scrut d
      withLocalDecl n c d fun x => do
        loop scrut (b.instantiate1 x)
    | Expr.letE n type val body _ =>
      loop scrut type
      loop scrut val
      withLetDecl n type val fun x => do
        loop scrut (body.instantiate1 x)
    | Expr.mdata _d b =>
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop scrut b
      else
        loop scrut b
    | Expr.proj _n _i e => loop scrut e
    | Expr.const .. => if e.isConstOf recFnName then processRec scrut e
    | Expr.app .. =>
      match (← matchMatcherApp? e) with
      | some matcherApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp scrut e
        else
          let altScruts ← matcherApp.transform scrut
          (Array.zip matcherApp.alts altScruts).forM fun (alt, altScrut) =>
            lambdaTelescope alt fun xs altBody => do
              loop (altScrut.instantiateRev xs) altBody
      | none =>
      match (← toCasesOnApp? e) with
      | some casesOnApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp scrut e
        else
          let altScruts ← casesOnApp.transform scrut
          (Array.zip casesOnApp.alts altScruts).forM fun (alt, altScrut) =>
            lambdaTelescope alt fun xs altBody => do
              loop (altScrut.instantiateRev xs) altBody
      | none => processApp scrut e
    | e => do
      let _ ← ensureNoRecFn recFnName e

private partial def withUnary {α} (preDef : PreDefinition) (prefixSize : Nat) (mvarId : MVarId) (fvarId : FVarId)
    (k : MVarId → Array FVarId → TermElabM α) : TermElabM α := do
  let varNames ← lambdaTelescope preDef.value fun xs _ => do
    xs.mapM fun x => x.fvarId!.getUserName
  let mut mvarId := mvarId
  for localDecl in (← Term.getMVarDecl mvarId).lctx, varName in varNames[:prefixSize] do
    unless localDecl.userName == varName do
      mvarId ← mvarId.rename localDecl.fvarId varName
  let numPackedArgs := varNames.size - prefixSize
  let rec go (i : Nat) (mvarId : MVarId) (fvarId : FVarId) (fvarIds : Array FVarId) : TermElabM α := do
    trace[Elab.definition.wf] "withUnary: i: {i}, varNames: {varNames}, goal: {mvarId}"
    if i < numPackedArgs - 1 then
      let #[s] ← mvarId.cases fvarId #[{ varNames := [varNames[prefixSize + i]!] }] | unreachable!
      go (i+1) s.mvarId s.fields[1]!.fvarId! (fvarIds.push s.fields[0]!.fvarId!)
    else
      let mvarId ← mvarId.rename fvarId varNames.back
      k mvarId (fvarIds.push fvarId)
  go 0 mvarId fvarId #[]

/-- A `SavedLocalCtxt` captures the local context (e.g. of a recursive call),
so that it can be resumed later.
-/
structure SavedLocalCtxt where
  savedState : Term.SavedState
  savedLocalContext : LocalContext
  savedLocalInstances : LocalInstances
  savedTermContext : Term.Context

def SavedLocalCtxt.create : TermElabM SavedLocalCtxt := do
  let savedState ← saveState
  let savedLocalContext ← getLCtx
  let savedLocalInstances ← getLocalInstances
  let savedTermContext ← readThe Term.Context
  return { savedState, savedLocalContext, savedLocalInstances, savedTermContext }


def SavedLocalCtxt.run {α} (slc : SavedLocalCtxt) (k : TermElabM α) :
    TermElabM α := withoutModifyingState $ do
  restoreState slc.savedState
  withLCtx slc.savedLocalContext slc.savedLocalInstances do
  withTheReader Term.Context (fun _ => slc.savedTermContext) do
  k

def SavedLocalCtxt.within {α} (slc : SavedLocalCtxt) (k : TermElabM α) :
    TermElabM (SavedLocalCtxt × α) :=
  slc.run do
    let x ← k
    let slc' ← SavedLocalCtxt.create
    pure (slc', x)


/-- A `RecCallContext` focuses on a single recursive call in a unary predefinition,
and runs the given action in the context of that call.
-/
structure RecCallContext where
  --- Function index of caller
  caller : Nat
  --- Parameters of caller
  params : Array Expr
  --- Function index of callee
  callee : Nat
  --- Arguments to callee
  args : Array Expr
  ctxt : SavedLocalCtxt

/-- Given the packed argument of a (possibly) mutual and (possibly) nary call,
return the function index that is called and the arguments individually.
Cf. `packMutual`
TODO: pass in number of functions and arities to not overshoot
-/
def unpackArg (e : Expr) : (Nat × Array Expr) := Id.run do
  -- count PSum injections to find out which function is doing the call
  let mut funidx := 0
  let mut e := e
  while e.isAppOfArity ``PSum.inr 3 do
    e := e.getArg! 2
    funidx := funidx +1
  if e.isAppOfArity ``PSum.inl 3 then
    e := e.getArg! 2

  -- now unpack PSigmas
  let mut args := #[]
  while e.isAppOfArity ``PSigma.mk 4 do
    args := args.push (e.getArg! 2)
    e := e.getArg! 3
  args := args.push e
  return (funidx, args)

def RecCallContext.create (param arg : Expr) : TermElabM RecCallContext := do
  let (caller, params) := unpackArg param
  let (callee, args) := unpackArg arg
  return { caller, params, callee, args, ctxt := (← SavedLocalCtxt.create) }

-- def RecCallContext.run {α} (rcc : RecCallContext) (k : Expr → Expr → TermElabM α) :
--     TermElabM α := rcc.ctxt.run $ k rcc.param rcc.arg


/-- Traverse a unary PreDefinition, and returns a `WithRecCall` closure for each recursive
call site.
-/
def collectRecCalls (unaryPreDef : PreDefinition) (fixedPrefixSize : Nat)
    -- (k : Expr → Expr → TermElabM α) : TermElabM (Array α)
    : TermElabM (Array RecCallContext)
    := withoutModifyingState do
  lambdaTelescope unaryPreDef.value fun xs body => do
    trace[Elab.definition.wf] "lexGuessCol: {xs} {body}"
    -- assert xs.size  == fixedPrefixSize + 1
    let param := xs[fixedPrefixSize]!
    withRecApps unaryPreDef.declName fixedPrefixSize body param fun param args => do
      let arg := args[0]!
      RecCallContext.create param arg

inductive GuessLexRel | lt | eq | le | gt
deriving Repr, DecidableEq

def GuessLexRel.toNatRel : GuessLexRel → Expr
  | lt => mkAppN (mkConst ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat]
  | eq => mkAppN (mkConst ``Eq [levelOne]) #[mkConst ``Nat]
  | le => mkAppN (mkConst ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``instLENat]
  | gt => mkAppN (mkConst ``GT.gt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat]

def lexGuessCol (preDef : PreDefinition) (unaryPreDef : PreDefinition) (fixedPrefixSize : Nat)
    (packedArgType : Expr)
    (varNames : Array Name) (varIdx : Nat) : TermElabM (Array (Option GuessLexRel)):= do
  let recCalls ← collectRecCalls unaryPreDef fixedPrefixSize
  recCalls.mapM fun rcc => rcc.ctxt.run do
      trace[Elab.definition.wf] "lexGuesscol: {rcc.caller} {rcc.params} → {rcc.callee} {rcc.args}"
      addAsAxiom unaryPreDef
      for rel in [GuessLexRel.lt, .eq, .le, .gt] do
        let goalExpr := mkAppN rel.toNatRel #[rcc.args[varIdx]!, rcc.params[varIdx]!]
        trace[Elab.definition.wf] "Goal (unchecked): {goalExpr}"
        check goalExpr

        let mvar ← mkFreshExprSyntheticOpaqueMVar goalExpr
        let mvarId := mvar.mvarId!
        let mvarId ← mvarId.cleanup
        -- logInfo m!"Remaining goals: {goalsToMessageData [mvarId]}"
        try
          let remainingGoals ← Tactic.run mvarId do
            Tactic.evalTactic (← `(tactic| decreasing_tactic))
          remainingGoals.forM fun mvarId => Term.reportUnsolvedGoals [mvarId]
          let expr ← instantiateMVars mvar
          trace[Elab.definition.wf] "Found {repr rel} proof: {expr}"
          return rel
        catch e =>
          trace[Elab.definition.wf] "Did not find {repr rel} proof of {goalsToMessageData [mvarId]}"
      return .none

-- NB: An array of columns
def LexMatrix := Array (Array (Option GuessLexRel))

def LexMatrix.rows (m : LexMatrix) : Nat := (m.get! 0).size
def LexMatrix.cols (m : LexMatrix) : Nat := m.size
def LexMatrix.get (m : LexMatrix) (i : Nat) (j : Nat) := (m.get! i).get! j

def LexMatrix.pretty : LexMatrix → Array Name → Format := fun m names =>
  if m.isEmpty then "(no columns)" else
    let header := #["Recursions:"].append (names.map (·.toString))
    let rows := (List.range m.rows).toArray.map fun i =>
      #[s!"Call {i+1}"].append (m.map (fun col => prettyGuessLexRel col[i]!))
    let table := #[header].append rows
    prettyTable table
  where
    prettyGuessLexRel : Option GuessLexRel → String
      | none => "?"
      | some .lt => "<"
      | some .le => "≤"
      | some .gt => ">"
      | some .eq => "="

    prettyTable : Array (Array String) → String := fun xss => Id.run $ do
      let mut colWidths := xss[0]!.map (fun _ => 0)
      for i in [:xss.size] do
        for j in [:xss[i]!.size] do
          if xss[i]![j]!.length > colWidths[j]! then
            colWidths := colWidths.set! j xss[i]![j]!.length
      let mut str := ""
      for i in [:xss.size] do
        for j in [:xss[i]!.size] do
          let s := xss[i]![j]!
          for k in [:colWidths[j]! - s.length] do
            str := str ++ " "
          str := str ++ s
          if j + 1 < xss[i]!.size then
            str := str ++ " "
        if i + 1 < xss.size then
          str := str ++ "\n"
      return str


partial def LexMatrix.solve (m : LexMatrix) (acc : Array Nat) : Option (Array Nat) := Id.run do
  if m.rows == 0 then return .some acc
  -- Find the first column that has at least one < and otherwise only = or <=
  for i in [:m.cols] do
    let mut has_lt := false
    let mut all_le := true
    for j in [:m.rows] do
      let entry := m.get i j
      if entry = some .lt then
        has_lt := true
      else
        if entry != some .le && entry != some .eq then
          all_le := false
          break
    if not (has_lt && all_le) then continue
    -- We found a suitable next column
    -- Remove these columns and recurse
    let m' : LexMatrix := m.map fun col => Id.run do
      -- This is very ugly; find better data structure.
      let mut col := col
      for j in (List.range m.rows).reverse do
        if m.get i j = some .lt then col := col.eraseIdx j
      return col
    return m'.solve (acc.push i)
  return .none

def guessLex (preDefs : Array PreDefinition) (wf? : Option TerminationWF) (decrTactic? : Option Syntax) : TermElabM Unit := do
  let (unaryPreDef, fixedPrefixSize) ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedPrefixSize ← getFixedPrefix preDefs
    trace[Elab.definition.wf] "fixed prefix: {fixedPrefixSize}"
    let preDefsDIte ← preDefs.mapM fun preDef => return { preDef with value := (← iteToDIte preDef.value) }
    let unaryPreDefs ← packDomain fixedPrefixSize preDefsDIte
    return (← packMutual fixedPrefixSize preDefs unaryPreDefs, fixedPrefixSize)
  /- let preDefNonRec ← -/
  forallBoundedTelescope unaryPreDef.type fixedPrefixSize fun prefixArgs type => do
    let type ← whnfForall type
    let packedArgType := type.bindingDomain!
    -- Maybe do this before packMutual?
    trace[Elab.definition.wf] "packedArgType is: {packedArgType}"

    -- TODO: mutual
    let varNames ← naryVarNames preDefs[0]!
    trace[Elab.definition.wf] "varNames is: {varNames}"

    let cols : LexMatrix ← (List.range (varNames.size)).toArray.mapM fun i =>
      lexGuessCol preDefs[0]! unaryPreDef fixedPrefixSize packedArgType varNames i
    trace[Elab.definition.wf] "{cols.map (repr ·)}"
    match cols.solve #[] with
    | .some dec =>
      -- logInfo <| m!"{cols.pretty varNames}" ++ Format.line ++ m!"{cols.solve #[]}"
      let varsSyntax := varNames.map mkIdent
      let bodySyntax ← Lean.Elab.Term.Quotation.mkTuple (dec.map (varsSyntax.get! ·))
      -- dbg_trace (varsSyntax,bodySyntax)
      -- we have an order that should work!
      -- let's construct a `TerminationWf`
      let termWF : TerminationWF := .ext #[
        { ref := .missing -- is this the right function
          declName := preDefs[0]!.declName
          vars := varsSyntax
          body := bodySyntax
          implicit := true -- TODO
        }
      ]
      wfRecursion preDefs termWF decrTactic?
    | .none =>
      throwError ("Cannot solve matrix:" ++ Format.line ++ cols.pretty varNames)


-- set_option trace.Elab.definition.wf true

def ping (n : Nat) := pong n
   where pong : Nat → Nat
  | 0 => 0
  | .succ n => ping n
derecursify_with (guessLex · none none)


def foo2 (n : Nat) (m : Nat) : Nat := match n, m with
  | .succ n, 1 => foo2 n 1
  | .succ n, 2 => foo2 (.succ n) 1
  | n,       3 => foo2 (.succ n) 2
  | .succ n, 4 => foo2 (if n > 10 then n else .succ n) 3
  | n,       5 => foo2 (n - 1) 4
  | n, .succ m => foo2 n m
  | _, _ => 0
derecursify_with (guessLex · none none)

def ackermann (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann n 1
  | .succ n, .succ m => ackermann n (ackermann (n + 1) m)
derecursify_with (guessLex · none none)

def ackermann2 (n m : Nat) := match n, m with
  | m, 0 => m + 1
  | 0, .succ n => ackermann2 1 n
  | .succ m, .succ n => ackermann2 (ackermann2 m (n + 1)) n
derecursify_with (guessLex · none none)



def blowup : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | 0, 0, 0, 0, 0, 0, 0, 0 => 0
  | 0, 0, 0, 0, 0, 0, 0, .succ i => .succ (blowup i i i i i i i i)
  | 0, 0, 0, 0, 0, 0, .succ h, i => .succ (blowup h h h h h h h i)
  | 0, 0, 0, 0, 0, .succ g, h, i => .succ (blowup g g g g g g h i)
  | 0, 0, 0, 0, .succ f, g, h, i => .succ (blowup f f f f f g h i)
  | 0, 0, 0, .succ e, f, g, h, i => .succ (blowup e e e e f g h i)
  | 0, 0, .succ d, e, f, g, h, i => .succ (blowup d d d e f g h i)
  | 0, .succ c, d, e, f, g, h, i => .succ (blowup c c d e f g h i)
  | .succ b, c, d, e, f, g, h, i => .succ (blowup b c d e f g h i)
-- derecursify_with (guessLex · none none)
derecursify_with fun _ _ _ => return
