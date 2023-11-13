import Lean.Elab.PreDefinition.Main
import Lean.Elab.Quotation
import Derec.Options

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab WF


namespace Derec

/--
Given a predefinition, find good variable names for its parameters.
Use user-given parameter names if present; use x1...xn otherwise.
TODO: Prettier code to generate x1...xn
-/
def naryVarNames (preDef : PreDefinition) : TermElabM (Array Name):= do
  lambdaTelescope preDef.value fun xs _ => do
    let mut ns := #[]
    for i in List.range xs.size do
      let n ← xs[i]!.fvarId!.getUserName
      if n.hasMacroScopes then
        ns := ns.push (← mkFreshUserName (.mkSimple ("x" ++ (repr (i+1)).pretty)))
      else
        ns := ns.push n
    return ns

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

/-- Traverse a unary PreDefinition, and returns a `WithRecCall` closure for each recursive
call site.
-/
def collectRecCalls (unaryPreDef : PreDefinition) (fixedPrefixSize : Nat)
    : TermElabM (Array RecCallContext) := withoutModifyingState do
  addAsAxiom unaryPreDef
  lambdaTelescope unaryPreDef.value fun xs body => do
    -- trace[Elab.definition.wf] "collectRecCalls: {xs} {body}"
    -- assert xs.size  == fixedPrefixSize + 1
    let param := xs[fixedPrefixSize]!
    withRecApps unaryPreDef.declName fixedPrefixSize body param fun param args => do
      let arg := args[0]!
      RecCallContext.create param arg

inductive GuessLexRel | lt | eq | le | no_idea
deriving Repr, DecidableEq

def GuessLexRel.toNatRel : GuessLexRel → Expr
  | lt => mkAppN (mkConst ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat]
  | eq => mkAppN (mkConst ``Eq [levelOne]) #[mkConst ``Nat]
  | le => mkAppN (mkConst ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``instLENat]
  | no_idea => unreachable! -- TODO: keep it partial or refactor?

-- For a given recursive call and choice of paramter index,
-- try to prove requality, < or ≤
def evalRecCall (rcc : RecCallContext) (paramIdx argIdx : Nat) :
    TermElabM GuessLexRel := do
  rcc.ctxt.run do
    let param := rcc.params[paramIdx]!
    let arg := rcc.args[argIdx]!
    trace[Elab.definition.wf] "inspectRecCall: {rcc.caller} ({param}) → {rcc.callee} ({arg})"
    for rel in [GuessLexRel.eq, .lt, .le] do
      let goalExpr := mkAppN rel.toNatRel #[rcc.args[argIdx]!, rcc.params[paramIdx]!]
      trace[Elab.definition.wf] "Goal (unchecked): {goalExpr}"
      check goalExpr

      let mvar ← mkFreshExprSyntheticOpaqueMVar goalExpr
      let mvarId := mvar.mvarId!
      let mvarId ← mvarId.cleanup
      -- logInfo m!"Remaining goals: {goalsToMessageData [mvarId]}"
      try
        if rel = .eq then
          MVarId.refl mvarId
        else do
          let remainingGoals ← Tactic.run mvarId do
            Tactic.evalTactic (← `(tactic| decreasing_tactic))
          remainingGoals.forM fun mvarId => Term.reportUnsolvedGoals [mvarId]
          let expr ← instantiateMVars mvar
          -- trace[Elab.definition.wf] "Found {repr rel} proof: {expr}"
        return rel
      catch _e =>
        -- trace[Elab.definition.wf] "Did not find {repr rel} proof of {goalsToMessageData [mvarId]}"
        continue
    return .no_idea

-- Like `evalRecCall`, but cached
def evalRecCallCached (recCalls : Array RecCallContext) :
    TermElabM (Nat → Nat → Nat → TermElabM GuessLexRel) := do
  let cache ← IO.mkRef <| recCalls.map fun rcc =>
      Array.mkArray rcc.params.size (Array.mkArray rcc.args.size Option.none)
  return fun callIdx paramIdx argIdx => do
    let some rcc := recCalls[callIdx]? | unreachable!
    -- Check the cache first
    if let Option.some res := (← cache.get)[callIdx]![paramIdx]![argIdx]! then
      return res
    else
      let res ← evalRecCall rcc paramIdx argIdx
      cache.modify (·.modify callIdx (·.modify paramIdx (·.set! argIdx res)))
      return res

/-- The measures that we order lexicographically can be comparing arguments,
or numbering the functions -/
inductive MutualMeasure where
  | args : Array Nat → MutualMeasure
  --- The given function index is assigned 1, the rest 0
  | func : Nat → MutualMeasure

-- Evaluate a call at a given measure
def inspectCall (recCalls : Array RecCallContext)
    (evalCall : Nat → Nat → Nat → TermElabM GuessLexRel) :
    MutualMeasure → Nat → TermElabM GuessLexRel
  | .args argIdxs, callIdx => do
    let some rcc := recCalls[callIdx]? | unreachable!
    let paramIdx := argIdxs[rcc.caller]!
    let argIdx := argIdxs[rcc.callee]!
    evalCall callIdx paramIdx argIdx
  | .func funIdx, callIdx => do
    let some rcc := recCalls[callIdx]? | unreachable!
    if rcc.caller == rcc.callee then
      return .eq
    else if rcc.caller == funIdx && rcc.callee != funIdx then
      return .lt
    else
      return .no_idea

/--
  Given a predefinition with value `fun (x_₁ ... xₙ) (y_₁ : α₁)... (yₘ : αₘ) => ...`,
  where `n = fixedPrefixSize`, return an array `A` s.t. `i ∈ A` iff `sizeOf yᵢ` reduces to a literal.
  This is the case for types such as `Prop`, `Type u`, etc.
  This arguments should not be considered when guessing a well-founded relation.
  See `generateCombinations?`
-/
def getForbiddenByTrivialSizeOf (fixedPrefixSize : Nat) (preDef : PreDefinition) : MetaM (Array Nat) :=
  lambdaTelescope preDef.value fun xs _ => do
    let mut result := #[]
    for x in xs[fixedPrefixSize:], i in [:xs.size] do
      try
        let sizeOf ← whnfD (← mkAppM ``sizeOf #[x])
        if sizeOf.isLit then
         result := result.push i
      catch _ =>
        result := result.push i
    return result


-- Generate all combination of arguments
def generateCombinations? (forbiddenArgs : Array (Array Nat)) (numArgs : Array Nat)
    (threshold : Nat := 32) : Option (Array (Array Nat)) :=
  go 0 #[] |>.run #[] |>.2
where
  isForbidden (fidx : Nat) (argIdx : Nat) : Bool :=
    if h : fidx < forbiddenArgs.size then
       forbiddenArgs.get ⟨fidx, h⟩ |>.contains argIdx
    else
      false

  go (fidx : Nat) : OptionT (ReaderT (Array Nat) (StateM (Array (Array Nat)))) Unit := do
    if h : fidx < numArgs.size then
      let n := numArgs.get ⟨fidx, h⟩
      for argIdx in [:n] do
        unless isForbidden fidx argIdx do
          withReader (·.push argIdx) (go (fidx + 1))
    else
      modify (·.push (← read))
      if (← get).size > threshold then
        failure
termination_by _ fidx => numArgs.size - fidx

/-

-- NB: An array of columns
def LexMatrix := Array (Array (Option GuessLexRel))

def LexMatrix.rows (m : LexMatrix) : Nat := (m.get! 0).size
def LexMatrix.cols (m : LexMatrix) : Nat := m.size
def LexMatrix.get (m : LexMatrix) (i : Nat) (j : Nat) := (m.get! i).get! j

def LexMatrix.pretty : LexMatrix → Array Name → Format := fun m names =>
  if m.isEmpty then "(no columns)" else
    let header := #["Recursions:"].append (names.map (·.eraseMacroScopes.toString))
    let rows := (List.range m.rows).toArray.map fun i =>
      #[s!"Call {i+1}"].append (m.map (fun col => prettyGuessLexRel col[i]!))
    let table := #[header].append rows
    prettyTable table
  where
    prettyGuessLexRel : GuessLexRel → String
      | .no_idea => "?"
      | .lt => "<"
      | .le => "≤"
      | .gt => ">"
      | .eq => "="

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
-/

/-- The core logic of guessing the lexicographic order
For each call and measure, the `inspect` function indicates whether that measure is
decreasing, equal, less-or-equal or unknown.
It finds a sequence of measures that is lexicographically decreasing.

It is monadic only so that `inspect` can be implemented lazily, otherwise it is
a pure function.
-/
partial def solve {m} {α} [Monad m] (measures : Array α)
  (calls : Nat) (inspect : α → Nat → m GuessLexRel) : m (Option (Array α)) := do
  go measures (Array.mkArray calls false) #[]
  where
  go (measures : Array α) (done : Array Bool) (acc : Array α) := do
    if done.all (·) then return .some acc

    -- Find the first measure that has at least one < and otherwise only = or <=
    for h : measureIdx in [:measures.size] do
      let measure := measures[measureIdx]'h.2
      let mut has_lt := false
      let mut all_le := true
      let mut done' := done
      for callIdx in [:calls] do
        if done[callIdx]! then continue
        let entry ← inspect measure callIdx
        if entry = .lt then
          has_lt := true
          done' := done'.set! callIdx true
        else
          if entry != .le && entry != .eq then
            all_le := false
            break
      -- No progress here? Try the next measure
      if not (has_lt && all_le) then continue
      -- We found a suitable measure, remove it from the list (mild optimization)
      let measures' := measures.eraseIdx measureIdx
      return ← go measures' done' (acc.push measure)
    -- None found, we have to give up
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
    -- trace[Elab.definition.wf] "packedArgType is: {packedArgType}"

    -- TODO: mutual
    let varNamess ← preDefs.mapM naryVarNames
    trace[Elab.definition.wf] "varNames is: {varNamess}"

    -- Collect all recursive calls and extract their context
    let recCalls ← collectRecCalls unaryPreDef fixedPrefixSize
    let evalCall ← evalRecCallCached recCalls
    let inspect := inspectCall recCalls evalCall

    let forbiddenArgs ← preDefs.mapM fun preDef =>
      getForbiddenByTrivialSizeOf fixedPrefixSize preDef

    -- Enumerate all meausures.
    -- (With many functions with multiple arguments, this can explode a bit.
    -- We could interleave enumerating measure with early pruning based on the recCalls,
    -- once that becomes a problem. Until then, a use can always use an explicit
    -- `terminating_by` annotatin.)
    let some arg_measures := generateCombinations? forbiddenArgs (varNamess.map (·.size))
      | throwError "Too many combinations"

    let measures : Array MutualMeasure :=
      (List.range varNamess.size).toArray.map .func ++ arg_measures.map .args

    match ← solve measures recCalls.size inspect with
    | .some solution =>
      -- logInfo <| m!"Solution: {solution}"
      let mut termByElements := #[]
      for h : funIdx in [:varNamess.size] do
        let vars := (varNamess[funIdx]'h.2).map mkIdent
        let body := ← Lean.Elab.Term.Quotation.mkTuple (← solution.mapM fun
          | .args varIdxs => return vars.get! (varIdxs[funIdx]!)
          | .func funIdx' => if funIdx' == funIdx then `(1) else `(0)
          )
        let declName := preDefs[funIdx]!.declName
        -- TODO: Can we turn it into user-facing syntax? Maybe for a “try-this” feature?
        trace[Elab.definition.wf] "Using termination {declName}: {vars} => {body}"
        termByElements := termByElements.push
          { ref := .missing -- is this the right function
            declName, vars, body,
            implicit := true -- TODO, what is this?
          }
      let termWF : TerminationWF := .ext termByElements
      wfRecursion preDefs termWF decrTactic?
    | .none =>
      throwError ("Cannot solve")

-- set_option trace.Elab.definition.wf true
set_option trace.Elab.definition.wf.lex_matrix true

def ackermann (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann n 1
  | .succ n, .succ m => ackermann n (ackermann (n + 1) m)
derecursify_with guessLex

def ackermann2 (n m : Nat) := match n, m with
  | m, 0 => m + 1
  | 0, .succ n => ackermann2 1 n
  | .succ m, .succ n => ackermann2 (ackermann2 m (n + 1)) n
derecursify_with guessLex


def foo2 : Nat → Nat → Nat
  | .succ n, 1 => foo2 n 1
  | .succ n, 2 => foo2 (.succ n) 1
  | n,       3 => foo2 (.succ n) 2
  | .succ n, 4 => foo2 (if n > 10 then n else .succ n) 3
  | n,       5 => foo2 (n - 1) 4
  | n, .succ m => foo2 n m
  | _, _ => 0
derecursify_with guessLex

mutual
def even : Nat → Bool
  | 0 => true
  | .succ n => not (odd n)
def odd : Nat → Bool
  | 0 => false
  | .succ n => not (even n)
end
derecursify_with guessLex

def ping (n : Nat) := pong n
   where pong : Nat → Nat
  | 0 => 0
  | .succ n => ping n
derecursify_with guessLex

set_option trace.Elab.definition.wf false in
def hasForbiddenArg (n : Nat) (h : n = n) (m : Nat) : Nat :=
  match n, m with
  | 0, 0 => 0
  | .succ m, n => hasForbiddenArg m rfl n
  | m, .succ n => hasForbiddenArg (.succ m) rfl n
derecursify_with guessLex


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
-- derecursify_with guessLex
derecursify_with fun _ _ _ => return
