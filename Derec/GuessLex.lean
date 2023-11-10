import Lean.Elab.PreDefinition.Main




set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab WF

namespace Derec

def naryVarNames (preDef : PreDefinition) : TermElabM (Array Name):= do
  -- TODO: Pretty names when no user name is available?
  lambdaTelescope preDef.value fun xs _ => do
    xs.mapM fun x => x.fvarId!.getUserName

@[reducible]
def M (recFnName : Name) (α β : Type) : Type :=
  StateRefT (Array α) (StateRefT (HasConstCache recFnName) TermElabM) β

/-- Given
  - matcherApp `match_i As (fun xs => motive[xs]) discrs (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining`, and
  - expression `e : B[discrs]`,
  returns the expressions `B[C_1[ys_1]])  ... B[C_n[ys_n]]`.
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
  (which `ys_i` as loose bound variable, ready to be `.instantiate`d)
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
      return

  processApp (scrut : Expr) (e : Expr) : M recFnName α Unit := do
    if e.isAppOf recFnName then
      processRec scrut e
    else
      e.withApp fun _f args => args.forM (loop scrut)

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
    | Expr.const .. => if e.isConstOf recFnName then processRec scrut e else return
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
      return

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

/-- A `RecCallContext` focuses on a single recursive call in a unary predefinition,
and runs the given action in the context of that call. The arguments are
the function's unary argument, refined by case analysis, and the recursive call'
unary argument.
-/
structure RecCallContext where
  param : Expr
  arg : Expr
  savedState : Term.SavedState
  savedMetaContext : Meta.Context
  savedTermContext : Term.Context

def RecCallContext.create (param arg : Expr) : TermElabM RecCallContext := do
  let savedState ← saveState
  let savedMetaContext ← readThe Meta.Context
  let savedTermContext ← readThe Term.Context
  return { param, arg, savedState, savedMetaContext, savedTermContext }


def RecCallContext.run {α} (rcc : RecCallContext) (k : Expr → Expr → TermElabM α) :
    TermElabM α := withoutModifyingState $ do
  restoreState rcc.savedState
  withTheReader Meta.Context (fun _ => rcc.savedMetaContext) do
  withTheReader Term.Context (fun _ => rcc.savedTermContext) do
  k rcc.param rcc.arg

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


inductive GuessLexRel | lt | le | gt
deriving Repr

def GuessLexRel.toNatRel : GuessLexRel → Expr
  | lt => mkAppN (mkConst ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat]
  | le => mkAppN (mkConst ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``instLENat]
  | gt => mkAppN (mkConst ``GT.gt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat]

def lexGuessCol (preDef : PreDefinition) (unaryPreDef : PreDefinition) (fixedPrefixSize : Nat)
    (packedArgType : Expr)
    (varNames : Array Name) (varIdx : Nat) : TermElabM (Array (Option GuessLexRel)):= do
  let varNames ← lambdaTelescope preDef.value fun xs _ => do
    xs.mapM fun x => x.fvarId!.getUserName

  let recCalls ← collectRecCalls unaryPreDef fixedPrefixSize
  recCalls.mapM fun rcc => rcc.run fun packed_param packed_arg => do
      trace[Elab.definition.wf] "rcc.run: {packed_param} {packed_arg}"
      withLetDecl (← mkFreshUserName `packed_param) packedArgType packed_param fun x => do
      withLetDecl (← mkFreshUserName `packed_arg) packedArgType packed_arg fun arg => do
        for rel in [GuessLexRel.lt, .le, .gt] do
          let goalMVar ← mkFreshExprSyntheticOpaqueMVar (.sort levelZero)
          let goalMVarId := goalMVar.mvarId!
          let [packedArgMVarId, packedParamMVarId] ← goalMVarId.apply rel.toNatRel | unreachable!

          withUnary preDef fixedPrefixSize packedArgMVarId arg.fvarId! fun argMVarId fvarIds =>
            argMVarId.assign (mkFVar fvarIds[varIdx]!)

          withUnary preDef fixedPrefixSize packedParamMVarId x.fvarId! fun paramMVarId fvarIds =>
            paramMVarId.assign (mkFVar fvarIds[varIdx]!)
          let goalExpr ← instantiateMVars goalMVar

          trace[Elab.definition.wf] "Goal (uncecked): {goalExpr}"
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

def prettyLexMatrix : Array Name → Array (Array (Option GuessLexRel)) → Format := fun names cols =>
  if cols.isEmpty then "(no columns)" else
    let header := #["Recursions:"].append (names.map (·.toString))
    let rows := (List.range (cols[0]!.size)).toArray.map fun i =>
      #[s!"Call {i+1}"].append (cols.map (fun col => prettyGuessLexRel col[i]!))
    let table := #[header].append rows
    prettyTable table
  where
    prettyGuessLexRel : Option GuessLexRel → String
      | none => "?"
      | some .lt => "<"
      | some .le => "≤"
      | some .gt => ">"

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
    let varNames ← naryVarNames preDefs[0]!
    trace[Elab.definition.wf] "varNames is: {varNames}"
    let cols ← (List.range (varNames.size)).toArray.mapM fun i =>
      lexGuessCol preDefs[0]! unaryPreDef fixedPrefixSize packedArgType varNames i
    trace[Elab.definition.wf] "cols is: {cols.map (repr ·)}"
    logInfo (prettyLexMatrix varNames cols)


set_option trace.Elab.definition.wf true
set_option pp.inaccessibleNames true
set_option pp.auxDecls true

def foo2 (n : Nat) (m : Nat) : Nat := match n, m with
  | .succ n, 0 => foo2 n 0
  | .succ n, 1 => foo2 (.succ n) 1
  | n, 2       => foo2 (.succ n) 2
  | .succ n, m => foo2 m m
  | n, .succ m => foo2 n m
  | _, _ => 0
derecursify_with (guessLex · none none)
