import Lean.Elab.PreDefinition.Main
import Lean.Elab.Quotation

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab WF
namespace Derec


open Meta

private def applyDefaultDecrTactic (mvarId : MVarId) : TermElabM Unit := do
  let remainingGoals ← Tactic.run mvarId do
    Tactic.evalTactic (← `(tactic| decreasing_tactic))
  remainingGoals.forM fun mvarId => Term.reportUnsolvedGoals [mvarId]

private def mkDecreasingProof (decreasingProp : Expr) (decrTactic? : Option Syntax) : TermElabM Expr := do
  mkFreshExprSyntheticOpaqueMVar decreasingProp
  -- let mvar ← mkFreshExprSyntheticOpaqueMVar decreasingProp
  -- let mvarId := mvar.mvarId!
  -- let mvarId ← mvarId.cleanup
  -- match decrTactic? with
  -- | none => applyDefaultDecrTactic mvarId
  -- | some decrTactic =>
  --   -- make info from `runTactic` available
  --   pushInfoTree (.hole mvarId)
  --   Term.runTactic mvarId decrTactic
  -- instantiateMVars mvar

private partial def replaceRecApps (recFnName : Name) (fixedPrefixSize : Nat) (decrTactic? : Option Syntax) (F : Expr) (e : Expr) : TermElabM Expr := do
  trace[Elab.definition.wf] "replaceRecApps:{indentExpr e}"
  trace[Elab.definition.wf] "{F} : {← inferType F}"
  loop F e |>.run' {}
where
  processRec (F : Expr) (e : Expr) : StateRefT (HasConstCache recFnName) TermElabM Expr := do
    if e.getAppNumArgs < fixedPrefixSize + 1 then
      loop F (← etaExpand e)
    else
      let args := e.getAppArgs
      let r := mkApp F (← loop F args[fixedPrefixSize]!)
      let decreasingProp := (← whnf (← inferType r)).bindingDomain!
      let r := mkApp r (← mkDecreasingProof decreasingProp decrTactic?)
      return mkAppN r (← args[fixedPrefixSize+1:].toArray.mapM (loop F))

  processApp (F : Expr) (e : Expr) : StateRefT (HasConstCache recFnName) TermElabM Expr := do
    if e.isAppOf recFnName then
      processRec F e
    else
      e.withApp fun f args => return mkAppN (← loop F f) (← args.mapM (loop F))

  containsRecFn (e : Expr) : StateRefT (HasConstCache recFnName) TermElabM Bool := do
    modifyGet (·.contains e)

  loop (F : Expr) (e : Expr) : StateRefT (HasConstCache recFnName) TermElabM Expr := do
    if !(← containsRecFn e) then
      return e
    match e with
    | Expr.lam n d b c =>
      withLocalDecl n c (← loop F d) fun x => do
        mkLambdaFVars #[x] (← loop F (b.instantiate1 x))
    | Expr.forallE n d b c =>
      withLocalDecl n c (← loop F d) fun x => do
        mkForallFVars #[x] (← loop F (b.instantiate1 x))
    | Expr.letE n type val body _ =>
      withLetDecl n (← loop F type) (← loop F val) fun x => do
        mkLetFVars #[x] (← loop F (body.instantiate1 x)) (usedLetOnly := false)
    | Expr.mdata d b =>
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop F b
      else
        return mkMData d (← loop F b)
    | Expr.proj n i e => return mkProj n i (← loop F e)
    | Expr.const .. => if e.isConstOf recFnName then processRec F e else return e
    | Expr.app .. =>
      match (← matchMatcherApp? e) with
      | some matcherApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp F e
        else if let some matcherApp ← matcherApp.addArg? F then
          if !(← Structural.refinedArgType matcherApp F) then
            processApp F e
          else
            let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
              lambdaTelescope alt fun xs altBody => do
                unless xs.size >= numParams do
                  throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
                let FAlt := xs[numParams - 1]!
                mkLambdaFVars xs (← loop FAlt altBody)
            return { matcherApp with alts := altsNew, discrs := (← matcherApp.discrs.mapM (loop F)) }.toExpr
        else
          processApp F e
      | none =>
      match (← toCasesOnApp? e) with
      | some casesOnApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp F e
        else if let some casesOnApp ← casesOnApp.addArg? F (checkIfRefined := true) then
          let altsNew ← (Array.zip casesOnApp.alts casesOnApp.altNumParams).mapM fun (alt, numParams) =>
            lambdaTelescope alt fun xs altBody => do
              unless xs.size >= numParams do
                throwError "unexpected `casesOn` application alternative{indentExpr alt}\nat application{indentExpr e}"
              let FAlt := xs[numParams]!
              mkLambdaFVars xs (← loop FAlt altBody)
          return { casesOnApp with
                   alts      := altsNew
                   remaining := (← casesOnApp.remaining.mapM (loop F)) }.toExpr
        else
          processApp F e
      | none => processApp F e
    | e => ensureNoRecFn recFnName e

/-- Refine `F` over `PSum.casesOn` -/
private partial def processSumCasesOn (x F val : Expr) (k : (x : Expr) → (F : Expr) → (val : Expr) → TermElabM Expr) : TermElabM Expr := do
  if x.isFVar && val.isAppOfArity ``PSum.casesOn 6 && val.getArg! 3 == x && (val.getArg! 4).isLambda && (val.getArg! 5).isLambda then
    let args := val.getAppArgs
    let α := args[0]!
    let β := args[1]!
    let FDecl ← F.fvarId!.getDecl
    let (motiveNew, u) ← lambdaTelescope args[2]! fun xs type => do
      let type ← mkArrow (FDecl.type.replaceFVar x xs[0]!) type
      return (← mkLambdaFVars xs type, ← getLevel type)
    let mkMinorNew (ctorName : Name) (minor : Expr) : TermElabM Expr :=
      lambdaTelescope minor fun xs body => do
        let xNew := xs[0]!
        let valNew ← mkLambdaFVars xs[1:] body
        let FTypeNew := FDecl.type.replaceFVar x (← mkAppOptM ctorName #[α, β, xNew])
        withLocalDeclD FDecl.userName FTypeNew fun FNew => do
          mkLambdaFVars #[xNew, FNew] (← processSumCasesOn xNew FNew valNew k)
    let minorLeft ← mkMinorNew ``PSum.inl args[4]!
    let minorRight ← mkMinorNew ``PSum.inr args[5]!
    let result := mkAppN (mkConst ``PSum.casesOn [u, (← getLevel α), (← getLevel β)]) #[α, β, motiveNew, x, minorLeft, minorRight, F]
    return result
  else
    k x F val

/-- Refine `F` over `PSigma.casesOn` -/
private partial def processPSigmaCasesOn (x F val : Expr) (k : (F : Expr) → (val : Expr) → TermElabM Expr) : TermElabM Expr := do
  if x.isFVar && val.isAppOfArity ``PSigma.casesOn 5 && val.getArg! 3 == x && (val.getArg! 4).isLambda && (val.getArg! 4).bindingBody!.isLambda then
    let args := val.getAppArgs
    let [_, u, v] := val.getAppFn.constLevels! | unreachable!
    let α := args[0]!
    let β := args[1]!
    let FDecl ← F.fvarId!.getDecl
    let (motiveNew, w) ← lambdaTelescope args[2]! fun xs type => do
      let type ← mkArrow (FDecl.type.replaceFVar x xs[0]!) type
      return (← mkLambdaFVars xs type, ← getLevel type)
    let minor ← lambdaTelescope args[4]! fun xs body => do
        let a := xs[0]!
        let xNew := xs[1]!
        let valNew ← mkLambdaFVars xs[2:] body
        let FTypeNew := FDecl.type.replaceFVar x (← mkAppOptM `PSigma.mk #[α, β, a, xNew])
        withLocalDeclD FDecl.userName FTypeNew fun FNew => do
          mkLambdaFVars #[a, xNew, FNew] (← processPSigmaCasesOn xNew FNew valNew k)
    let result := mkAppN (mkConst ``PSigma.casesOn [w, u, v]) #[α, β, motiveNew, x, minor, F]
    return result
  else
    k F val

def mkFix (preDef : PreDefinition) (prefixArgs : Array Expr) (wfRel : Expr) (decrTactic? : Option Syntax) : TermElabM Expr := do
  let type ← instantiateForall preDef.type prefixArgs
  let (wfFix, varName) ← forallBoundedTelescope type (some 1) fun x type => do
    let x := x[0]!
    let α ← inferType x
    let u ← getLevel α
    let v ← getLevel type
    let motive ← mkLambdaFVars #[x] type
    let rel := mkProj ``WellFoundedRelation 0 wfRel
    let wf  := mkProj ``WellFoundedRelation 1 wfRel
    let varName ← x.fvarId!.getUserName -- See comment below.
    return (mkApp4 (mkConst ``WellFounded.fix [u, v]) α motive rel wf, varName)
  forallBoundedTelescope (← whnf (← inferType wfFix)).bindingDomain! (some 2) fun xs _ => do
    let x   := xs[0]!
    -- Remark: we rename `x` here to make sure we preserve the variable name in the
    -- decreasing goals when the function has only one non fixed argument.
    -- This renaming is irrelevant if the function has multiple non fixed arguments. See `process*` functions above.
    let lctx := (← getLCtx).setUserName x.fvarId! varName
    withTheReader Meta.Context (fun ctx => { ctx with lctx }) do
      let F   := xs[1]!
      let val := preDef.value.beta (prefixArgs.push x)
      let val ← processSumCasesOn x F val fun x F val => do
        processPSigmaCasesOn x F val (replaceRecApps preDef.declName prefixArgs.size decrTactic?)
      dbg_trace "{(← getMVars val).size}"
      let val ← mkLambdaFVars #[x, F] val
      dbg_trace "{(← getMVars val).size}"
      let val := mkApp wfFix val
      dbg_trace "{(← getMVars val).size}"
      let val ← mkLambdaFVars prefixArgs val
      dbg_trace "{(← getMVars val).size}"
      return val


-- Copied from src/lean/Lean/Elab/PreDefinition/WF/Main.lean

private partial def addNonRecPreDefs (preDefs : Array PreDefinition) (preDefNonRec : PreDefinition) (fixedPrefixSize : Nat) : TermElabM Unit := do
  let us := preDefNonRec.levelParams.map mkLevelParam
  let all := preDefs.toList.map (·.declName)
  for fidx in [:preDefs.size] do
    let preDef := preDefs[fidx]!
    let value ← lambdaTelescope preDef.value fun xs _ => do
      let packedArgs : Array Expr := xs[fixedPrefixSize:]
      let mkProd (type : Expr) : MetaM Expr := do
        mkUnaryArg type packedArgs
      let rec mkSum (i : Nat) (type : Expr) : MetaM Expr := do
        if i == preDefs.size - 1 then
          mkProd type
        else
          (← whnfD type).withApp fun f args => do
            assert! args.size == 2
            if i == fidx then
              return mkApp3 (mkConst ``PSum.inl f.constLevels!) args[0]! args[1]! (← mkProd args[0]!)
            else
              let r ← mkSum (i+1) args[1]!
              return mkApp3 (mkConst ``PSum.inr f.constLevels!) args[0]! args[1]! r
      let Expr.forallE _ domain _ _ := (← instantiateForall preDefNonRec.type xs[:fixedPrefixSize]) | unreachable!
      let arg ← mkSum 0 domain
      mkLambdaFVars xs (mkApp (mkAppN (mkConst preDefNonRec.declName us) xs[:fixedPrefixSize]) arg)
    trace[Elab.definition.wf] "{preDef.declName} := {value}"
    addNonRec { preDef with value } (applyAttrAfterCompilation := false) (all := all)


private def isOnlyOneUnaryDef (preDefs : Array PreDefinition) (fixedPrefixSize : Nat) : MetaM Bool := do
  if preDefs.size == 1 then
    lambdaTelescope preDefs[0]!.value fun xs _ => return xs.size == fixedPrefixSize + 1
  else
    return false


def wfRecursionSingleGoal (preDefs : Array PreDefinition) (wf? : Option TerminationWF) (decrTactic? : Option Syntax) : TermElabM Unit := do
  let (unaryPreDef, fixedPrefixSize) ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedPrefixSize ← getFixedPrefix preDefs
    trace[Elab.definition.wf] "fixed prefix: {fixedPrefixSize}"
    let preDefsDIte ← preDefs.mapM fun preDef => return { preDef with value := (← iteToDIte preDef.value) }
    let unaryPreDefs ← packDomain fixedPrefixSize preDefsDIte
    return (← packMutual fixedPrefixSize preDefs unaryPreDefs, fixedPrefixSize)
  let preDefNonRec ← forallBoundedTelescope unaryPreDef.type fixedPrefixSize fun prefixArgs type => do
    let type ← whnfForall type
    let packedArgType := type.bindingDomain!
    elabWFRel preDefs unaryPreDef.declName fixedPrefixSize packedArgType wf? fun wfRel => do
      trace[Elab.definition.wf] "wfRel: {wfRel}"
      let (value, envNew) ← withoutModifyingEnv' do
        addAsAxiom unaryPreDef
        let value ← mkFix unaryPreDef prefixArgs wfRel decrTactic?
        eraseRecAppSyntaxExpr value
      /- `mkFix` invokes `decreasing_tactic` which may add auxiliary theorems to the environment. -/
      let value ← unfoldDeclsFrom envNew value
      return { unaryPreDef with value }

  let goals ← getMVars preDefNonRec.value
  let goals ← goals.mapM (·.cleanup)
  let remainingGoals ← Tactic.run goals[0]! do
    Tactic.setGoals goals.toList
    match decrTactic? with
    | none => Tactic.evalTactic (← `(tactic| decreasing_tactic))
    | some decrTactic =>
      -- make info from `runTactic` available
      Tactic.evalTactic decrTactic[1]
  Term.reportUnsolvedGoals remainingGoals
  -- instantiateMVars mvar

  trace[Elab.definition.wf] ">> {preDefNonRec.declName} :=\n{preDefNonRec.value}"
  let preDefs ← preDefs.mapM fun d => eraseRecAppSyntax d

  if (← isOnlyOneUnaryDef preDefs fixedPrefixSize) then
    addNonRec preDefNonRec (applyAttrAfterCompilation := false)
  else
    withEnableInfoTree false do
      addNonRec preDefNonRec (applyAttrAfterCompilation := false)
    addNonRecPreDefs preDefs preDefNonRec fixedPrefixSize
  registerEqnsInfo preDefs preDefNonRec.declName fixedPrefixSize
  for preDef in preDefs do
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation
  addAndCompilePartialRec preDefs

def foo (n : Nat) : Nat :=
    foo (n - 1) + foo n + foo (n + 1)
derecursify_with wfRecursionSingleGoal
termination_by foo n => n
decreasing_by
  all_goals simp_wf




#exit



def foo2 (n : Nat) (m : Nat) : Nat := match n, m with
  | .succ n, 1 => foo2 n 1
  | .succ n, 2 => foo2 (.succ n) 1
  | n,       3 => foo2 (.succ n) 2
  | .succ n, 4 => foo2 (if n > 10 then n else .succ n) 3
  | n,       5 => foo2 (n - 1) 4
  | n, .succ m => foo2 n m
  | _, _ => 0
derecursify_with wfRecursionSingleGoal
termination_by foo2 n m => (m, n)
decreasing_by
  done
