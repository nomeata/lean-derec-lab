import Lean.Util.HasConstCache
import Lean.Meta.CasesOn
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Cleanup
import Lean.Meta.Tactic.Refl
import Lean.Elab.Quotation
import Lean.Elab.RecAppSyntax
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.WF.TerminationHint

import Lean.Elab.PreDefinition.Main

set_option autoImplicit false

open Lean Meta Elab WF

namespace Lean.Elab.WF


/-- Combine different function domains `ds` using `PSum`s -/
private def mkNewDomain (ds : Array Expr) : MetaM Expr := do
  let mut r := ds.back
  for d in ds.pop.reverse do
    r ← mkAppM ``PSum #[d, r]
  return r

private def getCodomainLevel (preDefType : Expr) : MetaM Level :=
  forallBoundedTelescope preDefType (some 1) fun _ body => getLevel body

/--
  Return the universe level for the codomain of the given definitions.
  This method produces an error if the codomains are in different universe levels.
-/
private def getCodomainsLevel (preDefsOriginal : Array PreDefinition) (preDefTypes : Array Expr) : MetaM Level := do
  let r ← getCodomainLevel preDefTypes[0]!
  for i in [1:preDefTypes.size] do
    let preDef := preDefTypes[i]!
    unless (← isLevelDefEq r (← getCodomainLevel preDef)) do
      let arity₀ ← lambdaTelescope preDefsOriginal[0]!.value fun xs _ => return xs.size
      let arityᵢ ← lambdaTelescope preDefsOriginal[i]!.value fun xs _ => return xs.size
      forallBoundedTelescope preDefsOriginal[0]!.type arity₀ fun _ type₀ =>
      forallBoundedTelescope preDefsOriginal[i]!.type arityᵢ fun _ typeᵢ =>
        withOptions (fun o => pp.sanitizeNames.set o false) do
          throwError "invalid mutual definition, result types must be in the same universe level, resulting type for `{preDefsOriginal[0]!.declName}` is{indentExpr type₀} : {← inferType type₀}\nand for `{preDefsOriginal[i]!.declName}` is{indentExpr typeᵢ} : {← inferType typeᵢ}"
  return r

/--
  Create the codomain for the new function that "combines" different `preDef` types
  See: `packMutual`
-/
private partial def mkNewCoDomain (preDefsOriginal : Array PreDefinition) (preDefTypes : Array Expr) (x : Expr) : MetaM Expr := do
  let u ← getCodomainsLevel preDefsOriginal preDefTypes
  let rec go (x : Expr) (i : Nat) : MetaM Expr := do
    if i < preDefTypes.size - 1 then
      let xType ← whnfD (← inferType x)
      assert! xType.isAppOfArity ``PSum 2
      let xTypeArgs := xType.getAppArgs
      let casesOn := mkConst (mkCasesOnName ``PSum) (mkLevelSucc u :: xType.getAppFn.constLevels!)
      let casesOn := mkAppN casesOn xTypeArgs -- parameters
      let casesOn := mkApp casesOn (← mkLambdaFVars #[x] (mkSort u)) -- motive
      let casesOn := mkApp casesOn x -- major
      let minor1 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[0]! fun x =>
        mkLambdaFVars #[x] (preDefTypes[i]!.bindingBody!.instantiate1 x)
      let minor2 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[1]! fun x => do
        mkLambdaFVars #[x] (← go x (i+1))
      return mkApp2 casesOn minor1 minor2
    else
      return preDefTypes[i]!.bindingBody!.instantiate1 x
  go x 0

private partial def post (fixedPrefix : Nat) (preDefs : Array PreDefinition) (domain : Expr) (newFn : Name) (e : Expr) : MetaM TransformStep := do
  if e.getAppNumArgs < fixedPrefix + 1 then
    return TransformStep.done e
  let f := e.getAppFn
  if !f.isConst then
    return TransformStep.done e
  let declName := f.constName!
  let us       := f.constLevels!
  if let some fidx := preDefs.findIdx? (·.declName == declName) then
    let args := e.getAppArgs
    let fixedArgs := args[:fixedPrefix]
    let arg  := args[fixedPrefix]!
    let remaining := args[fixedPrefix+1:]
    let rec mkNewArg (i : Nat) (type : Expr) : MetaM Expr := do
      if i == preDefs.size - 1 then
        return arg
      else
        (← whnfD type).withApp fun f args => do
          assert! args.size == 2
          if i == fidx then
            return mkApp3 (mkConst ``PSum.inl f.constLevels!) args[0]! args[1]! arg
          else
            let r ← mkNewArg (i+1) args[1]!
            return mkApp3 (mkConst ``PSum.inr f.constLevels!) args[0]! args[1]! r
    return TransformStep.done <|
      mkAppN (mkApp (mkAppN (mkConst newFn us) fixedArgs) (← mkNewArg 0 domain)) remaining
  return TransformStep.done e

private partial def packValues (x : Expr) (codomain : Expr) (preDefValues : Array Expr) : MetaM Expr := do
  let varNames := preDefValues.map fun val =>
    assert! val.isLambda
    val.bindingName!
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (x : FVarId) (i : Nat) : MetaM Unit := do
    if i < preDefValues.size - 1 then
      /-
        Names for the `cases` tactics. The names are important to preserve the user provided names (unary functions).
      -/
      let givenNames : Array AltVarNames :=
         if i == preDefValues.size - 2 then
           #[{ varNames := [varNames[i]!] }, { varNames := [varNames[i+1]!] }]
         else
           #[{ varNames := [varNames[i]!] }]
       let #[s₁, s₂] ← mvarId.cases x (givenNames := givenNames) | unreachable!
      s₁.mvarId.assign (mkApp preDefValues[i]! s₁.fields[0]!).headBeta
      go s₂.mvarId s₂.fields[0]!.fvarId! (i+1)
    else
      mvarId.assign (mkApp preDefValues[i]! (mkFVar x)).headBeta
  go mvar.mvarId! x.fvarId! 0
  instantiateMVars mvar


def packMutual' (fixedPrefix : Nat) (preDefsOriginal : Array PreDefinition) (preDefs : Array PreDefinition) : MetaM PreDefinition := do
  if preDefs.size == 1 then return preDefs[0]!
  withFixedPrefix fixedPrefix preDefs fun ys types vals => do
    let domains := types.map fun type => type.bindingDomain!
    let domain ← mkNewDomain domains
    withLocalDeclD (← mkFreshUserName `_x) domain fun x => do
      let codomain ← mkNewCoDomain preDefsOriginal types x
      let type ← mkForallFVars (ys.push x) codomain
      let value ← packValues x codomain vals
      let newFn := preDefs[0]!.declName ++ `_mutual
      let preDefNew := { preDefs[0]! with declName := newFn, type, value }
      addAsAxiom preDefNew
      let value ← transform value (post := post fixedPrefix preDefs domain newFn)
      let value ← mkLambdaFVars (ys.push x) value
      return { preDefNew with value }
end Lean.Elab.WF

set_option linter.unusedVariables false

def test (preDefs : Array PreDefinition) (wf? : Option TerminationWF)
    (decrTactic? : Option Syntax) : TermElabM Unit := do
  let unaryPreDef ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedPrefixSize ← getFixedPrefix preDefs
    trace[Elab.definition.wf] "fixed prefix: {fixedPrefixSize}"
    let preDefsDIte ← preDefs.mapM fun preDef => return { preDef with value := (← iteToDIte preDef.value) }
    let unaryPreDefs ← packDomain fixedPrefixSize preDefsDIte
    packMutual' fixedPrefixSize preDefs unaryPreDefs
  logWarning m!"{unaryPreDef.value}"


mutual
  inductive A : Type
  | baseA  : A
  | fromB : B → A

  inductive B : Type
  | fromA  : A → B
end

set_option trace.Elab.definition.wf true
mutual
  def foo : B → Prop    -- unknown constant 'bar'
  | .fromA a => bar a 0

  def bar : A → Nat → Prop
  | .baseA   => (fun _ => True)
  | .fromB b => (fun (c : Nat) => ∃ (t : Nat), foo b)
end
derecursify_with test
termination_by
  foo x => sizeOf x
  bar x => sizeOf x

mutual
  inductive Thing : Type
    | Bag : Object → Thing
  inductive Object : Type
    | Bike : Object
    | Box : Thing -> Object
end

mutual
  def sizeOfThing : Thing → Nat
    | .Bag o => 1 + sizeOfObject o
  def sizeOfObject : Object → Nat
    | .Bike => 42
    | .Box t => 1 + sizeOfThing t
end

axiom Nat.add_mod (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n

mutual
theorem aboutThings : ∀ t, sizeOfThing t % 2 = 1
  | .Bag o => by
    unfold sizeOfThing
    rw [Nat.add_mod, aboutObjects /- o-/]
    rfl

theorem aboutObjects : ∀ o, sizeOfObject o % 2 = 0
  | .Bike => rfl
  | .Box t => by
    unfold sizeOfObject
    rw [Nat.add_mod, aboutThings t]
    rfl
end
derecursify_with test
decreasing_by sorry
