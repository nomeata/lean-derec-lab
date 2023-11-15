import Derec.GuessLex


inductive Foo where
  | a | b | c
  | pair: Foo × Foo → Foo

set_option trace.Elab.definition.wf true
def Foo.deq (a b : Foo) : Decidable (a = b) := by
  cases a <;> cases b
  any_goals apply isFalse Foo.noConfusion
  any_goals apply isTrue rfl
  case pair a b =>
    let (a₁, a₂) := a
    let (b₁, b₂) := b
    exact match deq a₁ b₁, deq a₂ b₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁,h₂])
    | isFalse h₁, _ => isFalse (fun h => by cases h; cases (h₁ rfl))
    | _, isFalse h₂ => isFalse (fun h => by cases h; cases (h₂ rfl))
derecursify_with Lean.Elab.WF.withGuessLex
