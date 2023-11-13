import Lean.Elab.PreDefinition.Main

set_option autoImplicit false

open Lean Elab

def foo (n : Nat) : Nat := match n with
  | .zero => .zero
  | .succ n => foo n
derecursify_with fun defs _ _ => Structural.structuralRecursion defs

def derec (preDefs : Array PreDefinition) : TermElabM Unit := do
  logInfo m!"{preDefs.map (·.declName)}"
  return

def foo2 (n : Nat) : Nat := match n with
  | .zero => .zero
  | .succ n => foo2 n
derecursify_with fun defs _ _ => derec defs
