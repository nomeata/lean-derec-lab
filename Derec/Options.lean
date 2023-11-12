import Lean.Data.Options
open Lean

-- Crashes lean, probably due to the way we evaluate stuff

register_option trace.Elab.definition.wf.lex_matrix : Bool := {
  defValue := false
  descr    := "When tracing is enabled, print the recursion matrix used when guessing lexicographic order"
}
