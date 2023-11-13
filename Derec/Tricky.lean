import Derec.GuessLex

macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.le_refl)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.succ_lt_succ; decreasing_trivial)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.sub_le)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.div_le_self)

syntax "search_lex " tacticSeq : tactic

macro_rules | `(tactic|search_lex $ts:tacticSeq) => `(tactic| (
    solve
    | apply Prod.Lex.right'
      · $ts
      · search_lex $ts
    | apply Prod.Lex.left
      · $ts
    | $ts
    ))

-- set_option trace.Elab.definition.wf true in
mutual
def prod (x y z : Nat) : Nat :=
  if y % 2 = 0 then eprod x y z else oprod x y z
def oprod (x y z : Nat) := eprod x (y - 1) (z + x)
def eprod (x y z : Nat) := if y = 0 then z else prod (2 * x) (y / 2) z
end
derecursify_with Derec.guessLex
-- termination_by
--   prod x y z => (y, 2)
--   oprod x y z => (y, 1)
--   eprod x y z => (y, 0)
decreasing_by
  simp_wf
  search_lex solve
    | decreasing_trivial
    | apply Nat.bitwise_rec_lemma; assumption
