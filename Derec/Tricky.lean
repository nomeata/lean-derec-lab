macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.le_refl)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.succ_lt_succ; decreasing_trivial)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.sub_le)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.div_le_self)

mutual
def prod (x y z : Nat) : Nat :=
  if y % 2 = 0 then eprod x y z else oprod x y z
def oprod (x y z : Nat) := eprod x (y - 1) (z + x)
def eprod (x y z : Nat) := if y = 0 then z else prod (2 * x) (y / 2) z
end
termination_by
  prod x y z => (y, 2)
  oprod x y z => (y, 1)
  eprod x y z => (y, 0)
decreasing_by
  simp_wf
  solve
    | apply Prod.Lex.right'
      · solve | decreasing_trivial
      · solve | decreasing_trivial
    | apply Prod.Lex.left
      · solve | decreasing_trivial
              | apply Nat.bitwise_rec_lemma; assumption
