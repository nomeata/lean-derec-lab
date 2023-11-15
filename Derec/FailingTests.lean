import Derec.GuessLex

def nonTerminating : Nat → Nat
  | 0 => 0
  | n => nonTerminating (.succ n)
derecursify_with Lean.Elab.WF.withGuessLex



def FinPlus1 n := Fin (n + 1)

def badCasesOn (n : Nat) : Fin (n + 1) :=
   Nat.casesOn (motive := FinPlus1) n (⟨0,Nat.zero_lt_succ _⟩) (fun n => Fin.succ (badCasesOn n))
derecursify_with Lean.Elab.WF.withGuessLex
-- termination_by badCasesOn n => n


-- In this example we have a casesOn with not enough manifest lambdas.
-- Old termination guesser:
--   failed to prove termination, use `termination_by` to specify a well-founded relation
-- When given termination metric
--   failed to prove termination, possible solutions… (with goal)
def Fin_succ_comp (f : (n : Nat) → Fin (n + 1)) : (n : Nat) → Fin (n + 2) := fun n => Fin.succ (f n)
def badCasesOn2 (n : Nat) : Fin (n + 1) :=
   Nat.casesOn (motive := fun n => Fin (n + 1)) n (⟨0,Nat.zero_lt_succ _⟩)
      (Fin_succ_comp (fun n => badCasesOn2 n))
derecursify_with Lean.Elab.WF.withGuessLex
-- termination_by badCasesOn2 n => n
