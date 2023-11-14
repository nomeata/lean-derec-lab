import Derec.GuessLex


def nonTerminating : Nat → Nat
  | 0 => 0
  | n => nonTerminating (.succ n)
derecursify_with Derec.guessLex
