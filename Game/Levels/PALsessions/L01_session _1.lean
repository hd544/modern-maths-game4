import GameServer.Commands

World "PAL sessions"
Level 1
Title "Session 1"

Introduction "
Let f: ℤ → ℤ be the function f(x):= 2x

We'll show that the function f is injective.
"

/-- `assume` is used to show what we assume to be true
-/
TacticDoc «assume»

NewTactic «assume»

/-- `given` is used to show hypotheses that we already know, rewritten in a different way
-/
TacticDoc «given»

NewTactic «given»


/-- `linarith` is used to prove many linear equations and inequalities
-/
TacticDoc «linarith»

NewTactic «linarith»

/-- `show` is used to state what is being proved
-/
TacticDoc «show»

NewTactic «show»


namespace MyGroup

open Group

variable {G : Type} [Group G]


/-- Let f: ℤ → ℤ be the function f(x):=2x. Prove that f is injective. -/
Statement eq_one_of_self_mul_eq (b : G) (h : ∀ (a : G), b * a = a) : b = 1 := by

Conclusion "
Well done!
"

end MyGroup
