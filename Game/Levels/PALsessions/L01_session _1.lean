import GameServer.Commands

World "PAL sessions"
Level 1
Title "Session 1"

Introduction "
Let f: ℤ → ℤ be the function f(x):= 2x

We'll show that the function f is injective.
"

/-- `linarith` is used to prove many linear equations and inequalities
-/

TacticDoc «linarith»

NewTactic «linarith»


/-- Let f: ℤ → ℤ be the function f(x):=2x. Prove that f is injective. -/
def f (x : ℕ) : ℕ := 2 * x
Statement injective f : by
intros x₁ x₂ h
have h_eq : 2 * x₁ = 2 * x₂ := h
linarith
Conclusion "
Well done!
"
