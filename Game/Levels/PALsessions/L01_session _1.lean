import GameServer.Commands
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.linarith

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

/-- Shows ∀ x₁ x₂ : ℤ, f(x₁) = f(x₂) → x₁ = x₂ -/
TheoremDoc f_injective as "injective f" in "PAL sessions"

open Function

/-- Let f: ℕ → ℕ be the function f(x):=2x. Prove that f is injective. -/
def f (x : Nat) : Nat := (2 : Nat) * x
Statement f_injective : Injective f := by
  intros x₁ x₂ h
  have h_eq : 2 * x₁ = 2 * x₂ := h
  show x₁ = x₂
  rw [←Nat.mul_right_inj]
  · exact h_eq
  · linarith

Conclusion "
Well done!
"
