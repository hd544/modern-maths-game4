import GameServer.Commands
import Game.Metadata

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Linarith


World "PALsessions"
Level 1
Title "Session 1"

Introduction "
Let f: ℕ → ℕ be the function f(x):= 2x


We'll show that the function f is injective.
"


/-- `intros`
-/

TacticDoc intros


/-- `have`
-/

TacticDoc «have»


/-- `show`
-/

TacticDoc «show»


/-- `sorry`
 -/

TacticDoc «sorry»


/-- `linarith` is used to prove many linear equations and inequalities
-/

TacticDoc linarith


NewTactic intros «have» «show» linarith «sorry»

/-- `f_injective`
-/

TheoremDoc f_injective as "f_injective" in "PALsessions"

open Function
def f (x : Nat) : Nat := (2 : Nat) * x

/-- Let f: ℕ → ℕ be the function f(x):=2x. Prove that f is injective.
-/
Statement f_injective : Injective f := by
  Hint (hidden := true) " .... in the text box and press \"Execute\"."
  intros x₁ x₂ h
  Hint (hidden := true) " .... in the text box and press \"Execute\"."
  have h₁ : 2 * x₁ = 2 * x₂ := h
  Hint (hidden := true) " .... in the text box and press \"Execute\"."
  show x₁ = x₂
  Hint (hidden := true) " .... in the text box and press \"Execute\"."
  linarith

Conclusion "
Well done!
"
