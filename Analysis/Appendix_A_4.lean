import Mathlib.Tactic

/-!
# Analysis I, Appendix A.4: Variables and quantifiers

Some examples of how variables and quantifiers are used in Lean

-/

namespace VariableExample1

variable (X:Type) (x y:X)

#check x = x
#check x = y

-- #check x+y = y+x   -- this will not typecheck

end VariableExample1

namespace VariableExample2

variable (x:ℝ)

#check x+3
#check x+3 = 5

example (h: x = 2) : x + 3 = 5 := by linarith

example (h: x ≠ 2) : x + 3 ≠ 5 := by
  contrapose! h
  linarith

example : ¬ ∀ (x:ℝ), x + 3 = 5 := by
  simp
  use 0
  simp

example : ¬ ∀ (x:ℝ), x + 3 ≠ 5 := by
  simp
  use 2
  norm_num

example : ∃ (x:ℝ), x + 3 = 5 := by
  use 2
  norm_num

example : ∀ (x:ℝ), (x+1)^2 = x^2 + 2*x + 1 := by
  intro x
  ring

end VariableExample2

/-- A dummy statement is in place here for this example.-/
example : 0 = 0 := by
  set x := 342
  have : x + 155 = 497 := by
    unfold x
    norm_num
  rfl

example : ¬ ∀ (x:ℝ), x + 155 = 497 := by
  simp
  use 0
  norm_num

example : ¬ ∀ x > (0:ℝ), x^2 > x := by
  simp
  use 0.5
  norm_num

/- The code below will not typecheck.

example : ∀ (x:ℝ), x + 3 = 5 := by
  use 2
  sorry

-/

example : ∀ x, (3 < x ∧ x < 2) → (6 < 2*x ∧ 2*x < 4) := by
  intro x h
  obtain ⟨ h1, h2 ⟩ := h
  -- the previous three lines can be golfed to `intro x ⟨ h1, h2 ⟩`
  constructor
  . linarith
  linarith

example : ∃ (x:ℝ), x^2 + 2*x - 8 = 0 := by
  use 2
  norm_num

example : ¬ ∃ x, (3 < x ∧ x < 2) ∧ (6 < 2*x ∧ 2*x < 4) := by
  simp
  intro x h1 h2 h3
  linarith
