import Mathlib.Tactic

/-!
# Analysis I, Appendix A.5: Nested quantifiers

Some examples of nested quantifiers in Lean

-/


example : ∀ x > (0:ℝ), ∃ y > 0, y^2 = x := by
  intro x hx
  use √x
  constructor
  . positivity
  convert Real.sq_sqrt _
  positivity

namespace SwanExample

variable (Swans:Type)
variable (isBlack : Swans → Prop)

example : (¬ ∀ s:Swans, isBlack s) = (∃ s:Swans, ¬ isBlack s) := by
  simp

example : (¬ ∃ s:Swans, isBlack s) = (∀ s:Swans, ¬ isBlack s) := by
  simp

end SwanExample

example : (¬ ∀ x, (0 < x ∧ x < Real.pi/2) → Real.cos x ≥ 0) = (∃ x, (0 < x ∧ x < Real.pi/2) ∧ Real.cos x < 0) := by
  simp
  simp_rw [and_assoc]

example : (¬ ∃ x:ℝ, x^2 + x + 1 = 0) = (∀ x:ℝ, x^2 + x + 1 ≠ 0) := by
  simp

theorem square_expand : ∀ (x:ℝ), (x + 1)^2 = x^2 + 2 * x + 1 := by
  intro x
  ring

example : (Real.pi+1)^2 = Real.pi^2 + 2 * Real.pi + 1 := by
  apply square_expand  -- one can also use `exact square_expand _`

example : ∀ (y:ℝ), (Real.cos y + 1)^2 = Real.cos y^2 + 2 * Real.cos y + 1 := by
  intro y
  apply square_expand

theorem solve_quadratic : ∃ (x:ℝ), x^2 + 2 * x - 8 = 0 := by
  use 2
  norm_num

/- The following proof will not typecheck.

example : Real.pi^2 + 2 * Real.pi - 8 = 0 := by
  apply solve_quadratic

-/

namespace Remark_A_5_1

variable (Man : Type)
variable (Mortal : Man → Prop)

example
  (premise : ∀ m : Man, Mortal m)
  (Socrates : Man) :
  Mortal Socrates := by
    apply premise  -- `exact premise Socrates` would also work

end Remark_A_5_1

example :
  (∀ a:ℝ, ∀ b:ℝ, (a+b)^2 = a^2 + 2*a*b + b^2)
  = (∀ b:ℝ, ∀ a:ℝ, (a+b)^2 = a^2 + 2*a*b + b^2)
  := by
    rw [forall_comm]

example :
  (∃ a:ℝ, ∃ b:ℝ, a^2 + b^2 = 0)
  = (∃ b:ℝ, ∃ a:ℝ, a^2 + b^2 = 0)
  := by
    rw [exists_comm]

example : ∀ n:ℤ, ∃ m:ℤ, m > n := by
  intro n
  use n + 1
  linarith

example : ¬ ∃ m:ℤ, ∀ n:ℤ, m > n := by
  by_contra h
  choose m hm using h -- `obtain ⟨m, hm⟩ := h` would also work here
  specialize hm (m+1)
  linarith

/-- Exercise A.5.1 -/
def Exercise_A_5_1a : Decidable (∀ x > (0:ℝ), ∀ y > (0:ℝ), y^2 = x ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Exercise_A_5_1b : Decidable (∃ x > (0:ℝ), ∀ y > (0:ℝ), y^2 = x ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Exercise_A_5_1c : Decidable (∃ x > (0:ℝ), ∃ y > (0:ℝ), y^2 = x ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Exercise_A_5_1d : Decidable (∀ y > (0:ℝ), ∃ x > (0:ℝ), y^2 = x ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Exercise_A_5_1e : Decidable (∃ y > (0:ℝ), ∀ x > (0:ℝ), y^2 = x ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry
