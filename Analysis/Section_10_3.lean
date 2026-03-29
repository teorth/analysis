import Mathlib.Tactic

/-!
# Analysis I, Section 10.3: Monotone functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relations between monotonicity and differentiability.

-/

namespace Chapter10

/-- Proposition 10.3.1 / Exercise 10.3.1 -/
theorem derivative_of_monotone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Monotone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≥ 0 := by
  sorry

theorem derivative_of_antitone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Antitone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≤ 0 := by
  sorry

/-- Proposition 10.3.3 / Exercise 10.3.4 -/
theorem strictMono_of_positive_derivative {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hpos: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x > 0) :
    StrictMonoOn f (.Icc a b) := by
  sorry

theorem strictAnti_of_negative_derivative {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hneg: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x < 0) :
    StrictAntiOn f (.Icc a b) := by
  sorry

/-- Example 10.3.2 -/
example : ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ ¬ DifferentiableAt ℝ f 0 := by sorry

/-- Exercise 10.3.3 -/
example : ∃ f: ℝ → ℝ, StrictMono f ∧ Differentiable ℝ f ∧ deriv f 0 = 0 := by sorry

/-- Exercise 10.3.5 -/
example : ∃ (X : Set ℝ) (f : ℝ → ℝ), DifferentiableOn ℝ f X ∧
  (∀ x ∈ X, derivWithin f X x > 0) ∧ ¬ StrictMonoOn f X  := by
  sorry

end Chapter10
