import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4
import Analysis.Section_10_1

/-!
# Analysis I, Section 10.4: Inverse functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The inverse function theorem.

-/

open Chapter9
namespace Chapter10

/-- Lemma 10.4.1 -/
theorem _root_.HasDerivWithinAt.of_inverse {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ * f'x₀ = 1 := by
  -- This proof is written to follow the structure of the original text.
  have h1 : HasDerivWithinAt id (g'y₀ * f'x₀) X x₀ := by
    apply (hf.of_comp hfx₀ hfXY _).congr _ (hgf _ hx₀).symm <;> grind
  observe h2 : HasDerivWithinAt id 1 X x₀
  solve_by_elim [derivative_unique]

theorem _root_.HasDerivWithinAt.of_inverse' {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ = 1/f'x₀ :=
    eq_one_div_of_mul_eq_one_left (hf.of_inverse hfXY hgf hx₀ hfx₀ hcluster hg)

theorem _root_.HasDerivWithinAt.of_inverse_of_zero_deriv {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f 0 X x₀) :
  ¬ DifferentiableWithinAt ℝ g Y y₀ := by
  by_contra this; rw [DifferentiableWithinAt.iff] at this; choose _ hg using this
  apply hf.of_inverse at hg <;> grind

example : ¬ DifferentiableWithinAt ℝ (fun x:ℝ ↦ x^(1/3:ℝ)) (.Ici 0) 0 := by sorry

/-- Theorem 10.4.2 (Inverse function theorem) -/
theorem inverse_function_theorem {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgYX: ∀ y ∈ Y, g y ∈ X)
  (hgf: ∀ x ∈ X, g (f x) = x) (hfg: ∀ y ∈ Y, f (g y) = y)
  {x₀ y₀ f'x₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀) (hne : f'x₀ ≠ 0)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: ContinuousWithinAt g Y y₀) :
    HasDerivWithinAt g (1/f'x₀) Y y₀ := by
    -- This proof is written to follow the structure of the original text.
    have had : AdherentPt y₀ (Y \ {y₀}) := by
      simp [←AdherentPt_def, limit_of_AdherentPt] at *
      choose x hx hconv using hcluster; use f ∘ x
      split_ands; grind
      rw [←hfx₀]
      apply hconv.comp_of_continuous hx₀ _ (fun n ↦ (hx n).1)
      exact ContinuousWithinAt.of_differentiableWithinAt (DifferentiableWithinAt.of_hasDeriv hf)
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _ had]
    intro y hy hconv
    set x : ℕ → ℝ := fun n ↦ g (y n)
    have hy' : ∀ n, y n ∈ Y := by aesop
    have hy₀: y₀ ∈ Y := by aesop
    have hx : ∀ n, x n ∈ X \ {x₀}:= by
      sorry
    replace hconv := hconv.comp_of_continuous hy₀ hg hy'
    have had' : AdherentPt x₀ (X \ {x₀}) := by rwa [AdherentPt_def]
    have hgy₀ : g y₀ = x₀ := by aesop
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _ had'] at hf
    convert (hf _ hx _).inv₀ _ using 2 with n <;> grind

/-- Exercise 10.4.1(a) -/
example {n:ℕ} (hn: n > 0) : ContinuousOn (fun x:ℝ ↦ x^(1/n:ℝ)) (.Ici 0) := by sorry

/-- Exercise 10.4.1(b) -/
example {n:ℕ} (hn: n > 0) {x:ℝ} (hx: x ∈ Set.Ici 0) : HasDerivWithinAt (fun x:ℝ ↦ x^(1/n:ℝ))
  ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1)) (.Ici 0) x := by sorry

/-- Exercise 10.4.2(a) -/
example (q:ℚ) {x:ℝ} (hx: x ∈ Set.Ici 0) :
  HasDerivWithinAt (fun x:ℝ ↦ x^(q:ℝ)) (q * x^(q-1:ℝ)) (.Ici 0) x := by
  sorry

/-- Exercise 10.4.2(b) -/
example (q:ℚ) : (nhdsWithin 1 (.Ici 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^(q:ℝ)-1)/(x-1)) (nhds q) := by
  sorry

/-- Exercise 10.4.3(a) -/
example (α:ℝ) : (nhdsWithin 1 (.Ici 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^α-1^α)/(x-1)) (nhds α) := by
  sorry

/-- Exercise 10.4.2(b) -/
example (α:ℝ) {x:ℝ} (hx: x ∈ Set.Ici 0) : HasDerivWithinAt (fun x:ℝ ↦ x^α) (α * x^(α-1)) (.Ici 0) x := by
  sorry

end Chapter10
