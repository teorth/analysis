import Mathlib.Tactic
import Analysis.Section_10_2

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
theorem strictMono_of_positive_derivative {a b:ℝ} (_hab: a < b) {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hpos: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x > 0) :
    StrictMonoOn f (.Icc a b) := by
  unfold StrictMonoOn
  intro x₁ hx₁ x₂ hx₂ hxx
  have hsub : Set.Icc x₁ x₂ ⊆ Set.Icc a b := Set.Icc_subset_Icc hx₁.1 hx₂.2
  have hcont : ContinuousOn f (Set.Icc x₁ x₂) := hderiv.continuousOn.mono hsub
  have hdiffsub : DifferentiableOn ℝ f (Set.Ioo x₁ x₂) :=
    hderiv.mono (subset_trans Set.Ioo_subset_Icc_self hsub)
  rcases _root_.HasDerivWithinAt.mean_value hxx hcont hdiffsub with ⟨c, hc, hpente⟩
  rw [Set.mem_Ioo] at hc
  have hcab : c ∈ Set.Ioo a b := by
    constructor
    · exact lt_of_le_of_lt hx₁.1 hc.1
    · exact lt_of_lt_of_le hc.2 hx₂.2
  have hdp : derivWithin f (Set.Icc a b) c > 0 := hpos c hcab
  have hpenteder : (f x₂ - f x₁) / (x₂ - x₁) = derivWithin f (Set.Icc a b) c := by
    have hpentec : HasDerivAt f ((f x₂ - f x₁) / (x₂ - x₁)) c :=
      hpente.hasDerivAt (IsOpen.mem_nhds isOpen_Ioo hc)
    have hvoic : Set.Icc a b ∈ nhds c := by
      apply Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hcab)
      exact Set.Ioo_subset_Icc_self
    rw [derivWithin_of_mem_nhds hvoic]
    exact hpentec.deriv.symm
  rw [← hpenteder] at hdp
  have h_denom_pos : 0 < x₂ - x₁ := sub_pos.mpr hxx
  have h_num_pos : f x₂ - f x₁ > 0 := by
    exact (div_pos_iff_of_pos_right h_denom_pos).mp hdp
  nlinarith

theorem strictAnti_of_negative_derivative {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hneg: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x < 0) :
    StrictAntiOn f (.Icc a b) := by
  have hpos: ∀ x ∈ Set.Ioo a b, derivWithin (- f) (.Icc a b) x > 0 := by
     intro x hx
     rw [derivWithin.neg]
     specialize hneg x hx
     linarith
  have hdiff : DifferentiableOn ℝ (- f) (.Icc a b) := by
    apply DifferentiableOn.neg
    exact hderiv
  have h_strict_mono : StrictMonoOn (- f) (.Icc a b) := strictMono_of_positive_derivative hab hdiff hpos
  unfold StrictAntiOn
  intro x₁ hx₁ x₂ hx₂ hxx
  have h_sub : - f x₁ < - f x₂ := by
    apply h_strict_mono hx₁ hx₂ hxx
  linarith

/-- Example 10.3.2 -/
example : ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ ¬ DifferentiableAt ℝ f 0 := by 
  let f : ℝ → ℝ := fun x ↦ x + max x 0
  use f
  constructor
  apply Continuous.add
  exact continuous_id
  refine Continuous.max ?_ ?_
  exact continuous_id
  exact continuous_const
  constructor
  apply StrictMono.add_monotone strictMono_id
  intro a b h
  apply max_le_max
  exact h        
  linarith

  have h_neg : ∀ x ≤ 0, f x = x := by
    intro x hx
    dsimp [f]
    rw [max_eq_right hx]
    simp
  have h_pos : ∀ x ≥  0, f x = 2 * x := by
    intro x hx
    dsimp [f]
    rw [max_eq_left hx]
    linarith

  intro hdiff
  have hderiv : HasDerivAt f (deriv f 0) 0 := hdiff.hasDerivAt
  rw[HasDerivAt] at hderiv
  rw[HasDerivAtFilter] at hderiv
  let L := deriv f 0
  have hL : HasDerivAt f L 0 := hdiff.hasDerivAt

  have h_L_is_1 : L = 1 := by
    have h_deriv_x : HasDerivWithinAt id (1 : ℝ) (Set.Iic (0 : ℝ)) (0 : ℝ) :=
      hasDerivWithinAt_id (0 : ℝ) (Set.Iic (0 : ℝ))
    have h_deriv_f : HasDerivWithinAt f L (Set.Iic 0) 0 :=
      (HasDerivAt.hasDerivWithinAt hL).mono (Set.subset_univ _)
    have h_unique : UniqueDiffWithinAt ℝ (Set.Iic (0 : ℝ)) 0 :=
      uniqueDiffOn_Iic (0 : ℝ) 0 (Set.mem_Iic.mpr (le_refl 0))
    have h_deriv_f_val : HasDerivWithinAt f 1 (Set.Iic 0) 0 := by
      apply h_deriv_x.congr
      · intro x hx; rw [h_neg  x hx]; rfl  
      · rw [h_neg 0 (le_refl _)]; rfl     
    have h_eq := h_unique.eq h_deriv_f h_deriv_f_val
    simp at h_eq
    exact h_eq

  have h_L_is_2 : L = 2 := by
    have h_deriv_2x : HasDerivWithinAt (fun x ↦ 2 * x) (2 : ℝ) (Set.Ici (0 : ℝ)) (0 : ℝ) := by
      convert (hasDerivWithinAt_id (0 : ℝ) (Set.Ici (0 : ℝ))).const_mul (2 : ℝ)
      simp
    have h_deriv_f : HasDerivWithinAt f L (Set.Ici 0) 0 :=
      (HasDerivAt.hasDerivWithinAt hL).mono (Set.subset_univ _)
    have h_unique : UniqueDiffWithinAt ℝ (Set.Ici (0 : ℝ)) 0 :=
      uniqueDiffOn_Ici (0 : ℝ) 0 (Set.mem_Ici.mpr (le_refl 0))
    have h_deriv_f_val : HasDerivWithinAt f 2 (Set.Ici 0) 0 := by
      apply h_deriv_2x.congr
      · intro x hx; rw [h_pos x hx]
      · rw [h_pos 0 (le_refl _)]    
    have h_eq := h_unique.eq h_deriv_f h_deriv_f_val
    simp at h_eq
    exact h_eq
  rw [h_L_is_1] at h_L_is_2
  norm_num at h_L_is_2

/-- Exercise 10.3.3 -/
example : ∃ f: ℝ → ℝ, StrictMono f ∧ Differentiable ℝ f ∧ deriv f 0 = 0 := by 
  use fun x ↦ x^3
  constructor
  refine Odd.strictMono_pow ?_
  use 1
  norm_num
  constructor
  exact differentiable_pow 3
  rw [deriv_pow_field]
  norm_num
  

/-- Exercise 10.3.5 -/
example : ∃ (X : Set ℝ) (f : ℝ → ℝ), DifferentiableOn ℝ f X ∧
  (∀ x ∈ X, derivWithin f X x > 0) ∧ ¬ StrictMonoOn f X  := by
  use {0}ᶜ, fun x ↦ -x⁻¹
  refine ⟨?_, ?_, ?_⟩
  apply DifferentiableOn.neg
  apply DifferentiableOn.inv
  exact differentiableOn_id
  intro x hx
  exact hx
  intro x hx
  rw [derivWithin_of_isOpen isOpen_compl_singleton hx]
  have h_ne : x ≠ 0 := hx
  have h_diff : DifferentiableAt ℝ (fun y ↦ y⁻¹) x := differentiableAt_inv h_ne
  change deriv (-(fun x : ℝ ↦ x⁻¹)) x > 0
  rw [deriv.neg]
  rw [deriv_inv]
  simp; positivity
  rw [StrictMonoOn]
  push_neg
  use -1; norm_num; use 1; norm_num


end Chapter10
