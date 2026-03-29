import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_3

/-!
# Analysis I, Section 11.4: Basic properties of the Riemann integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Basic properties of the Riemann integral.

-/

namespace Chapter11
open Chapter9

/-- Theorem 11.4.1(a) / Exercise 11.4.1 -/
theorem IntegrableOn.add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f + g) I ∧ integ (f + g) I = integ f I + integ g I := by
  sorry

/-- Theorem 11.4.1(b) / Exercise 11.4.1 -/
theorem IntegrableOn.smul {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (c • f) I ∧ integ (c • f) I = c * integ f I := by
  sorry

theorem IntegrableOn.neg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (-f) I ∧ integ (-f) I = -integ f I := by have := IntegrableOn.smul (-1) hf; aesop

/-- Theorem 11.4.1(c) / Exercise 11.4.1 -/
theorem IntegrableOn.sub {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f - g) I ∧ integ (f - g) I = integ f I - integ g I := by
  sorry

/-- Theorem 11.4.1(d) / Exercise 11.4.1 -/
theorem IntegrableOn.nonneg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) (hf_nonneg: ∀ x ∈ I, 0 ≤ f x) :
  0 ≤ integ f I := by
  sorry

/-- Theorem 11.4.1(e) / Exercise 11.4.1 -/
theorem IntegrableOn.mono {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (h: MajorizesOn g f I) :
  integ f I ≤ integ g I := by
  sorry

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const (c:ℝ) (I: BoundedInterval) :
  IntegrableOn (fun _ ↦ c) I ∧ integ (fun _ ↦ c) I = c * |I|ₗ := by
  sorry

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const' {I: BoundedInterval} {f:ℝ → ℝ} (hf: ConstantOn f I) :
  IntegrableOn f I ∧ integ f I = (constant_value_on f I) * |I|ₗ := by
  sorry


open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  IntegrableOn (fun x ↦ if x ∈ I then f x else 0) J := by
  sorry

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend' {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  sorry

/-- Theorem 11.4.1 (h) (Laws of integration) / Exercise 11.4.1 -/
theorem IntegrableOn.join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) :
  IntegrableOn f I ∧ IntegrableOn f J ∧ integ f K = integ f I + integ f J := by
  sorry

/-- A variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.mono' {I J: BoundedInterval} (hIJ: J ⊆ I)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : IntegrableOn f J := by
  sorry

/-- A further variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.eq {I J: BoundedInterval} (hIJ: J ⊆ I)
  (ha: J.a = I.a) (hb: J.b = I.b)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : integ f J = integ f I := by
  sorry

/-- A handy little lemma for "epsilon of room" type arguments -/
lemma nonneg_of_le_const_mul_eps {x C:ℝ} (h: ∀ ε>0, x ≤ C * ε) : x ≤ 0 := by
  by_cases hC: C > 0
  . by_contra!
    specialize h (x/(2*C)) (by positivity); convert_to x ≤ x/2 at h; grind
    linarith
  specialize h 1 ?_ <;> grind

/-- Theorem 11.4.3 (Max and min preserve integrability)-/
theorem IntegrableOn.max {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊔ g) I  := by
  -- This proof is written to follow the structure of the original text.
  unfold IntegrableOn at hf hg
  have hmax_bound : BddOn (f ⊔ g) I := by
    choose M hM using hf.1; choose M' hM' using hg.1
    use M ⊔ M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.sup_apply]
    exact abs_max_le_max_abs_abs.trans (sup_le_sup hM hM')
  have lower_le_upper : 0 ≤ upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I := by linarith [lower_integral_le_upper hmax_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I ≤ 4*ε := by
    choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I
    by grind)
    choose g' hg'min hg'const hg'int using gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by grind)
    choose f'' hf''max hf''const hf''int using lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε by grind)
    choose g'' hg''max hg''const hg''int using lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by grind)
    set h := (f'' - f') + (g'' - g')
    have hf'_integ := integ_of_piecewise_const hf'const
    have hg'_integ := integ_of_piecewise_const hg'const
    have hf''_integ := integ_of_piecewise_const hf''const
    have hg''_integ := integ_of_piecewise_const hg''const
    have hf''f'_integ := hf''_integ.1.sub hf'_integ.1
    have hg''g'_integ := hg''_integ.1.sub hg'_integ.1
    have hh_IntegrableOn.eq := hf''f'_integ.1.add hg''g'_integ.1
    have hinteg_le : integ h I ≤ 4 * ε := by linarith
    have hf''g''_const := hf''const.max hg''const
    have hf''g''_maj : MajorizesOn (f'' ⊔ g'') (f ⊔ g) I := by
      sorry
    have hf'g'_const := hf'const.max hg'const
    have hf'g'_maj : MinorizesOn (f' ⊔ g') (f ⊔ g) I := by
      sorry
    have hff'g''_ge := upper_integral_le_integ hmax_bound hf''g''_maj hf''g''_const
    have hf'g'_le := integ_le_lower_integral hmax_bound hf'g'_maj hf'g'_const
    have : MinorizesOn (f'' ⊔ g'') (f' ⊔ g' + h) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx; specialize hf''max _ hx; specialize hg''max _ hx
      simp [h]; split_ands <;> linarith [le_max_left (f' x) (g' x), le_max_right (f' x) (g' x)]
    have hf'g'_integ := integ_of_piecewise_const hf'g'_const
    have hf''g''_integ := integ_of_piecewise_const hf''g''_const
    have hf'g'h_integ := hf'g'_integ.1.add hh_IntegrableOn.eq.1
    rw [MinorizesOn.iff] at this
    linarith [hf''g''_integ.1.mono hf'g'h_integ.1 this]
  exact ⟨ hmax_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩



/-- Theorem 11.4.5 / Exercise 11.4.3.  The objective here is to create a shorter proof than the one above.-/
theorem IntegrableOn.min {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊓ g) I  := by
  sorry

/-- Corollary 11.4.4 -/
theorem IntegrableOn.abs {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (abs f) I := by
  have := (IntegrableOn.const 0 I).1
  convert ((hf.max this).sub (hf.min this)).1 using 1
  ext x; obtain h | h := (show f x ≤ 0 ∨ f x ≥ 0 by grind) <;> simp [h]

/-- Theorem 11.4.5 (Products preserve Riemann integrability).
It is convenient to first establish the non-negative case.-/
theorem integ_of_mul_nonneg {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (hf_nonneg: MajorizesOn f 0 I) (hg_nonneg: MajorizesOn g 0 I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hI : (I:Set ℝ).Nonempty
  swap
  . apply (integ_on_subsingleton _).1
    rw [←BoundedInterval.length_of_subsingleton]
    simp_all [Set.not_nonempty_iff_eq_empty]
  unfold IntegrableOn at hf hg
  choose M₁ hM₁ using hf.1
  choose M₂ hM₂ using hg.1
  have hM₁pos : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ hI.some hI.some_mem)
  have hM₂pos : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ hI.some hI.some_mem)
  have hmul_bound : BddOn (f * g) I := by
    use M₁ * M₂; peel hM₁ with x hx hM₁; specialize hM₂ _ hx
    simp [abs_mul]; apply mul_le_mul hM₁ hM₂ <;> positivity
  have lower_le_upper : 0 ≤ upper_integral (f * g) I - lower_integral (f * g) I := by
    linarith [lower_integral_le_upper hmul_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f * g) I - lower_integral (f * g) I ≤ 2*(M₁+M₂)*ε := by
    have : ∃ f', MinorizesOn f' f I ∧ PiecewiseConstantOn f' I ∧ integ f I - ε < PiecewiseConstantOn.integ f' I ∧ MajorizesOn f' 0 I := by
      choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I by linarith)
      use max f' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hf_nonneg with x hx _; specialize hf'min _ hx; aesop
      . exact hf'const.max hzero
      . apply lt_of_lt_of_le hf'int (hf'const.integ_mono _ (hf'const.max hzero)); simp
      intro _; simp
    choose f' hf'min hf'const hf'int hf'_nonneg using this
    have : ∃ g', MinorizesOn g' g I ∧ PiecewiseConstantOn g' I ∧ integ g I - ε < PiecewiseConstantOn.integ g' I ∧ MajorizesOn g' 0 I := by
      obtain ⟨ g', hg'min, hg'const, hg'int ⟩ := gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by linarith)
      use max g' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hg_nonneg with x hx _; specialize hg'min _ hx; aesop
      . exact hg'const.max hzero
      . apply lt_of_lt_of_le hg'int (hg'const.integ_mono _ (hg'const.max hzero)); simp
      intro _; simp
    choose g' hg'min hg'const hg'int hg'_nonneg using this
    have : ∃ f'', MajorizesOn f'' f I ∧ PiecewiseConstantOn f'' I ∧ PiecewiseConstantOn.integ f'' I < integ f I + ε ∧ MinorizesOn f'' (fun _ ↦ M₁) I := by
      obtain ⟨ f'', hf''maj, hf''const, hf''int ⟩ := lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε  by linarith)
      use min f'' (fun _ ↦ M₁)
      have hM₁_piece := (ConstantOn.of_const' M₁ I).piecewiseConstantOn
      split_ands
      . peel hM₁ with x hx hM₁; rw [abs_le'] at hM₁
        simp [hf''maj _ hx, hM₁.1]
      . exact hf''const.min hM₁_piece
      . apply lt_of_le_of_lt ((hf''const.min hM₁_piece).integ_mono _ hf''const) hf''int
        simp
      intro _; simp
    choose f'' hf''maj hf''const hf''int hf''bound using this
    have : ∃ g'', MajorizesOn g'' g I ∧ PiecewiseConstantOn g'' I ∧ PiecewiseConstantOn.integ g'' I < integ g I + ε ∧ MinorizesOn g'' (fun _ ↦ M₂) I := by
      obtain ⟨ g'', hg''maj, hg''const, hg''int ⟩ := lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by linarith)
      use min g'' (fun _ ↦ M₂)
      have hM₂_piece := (ConstantOn.of_const' M₂ I).piecewiseConstantOn
      split_ands
      . peel hM₂ with x hx hM₂; rw [abs_le'] at hM₂
        simp [hg''maj _ hx, hM₂.1]
      . exact hg''const.min hM₂_piece
      . apply lt_of_le_of_lt ((hg''const.min hM₂_piece).integ_mono _ hg''const) hg''int
        simp
      intro _ _; simp
    choose g'' hg''maj hg''const hg''int hg''bound using this
    have hf'g'_const := hf'const.mul hg'const
    have hf'g'_maj : MinorizesOn (f' * g') (f * g) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx;
      specialize hf'_nonneg _ hx; specialize hg'_nonneg _ hx
      simp at *; apply mul_le_mul hf'min hg'min <;> grind
    have hf''g''_const := hf''const.mul hg''const
    have hf''g''_maj : MajorizesOn (f'' * g'') (f * g) I := by
      peel hf''maj with x hx hf''maj; specialize hg''maj _ hx
      specialize hg_nonneg _ hx; specialize hf_nonneg _ hx
      simp at *; apply mul_le_mul hf''maj hg''maj <;> grind
    have hupper_le := upper_integral_le_integ hmul_bound hf''g''_maj hf''g''_const
    have hlower_ge := integ_le_lower_integral hmul_bound hf'g'_maj hf'g'_const
    have hh_const := hf''g''_const.sub hf'g'_const
    have hh_integ := hf''g''_const.integ_sub hf'g'_const
    have hhmin : MinorizesOn (f'' * g'' - f' * g') (M₁ • (g''-g') + M₂ • (f''-f')) I := by
      intro x hx
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        _ = (f'' x) * (g'' x - g' x) + (g' x) * (f'' x - f' x) := by ring
        _ ≤ _ := by gcongr <;> grind
    have hg''g'_const := hg''const.sub hg'const
    have hg''g'_integ := hg''const.integ_sub hg'const
    have hM₁g''g'_const := hg''g'_const.smul M₁
    have hM₁g''g_integ := hg''g'_const.integ_smul M₁
    have hf''f'_const := hf''const.sub hf'const
    have hf''f_integ := hf''const.integ_sub hf'const
    have hM₂f''f'_const := hf''f'_const.smul M₂
    have hM₂f''f_integ := hf''f'_const.integ_smul M₂
    have hsum_const := hM₁g''g'_const.add hM₂f''f'_const
    have hsum_integ := hM₁g''g'_const.integ_add hM₂f''f'_const
    have hsum_bound := hh_const.integ_mono hhmin hsum_const
    calc
      _ ≤ M₁ * PiecewiseConstantOn.integ (g'' - g') I + M₂ * PiecewiseConstantOn.integ (f'' - f') I := by linarith
      _ ≤ M₁ * (2*ε) + M₂ * (2*ε) := by gcongr <;> linarith
      _ = _ := by ring
  exact ⟨ hmul_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩


theorem integ_of_mul {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  set fplus := max f (fun _ ↦ 0)
  set fminus := -min f (fun _ ↦ 0)
  set gplus := max g (fun _ ↦ 0)
  set gminus := -min g (fun _ ↦ 0)
  have := (IntegrableOn.const 0 I).1
  observe hfplus_integ : IntegrableOn fplus I
  observe hgplus_integ : IntegrableOn gplus I
  have hfminus_integ : IntegrableOn fminus I := (hf.min this).neg.1
  have hgminus_integ : IntegrableOn gminus I := (hg.min this).neg.1
  have hfplus_nonneg : MajorizesOn fplus 0 I := by intro _; simp [fplus]
  have hfminus_nonneg : MajorizesOn fminus 0 I := by intro _; simp [fminus]
  have hgplus_nonneg : MajorizesOn gplus 0 I := by intro _; simp [gplus]
  have hgminus_nonneg : MajorizesOn gminus 0 I := by intro _; simp [gminus]
  have hfplusgplus := integ_of_mul_nonneg hfplus_integ hgplus_integ hfplus_nonneg hgplus_nonneg
  have hfplusgminus := integ_of_mul_nonneg hfplus_integ hgminus_integ hfplus_nonneg hgminus_nonneg
  have hfminusgplus := integ_of_mul_nonneg hfminus_integ hgplus_integ hfminus_nonneg hgplus_nonneg
  have hfminusgminus := integ_of_mul_nonneg hfminus_integ hgminus_integ hfminus_nonneg hgminus_nonneg
  rw [show f = fplus - fminus by ext; simp [fplus, fminus],
      show g = gplus - gminus by ext; simp [gplus, gminus]]
  ring_nf
  exact ((hfplusgplus.add (hfplusgminus.neg.1.sub hfminusgplus).1).1.add hfminusgminus).1
open BoundedInterval

/-- Exercise 11.4.2 -/
theorem IntegrableOn.split {I: BoundedInterval} {f: ℝ → ℝ} (hf: IntegrableOn f I) (P: Partition I) :
  integ f I = ∑ J ∈ P.intervals, integ f J := by
    sorry

end Chapter11
