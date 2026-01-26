import Analysis.MeasureTheory.Section_1_3_3

/-!
# Introduction to Measure Theory, Section 1.3.4: Absolute integrability

A companion to (the introduction to) Section 1.3.4 of the book "An introduction to Measure Theory".

-/

-- It is probably possible to unify the real and complex theory here using the `RCLike` class in Mathlib, but we will adopt the more pedestrian approach of duplicating definitions in the real and complex cases.

/-- Definition 1.3.17 -/

def UnsignedAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := UnsignedMeasurable f ∧ UnsignedLebesgueIntegral f < ⊤

def ComplexAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ComplexMeasurable f ∧ UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤

def RealAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := RealMeasurable f ∧ UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤

lemma ComplexAbsolutelyIntegrable.abs {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.abs_fun f) := by
  constructor
  · -- UnsignedMeasurable (EReal.abs_fun f)
    constructor
    · -- Unsigned: ∀ x, EReal.abs_fun f x ≥ 0
      intro x
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · -- Exists approximating unsigned simple functions
      obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
      use fun n => EReal.abs_fun (g n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  · exact hf.2

lemma RealAbsolutelyIntegrable.abs {d:ℕ} (f: EuclideanSpace' d → ℝ) (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.abs_fun f) := by
  constructor
  · -- UnsignedMeasurable (EReal.abs_fun f)
    constructor
    · intro x
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
      use fun n => EReal.abs_fun (g n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  · exact hf.2



lemma RealAbsolutelyIntegrable.iff {d:ℕ} (f: EuclideanSpace' d → ℝ) : RealAbsolutelyIntegrable f ↔ ComplexAbsolutelyIntegrable (fun x ↦ (f x:ℂ)) := by
  constructor
  · intro ⟨hf_meas, hf_integ⟩
    constructor
    · exact RealMeasurable.iff.mp hf_meas
    · convert hf_integ using 2
      funext x
      simp only [EReal.abs_fun]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]
  · intro ⟨hf_meas, hf_integ⟩
    constructor
    · exact RealMeasurable.iff.mpr hf_meas
    · convert hf_integ using 2
      funext x
      simp only [EReal.abs_fun]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]

lemma ComplexAbsolutelyIntegrable.re {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (Complex.re_fun f) := by
  have h_re_meas : RealMeasurable (Complex.re_fun f) := ComplexMeasurable.iff.mp hf.1 |>.1
  constructor
  · exact h_re_meas
  · have h_le : ∀ x, EReal.abs_fun (Complex.re_fun f) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Complex.re_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm (f x)
    -- Build UnsignedMeasurable for |Re(f)| directly from RealMeasurable (re_fun f)
    have h_re_abs_meas : UnsignedMeasurable (EReal.abs_fun (Complex.re_fun f)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := h_re_meas
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun, Complex.re_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact h_re_abs_meas
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

lemma ComplexAbsolutelyIntegrable.im {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (Complex.im_fun f) := by
  have h_im_meas : RealMeasurable (Complex.im_fun f) := ComplexMeasurable.iff.mp hf.1 |>.2
  constructor
  · exact h_im_meas
  · have h_le : ∀ x, EReal.abs_fun (Complex.im_fun f) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Complex.im_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs]
      exact Complex.abs_im_le_norm (f x)
    -- Build UnsignedMeasurable for |Im(f)| directly from RealMeasurable (im_fun f)
    have h_im_abs_meas : UnsignedMeasurable (EReal.abs_fun (Complex.im_fun f)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := h_im_meas
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun, Complex.im_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact h_im_abs_meas
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

lemma ComplexAbsolutelyIntegrable.iff {d:ℕ} (f: EuclideanSpace' d → ℂ) : ComplexAbsolutelyIntegrable f ↔ RealAbsolutelyIntegrable (Complex.re_fun f) ∧ RealAbsolutelyIntegrable (Complex.im_fun f) := by
  constructor
  · intro hf
    exact ⟨ComplexAbsolutelyIntegrable.re f hf, ComplexAbsolutelyIntegrable.im f hf⟩
  · intro ⟨hre, him⟩
    constructor
    · exact ComplexMeasurable.iff.mpr ⟨hre.1, him.1⟩
    · -- Use |f| ≤ |Re(f)| + |Im(f)| to bound the integral
      have h_bound : ∀ x, EReal.abs_fun f x ≤
          (EReal.abs_fun (Complex.re_fun f) + EReal.abs_fun (Complex.im_fun f)) x := fun x => by
        simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
        apply EReal.coe_le_coe_iff.mpr
        calc ‖f x‖ = Real.sqrt ((f x).re^2 + (f x).im^2) := Complex.norm_eq_sqrt_sq_add_sq (f x)
          _ ≤ |((f x).re)| + |(f x).im| := by
            have h1 : (f x).re^2 + (f x).im^2 ≤ (|(f x).re| + |(f x).im|)^2 := by
              have h_cross : 0 ≤ 2 * |(f x).re| * |(f x).im| := by positivity
              calc (f x).re^2 + (f x).im^2
                  ≤ (f x).re^2 + 2 * |(f x).re| * |(f x).im| + (f x).im^2 := by linarith
                _ = |(f x).re|^2 + 2 * |(f x).re| * |(f x).im| + |(f x).im|^2 := by rw [sq_abs, sq_abs]
                _ = (|(f x).re| + |(f x).im|)^2 := by ring
            have h2 : 0 ≤ |(f x).re| + |(f x).im| := by positivity
            calc Real.sqrt ((f x).re^2 + (f x).im^2)
                ≤ Real.sqrt ((|(f x).re| + |(f x).im|)^2) := Real.sqrt_le_sqrt h1
              _ = |(f x).re| + |(f x).im| := Real.sqrt_sq h2
          _ = ‖(f x).re‖ + ‖(f x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      -- Apply monotonicity and additivity of integral
      have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun f) ≤
                    UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f) +
                                              EReal.abs_fun (Complex.im_fun f)) := by
        apply LowerUnsignedLebesgueIntegral.mono
        · constructor
          · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
          · obtain ⟨g, hg_simple, hg_conv⟩ := ComplexMeasurable.iff.mpr ⟨hre.1, him.1⟩
            use fun n => EReal.abs_fun (g n)
            constructor
            · intro n; exact (hg_simple n).abs
            · intro x
              simp only [EReal.abs_fun]
              exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
        · exact hre.abs.1.add him.abs.1
        · exact AlmostAlways.ofAlways h_bound
      -- UnsignedLebesgueIntegral is defined as LowerUnsignedLebesgueIntegral
      have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f) +
                                             EReal.abs_fun (Complex.im_fun f)) =
                   UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) +
                   UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) := by
        exact LowerUnsignedLebesgueIntegral.add hre.abs.1 him.abs.1
          (UnsignedMeasurable.add hre.abs.1 him.abs.1)
      rw [h_add] at h_mono
      calc UnsignedLebesgueIntegral (EReal.abs_fun f)
          ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) +
            UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) := h_mono
        _ < ⊤ := EReal.add_lt_top (lt_top_iff_ne_top.mp hre.2) (lt_top_iff_ne_top.mp him.2)

noncomputable def UnsignedAbsolutelyIntegrable.integ {d:ℕ} (f: EuclideanSpace' d → EReal) (_: UnsignedAbsolutelyIntegrable f) : ℝ := (UnsignedLebesgueIntegral f).toReal

noncomputable def ComplexAbsolutelyIntegrable.norm {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ℝ := hf.abs.integ

noncomputable def RealAbsolutelyIntegrable.norm {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : ℝ := hf.abs.integ


def RealMeasurable.measurable_pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) : UnsignedMeasurable (EReal.pos_fun f) := by
  constructor
  · -- Unsigned: ∀ x, EReal.pos_fun f x ≥ 0
    intro x
    simp only [EReal.pos_fun]
    exact EReal.coe_nonneg.mpr (le_max_right _ _)
  · -- Exists approximating unsigned simple functions
    obtain ⟨g, hg_simple, hg_conv⟩ := hf
    use fun n => EReal.pos_fun (g n)
    constructor
    · intro n; exact (hg_simple n).pos
    · intro x
      simp only [EReal.pos_fun]
      have hcont : Continuous (fun y : ℝ => (max y 0).toEReal) :=
        continuous_coe_real_ereal.comp (continuous_max.comp (continuous_id.prodMk continuous_const))
      exact hcont.continuousAt.tendsto.comp (hg_conv x)

def RealMeasurable.measurable_neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) : UnsignedMeasurable (EReal.neg_fun f) := by
  constructor
  · -- Unsigned: ∀ x, EReal.neg_fun f x ≥ 0
    intro x
    simp only [EReal.neg_fun]
    exact EReal.coe_nonneg.mpr (le_max_right _ _)
  · -- Exists approximating unsigned simple functions
    obtain ⟨g, hg_simple, hg_conv⟩ := hf
    use fun n => EReal.neg_fun (g n)
    constructor
    · intro n; exact (hg_simple n).neg
    · intro x
      simp only [EReal.neg_fun]
      have hcont : Continuous (fun y : ℝ => (max (-y) 0).toEReal) :=
        continuous_coe_real_ereal.comp (continuous_max.comp (continuous_neg.prodMk continuous_const))
      exact hcont.continuousAt.tendsto.comp (hg_conv x)

def RealAbsolutelyIntegrable.pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.pos_fun f) := by
  constructor
  · exact hf.1.measurable_pos
  · -- UnsignedLebesgueIntegral (pos_fun f) ≤ UnsignedLebesgueIntegral (abs_fun f) < ⊤
    have h_le : ∀ x, EReal.pos_fun f x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.pos_fun, EReal.abs_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs, max_le_iff]
      exact ⟨le_abs_self _, abs_nonneg _⟩
    have h_mono : UnsignedLebesgueIntegral (EReal.pos_fun f) ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact hf.1.measurable_pos
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

def RealAbsolutelyIntegrable.neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.neg_fun f) := by
  constructor
  · exact hf.1.measurable_neg
  · -- UnsignedLebesgueIntegral (neg_fun f) ≤ UnsignedLebesgueIntegral (abs_fun f) < ⊤
    have h_le : ∀ x, EReal.neg_fun f x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.neg_fun, EReal.abs_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs, max_le_iff]
      exact ⟨neg_le_abs _, abs_nonneg _⟩
    have h_mono : UnsignedLebesgueIntegral (EReal.neg_fun f) ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact hf.1.measurable_neg
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

noncomputable def RealAbsolutelyIntegrable.integ {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : ℝ := hf.pos.integ - hf.neg.integ

noncomputable def ComplexAbsolutelyIntegrable.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ℂ := hf.re.integ + Complex.I * hf.im.integ

open Classical in
noncomputable def RealLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → ℝ) : ℝ  := if hf: RealAbsolutelyIntegrable f then hf.integ else 0

open Classical in
noncomputable def ComplexLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → ℂ) : ℂ  := if hf: ComplexAbsolutelyIntegrable f then hf.integ else 0

def RealSimpleFunction.absolutelyIntegrable_iff' {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : hf.AbsolutelyIntegrable ↔ RealAbsolutelyIntegrable f := by
  constructor
  · -- Forward: hf.AbsolutelyIntegrable → RealAbsolutelyIntegrable f
    intro hfi
    constructor
    · -- RealMeasurable f: use constant sequence
      exact ⟨fun _ => f, fun _ => hf, fun _ => tendsto_const_nhds⟩
    · -- UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤
      rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
      exact hfi
  · -- Backward: RealAbsolutelyIntegrable f → hf.AbsolutelyIntegrable
    intro ⟨_, hf_integ⟩
    rw [RealSimpleFunction.AbsolutelyIntegrable, ← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
    exact hf_integ

def ComplexSimpleFunction.absolutelyIntegrable_iff' {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ ComplexAbsolutelyIntegrable f := by
  constructor
  · -- Forward: hf.AbsolutelyIntegrable → ComplexAbsolutelyIntegrable f
    intro hfi
    constructor
    · -- ComplexMeasurable f: use constant sequence
      exact ⟨fun _ => f, fun _ => hf, fun _ => tendsto_const_nhds⟩
    · -- UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤
      rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
      exact hfi
  · -- Backward: ComplexAbsolutelyIntegrable f → hf.AbsolutelyIntegrable
    intro ⟨_, hf_integ⟩
    rw [ComplexSimpleFunction.AbsolutelyIntegrable, ← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
    exact hf_integ

def RealSimpleFunction.AbsolutelyIntegrable.integ_eq {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (hfi: hf.AbsolutelyIntegrable) : hf.integ = (hf.absolutelyIntegrable_iff'.mp hfi).integ := by
  -- hf.integ = (hf.pos).integ.toReal - (hf.neg).integ.toReal
  -- (hf.absolutelyIntegrable_iff'.mp hfi).integ = (UnsignedLebesgueIntegral (pos_fun f)).toReal - (UnsignedLebesgueIntegral (neg_fun f)).toReal
  simp only [RealSimpleFunction.integ, RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  congr 1
  · -- (hf.pos).integ.toReal = (UnsignedLebesgueIntegral (pos_fun f)).toReal
    rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.pos]
  · -- (hf.neg).integ.toReal = (UnsignedLebesgueIntegral (neg_fun f)).toReal
    rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.neg]

def ComplexSimpleFunction.AbsolutelyIntegrable.integ_eq {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (hfi: hf.AbsolutelyIntegrable) : hf.integ = (hf.absolutelyIntegrable_iff'.mp hfi).integ := by
  -- Both sides are defined as re.integ + I * im.integ
  simp only [ComplexSimpleFunction.integ, ComplexAbsolutelyIntegrable.integ]
  -- The key is that the re and im of the complex absolutely integrable give the same integral as the real simple function integrals
  have hf_re : RealSimpleFunction (Complex.re_fun f) := ComplexSimpleFunction.re hf
  have hf_im : RealSimpleFunction (Complex.im_fun f) := ComplexSimpleFunction.im hf
  congr 1
  · -- hf.re.integ = (hf.absolutelyIntegrable_iff'.mp hfi).re.integ
    have hre_fi : hf_re.AbsolutelyIntegrable := by
      rw [RealSimpleFunction.AbsolutelyIntegrable]
      have h := ComplexAbsolutelyIntegrable.re f (hf.absolutelyIntegrable_iff'.mp hfi)
      rw [RealAbsolutelyIntegrable, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf_re.abs] at h
      exact h.2
    have heq := RealSimpleFunction.AbsolutelyIntegrable.integ_eq hf_re hre_fi
    simp only [heq]
  · -- hf.im.integ = (hf.absolutelyIntegrable_iff'.mp hfi).im.integ
    have him_fi : hf_im.AbsolutelyIntegrable := by
      rw [RealSimpleFunction.AbsolutelyIntegrable]
      have h := ComplexAbsolutelyIntegrable.im f (hf.absolutelyIntegrable_iff'.mp hfi)
      rw [RealAbsolutelyIntegrable, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf_im.abs] at h
      exact h.2
    have heq := RealSimpleFunction.AbsolutelyIntegrable.integ_eq hf_im him_fi
    simp only [heq]

theorem RealAbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) : RealAbsolutelyIntegrable (f + g) := by
  constructor
  · exact RealMeasurable.add hf.1 hg.1
  · -- Show ∫ |f + g| ≤ ∫ |f| + ∫ |g| < ∞
    have h_le : ∀ x, EReal.abs_fun (f + g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le (f x) (g x))
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have hg_abs := RealAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f + g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n + gg n)
        constructor
        · intro n; exact (RealSimpleFunction.add (hgf_simple n) (hgg_simple n)).abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℝ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x + gg n x) Filter.atTop (nhds (f x + g x)) :=
            Filter.Tendsto.add (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f + g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f + g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem ComplexAbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : ComplexAbsolutelyIntegrable (f + g) := by
  constructor
  · exact ComplexMeasurable.add hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f + g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le (f x) (g x))
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have hg_abs := ComplexAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f + g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n + gg n)
        constructor
        · intro n; exact (ComplexSimpleFunction.add (hgf_simple n) (hgg_simple n)).abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℂ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x + gg n x) Filter.atTop (nhds (f x + g x)) :=
            Filter.Tendsto.add (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f + g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f + g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem RealAbsolutelyIntegrable.sub {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) : RealAbsolutelyIntegrable (f - g) := by
  constructor
  · exact RealMeasurable.sub hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f - g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.sub_apply, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_sub_le (f x) (g x))
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have hg_abs := RealAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n - gg n)
        constructor
        · intro n
          have hsub : RealSimpleFunction (gf n - gg n) := by
            have heq : gf n - gg n = gf n + (-1 : ℝ) • gg n := by
              funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
            rw [heq]
            exact RealSimpleFunction.add (hgf_simple n) ((hgg_simple n).smul (-1))
          exact hsub.abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℝ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x - gg n x) Filter.atTop (nhds (f x - g x)) :=
            Filter.Tendsto.sub (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem ComplexAbsolutelyIntegrable.sub {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : ComplexAbsolutelyIntegrable (f - g) := by
  constructor
  · exact ComplexMeasurable.sub hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f - g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.sub_apply, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_sub_le (f x) (g x))
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have hg_abs := ComplexAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n - gg n)
        constructor
        · intro n
          have hsub : ComplexSimpleFunction (gf n - gg n) := by
            have heq : gf n - gg n = gf n + (-1 : ℂ) • gg n := by
              funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
            rw [heq]
            exact ComplexSimpleFunction.add (hgf_simple n) ((hgg_simple n).smul (-1))
          exact hsub.abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℂ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x - gg n x) Filter.atTop (nhds (f x - g x)) :=
            Filter.Tendsto.sub (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem RealAbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (c:ℝ) : RealAbsolutelyIntegrable (c • f) := by
  constructor
  · -- RealMeasurable (c • f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => c • g n
    constructor
    · intro n; exact (hg_simple n).smul c
    · intro x
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      have hsmul_conv : Filter.Tendsto (fun n => c • g n x) Filter.atTop (nhds (c • f x)) := by
        simp only [smul_eq_mul]
        exact hconv.const_mul c
      simp only [Pi.smul_apply]
      exact hsmul_conv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (c • f)) < ⊤
    have h_eq : ∀ x, EReal.abs_fun (c • f) x = ‖c‖.toEReal * EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
      rw [EReal.coe_mul]
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have h_smul_eq : EReal.abs_fun (c • f) = (fun x => ‖c‖.toEReal * EReal.abs_fun f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖c‖.toEReal * EReal.abs_fun f x) =
                   ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      have h_eq' : (fun x => ‖c‖.toEReal * EReal.abs_fun f x) = (‖c‖.toEReal : EReal) • EReal.abs_fun f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      have h_hom := LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg c)
      exact h_hom
    rw [h_scale]
    by_cases hc : c = 0
    · simp only [hc, norm_zero]
      rw [show (0 : ℝ).toEReal = 0 by rfl, zero_mul]
      exact EReal.coe_lt_top 0
    · have hc_pos : ‖c‖ > 0 := norm_pos_iff.mpr hc
      have h_ne_top : ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨?_, ?_, ?_, ?_⟩
        · left; exact EReal.coe_ne_bot ‖c‖
        · left; exact le_of_lt (EReal.coe_pos.mpr hc_pos)
        · left; exact EReal.coe_ne_top ‖c‖
        · right; exact hf.2.ne_top
      exact Ne.lt_top h_ne_top

theorem ComplexAbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (c:ℂ) : ComplexAbsolutelyIntegrable (c • f) := by
  constructor
  · -- ComplexMeasurable (c • f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => c • g n
    constructor
    · intro n; exact (hg_simple n).smul c
    · intro x
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      have hsmul_conv : Filter.Tendsto (fun n => c • g n x) Filter.atTop (nhds (c • f x)) := by
        simp only [smul_eq_mul]
        exact hconv.const_mul c
      simp only [Pi.smul_apply]
      exact hsmul_conv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (c • f)) < ⊤
    have h_eq : ∀ x, EReal.abs_fun (c • f) x = ‖c‖.toEReal * EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul]
      rw [EReal.coe_mul]
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have h_smul_eq : EReal.abs_fun (c • f) = (fun x => ‖c‖.toEReal * EReal.abs_fun f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖c‖.toEReal * EReal.abs_fun f x) =
                   ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      have h_eq' : (fun x => ‖c‖.toEReal * EReal.abs_fun f x) = (‖c‖.toEReal : EReal) • EReal.abs_fun f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      have h_hom := LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg c)
      exact h_hom
    rw [h_scale]
    by_cases hc : c = 0
    · simp only [hc, norm_zero]
      rw [show (0 : ℝ).toEReal = 0 by rfl, zero_mul]
      exact EReal.coe_lt_top 0
    · have hc_pos : ‖c‖ > 0 := norm_pos_iff.mpr hc
      have h_ne_top : ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨?_, ?_, ?_, ?_⟩
        · left; exact EReal.coe_ne_bot ‖c‖
        · left; exact le_of_lt (EReal.coe_pos.mpr hc_pos)
        · left; exact EReal.coe_ne_top ‖c‖
        · right; exact hf.2.ne_top
      exact Ne.lt_top h_ne_top

theorem RealAbsolutelyIntegrable.of_neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (-f) := by
  have h : -f = (-1 : ℝ) • f := by funext x; simp [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact hf.smul (-1)

theorem ComplexAbsolutelyIntegrable.of_neg {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ComplexAbsolutelyIntegrable (-f) := by
  have h : -f = (-1 : ℂ) • f := by funext x; simp [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact hf.smul (-1)

theorem ComplexAbsolutelyIntegrable.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ComplexAbsolutelyIntegrable (Complex.conj_fun f) := by
  constructor
  · -- ComplexMeasurable (Complex.conj_fun f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => Complex.conj_fun (g n)
    constructor
    · intro n; exact (hg_simple n).conj
    · intro x
      simp only [Complex.conj_fun]
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      exact (RCLike.continuous_conj.tendsto (f x)).comp hconv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (Complex.conj_fun f)) < ⊤
    have h_eq : EReal.abs_fun (Complex.conj_fun f) = EReal.abs_fun f := by
      funext x
      simp only [EReal.abs_fun, Complex.conj_fun, RCLike.norm_conj]
    rw [h_eq]
    exact hf.2

@[ext]
structure PreL1 (d:ℕ) where
  f : EuclideanSpace' d → ℂ
  integrable : ComplexAbsolutelyIntegrable f

noncomputable def PreL1.norm {d:ℕ} {X:Type*} [RCLike X] (f: EuclideanSpace' d → X) := UnsignedLebesgueIntegral (EReal.abs_fun f)

def ComplexAbsolutelyIntegrable.to_PreL1 {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : PreL1 d := ⟨ f, hf ⟩

def PreL1.conj {d:ℕ} (F: PreL1 d) : PreL1 d := ⟨ Complex.conj_fun F.f, F.integrable.conj ⟩

lemma ComplexAbsolutelyIntegrable.zero {d:ℕ} : ComplexAbsolutelyIntegrable (0 : EuclideanSpace' d → ℂ) := by
  constructor
  · -- ComplexMeasurable 0
    use fun _ => 0
    constructor
    · intro n
      use 0, fun _ => 0, fun _ => ∅
      constructor
      · intro i; exact Fin.elim0 i
      · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
    · intro x; exact tendsto_const_nhds
  · -- UnsignedLebesgueIntegral (EReal.abs_fun 0) < ⊤
    have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℂ) = 0 := by
      funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
    rw [h_zero, UnsignedLebesgueIntegral]
    -- Show that 0 is an unsigned simple function
    have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      constructor
      · intro i; exact Fin.elim0 i
      · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    -- The integral of the zero simple function is < ⊤
    -- Key: h_simple.integ ≤ ∑ i, c_i * measure(E_i) where c_i are bounded
    -- For the zero function, each term in any representation contributes 0
    simp only [UnsignedSimpleFunction.integ]
    -- The sum is over Fin (choose ...) which is some natural number
    -- Show it's < ⊤ by showing sum ≤ some finite bound
    apply lt_of_le_of_lt _ (EReal.coe_lt_top (0:ℝ))
    rw [EReal.coe_zero]
    have hcond := h_simple.choose_spec.choose_spec.choose_spec.1
    have hf_eq := h_simple.choose_spec.choose_spec.choose_spec.2
    apply Finset.sum_nonpos
    intro i _
    by_cases hci : h_simple.choose_spec.choose i = 0
    · rw [hci, zero_mul]
    · -- c i > 0, need to show E i is empty
      have hci_pos : h_simple.choose_spec.choose i > 0 := lt_of_le_of_ne (hcond i).2 (Ne.symm hci)
      have hE_empty : h_simple.choose_spec.choose_spec.choose i = ∅ := by
        by_contra hne
        have hne' := Set.nonempty_iff_ne_empty.mpr hne
        obtain ⟨x, hx⟩ := hne'
        have h1 : (0 : EuclideanSpace' d → EReal) x = 0 := rfl
        rw [hf_eq] at h1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
        have h_nonneg : ∀ j, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x ≥ 0 := fun j => by
          apply mul_nonneg (hcond j).2
          simp only [EReal.indicator, Real.EReal_fun]
          by_cases hjx : x ∈ h_simple.choose_spec.choose_spec.choose j
          · simp only [Set.indicator'_of_mem hjx, EReal.coe_one]; norm_num
          · simp only [Set.indicator'_of_notMem hjx, EReal.coe_zero, le_refl]
        have h_all_zero : ∀ j ∈ Finset.univ, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j) |>.mp h1
        have h_term_i_zero := h_all_zero i (Finset.mem_univ i)
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hx, EReal.coe_one, mul_one] at h_term_i_zero
        exact (ne_of_gt hci_pos) h_term_i_zero
      rw [hE_empty, Lebesgue_measure.empty, mul_zero]

-- Helper lemma: the norm of zero is zero
lemma ComplexAbsolutelyIntegrable.norm_zero {d:ℕ} : (ComplexAbsolutelyIntegrable.zero (d:=d)).norm = 0 := by
  simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
  have h_abs_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℂ) = 0 := by
    funext x; simp only [EReal.abs_fun, Pi.zero_apply]; norm_cast
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    constructor
    · intro i; exact Fin.elim0 i
    · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
  calc (UnsignedLebesgueIntegral (EReal.abs_fun 0)).toReal
      = (LowerUnsignedLebesgueIntegral (EReal.abs_fun 0)).toReal := rfl
    _ = (LowerUnsignedLebesgueIntegral 0).toReal := by rw [h_abs_zero]
    _ = h_simple.integ.toReal := by rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    _ = 0 := by
        -- h_simple.integ is a sum over Fin (h_simple.choose) = Fin k for some k
        -- For the zero function, each term is 0
        simp only [UnsignedSimpleFunction.integ]
        have hcond := h_simple.choose_spec.choose_spec.choose_spec.1
        have hf_eq := h_simple.choose_spec.choose_spec.choose_spec.2
        have h_sum_zero : ∑ i, h_simple.choose_spec.choose i * Lebesgue_measure (h_simple.choose_spec.choose_spec.choose i) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          by_cases hci : h_simple.choose_spec.choose i = 0
          · rw [hci, zero_mul]
          · have hci_pos : h_simple.choose_spec.choose i > 0 := lt_of_le_of_ne (hcond i).2 (Ne.symm hci)
            have hE_empty : h_simple.choose_spec.choose_spec.choose i = ∅ := by
              by_contra hne
              have hne' := Set.nonempty_iff_ne_empty.mpr hne
              obtain ⟨x, hx⟩ := hne'
              have h1 : (0 : EuclideanSpace' d → EReal) x = 0 := rfl
              rw [hf_eq] at h1
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
              have h_nonneg : ∀ j, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x ≥ 0 := fun j => by
                apply mul_nonneg (hcond j).2
                simp only [EReal.indicator, Real.EReal_fun]
                by_cases hjx : x ∈ h_simple.choose_spec.choose_spec.choose j
                · simp only [Set.indicator'_of_mem hjx, EReal.coe_one]; norm_num
                · simp only [Set.indicator'_of_notMem hjx, EReal.coe_zero, le_refl]
              have h_all_zero : ∀ j ∈ Finset.univ, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x = 0 :=
                Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j) |>.mp h1
              have h_term_i_zero := h_all_zero i (Finset.mem_univ i)
              simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hx, EReal.coe_one, mul_one] at h_term_i_zero
              exact (ne_of_gt hci_pos) h_term_i_zero
            rw [hE_empty, Lebesgue_measure.empty, mul_zero]
        simp only [h_sum_zero, EReal.toReal_zero]

instance PreL1.inst_AddZeroClass {d:ℕ} : AddZeroClass (PreL1 d) := {
  zero := ⟨ 0, ComplexAbsolutelyIntegrable.zero ⟩
  add F G := ⟨ F.f + G.f, F.integrable.add G.integrable ⟩
  zero_add := fun F => by
    apply PreL1.ext
    funext x
    -- Goal: (0 + F).f x = F.f x
    -- (0 + F).f = (⟨0, _⟩ + F).f = (0 : EuclideanSpace' d → ℂ) + F.f
    -- So goal is: (0 + F.f) x = F.f x, i.e., 0 x + F.f x = F.f x
    show (0 : EuclideanSpace' d → ℂ) x + F.f x = F.f x
    simp only [Pi.zero_apply, zero_add]
  add_zero := fun F => by
    apply PreL1.ext
    funext x
    show F.f x + (0 : EuclideanSpace' d → ℂ) x = F.f x
    simp only [Pi.zero_apply, add_zero]
}

instance PreL1.inst_addCommMonoid {d:ℕ} : AddCommMonoid (PreL1 d) := {
  add_assoc := fun F G H => by
    apply PreL1.ext
    funext x
    show (F.f + G.f) x + H.f x = F.f x + (G.f + H.f) x
    simp only [Pi.add_apply, add_assoc]
  add_comm := fun F G => by
    apply PreL1.ext
    funext x
    show F.f x + G.f x = G.f x + F.f x
    ring
  nsmul := nsmulRec
}

instance PreL1.inst_Neg {d:ℕ} : Neg (PreL1 d) := {
  neg F := ⟨ -F.f, F.integrable.of_neg ⟩
}

instance PreL1.inst_Sub {d:ℕ} : Sub (PreL1 d) := {
  sub F G := ⟨ F.f - G.f, F.integrable.sub G.integrable ⟩
}

instance PreL1.inst_module {d:ℕ} : Module ℂ (PreL1 d) := {
  smul c F := ⟨ c • F.f, F.integrable.smul c ⟩
  zero_smul := fun F => by
    apply PreL1.ext
    funext x
    show (0 : ℂ) • F.f x = (0 : EuclideanSpace' d → ℂ) x
    simp only [zero_smul, Pi.zero_apply]
  smul_zero := fun c => by
    apply PreL1.ext
    funext x
    show c • (0 : EuclideanSpace' d → ℂ) x = (0 : EuclideanSpace' d → ℂ) x
    simp only [Pi.zero_apply, smul_zero]
  one_smul := fun F => by
    apply PreL1.ext
    funext x
    show (1 : ℂ) • F.f x = F.f x
    simp only [one_smul]
  mul_smul := fun a b F => by
    apply PreL1.ext
    funext x
    show (a * b) • F.f x = a • (b • F.f x)
    simp only [mul_smul]
  smul_add := fun c F G => by
    apply PreL1.ext
    funext x
    show c • (F.f + G.f) x = (c • F.f + c • G.f) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_add]
  add_smul := fun a b F => by
    apply PreL1.ext
    funext x
    show (a + b) • F.f x = (a • F.f + b • F.f) x
    simp only [Pi.add_apply, Pi.smul_apply, add_smul]
}

-- Helper: integral of the zero simple function is zero
lemma UnsignedSimpleFunction.integ_zero {d:ℕ} :
    let h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
    h_simple.integ = 0 := by
  -- Use integral_eq with k=0 to compute the integral
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  have heq : (0 : EuclideanSpace' d → EReal) = ∑ i : Fin 0, ((Fin.elim0 i : EReal) • (EReal.indicator (Fin.elim0 i : Set (EuclideanSpace' d)))) := by
    funext x; simp [Finset.univ_eq_empty]
  have hmes : ∀ i : Fin 0, LebesgueMeasurable (Fin.elim0 i : Set (EuclideanSpace' d)) := fun i => Fin.elim0 i
  have hnonneg : ∀ i : Fin 0, (Fin.elim0 i : EReal) ≥ 0 := fun i => Fin.elim0 i
  have h_integ := UnsignedSimpleFunction.integral_eq h_simple hmes hnonneg heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at h_integ
  exact h_integ

-- Helper: integral of unsigned measurable function is nonnegative
lemma UnsignedLebesgueIntegral.nonneg {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
    0 ≤ UnsignedLebesgueIntegral f := by
  simp only [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
  apply le_csSup_of_le ⟨⊤, fun _ _ => le_top⟩ _ (le_refl 0)
  use 0
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  use h_simple; intro x
  constructor
  · simp only [Pi.zero_apply]; exact hf.1 x
  · have : h_simple.integ = 0 := UnsignedSimpleFunction.integ_zero
    rw [this]

noncomputable instance PreL1.inst_seminormedAddCommGroup {d:ℕ} : SeminormedAddCommGroup (PreL1 d) := {
  norm F := F.integrable.norm
  neg F := ⟨ -F.f, F.integrable.of_neg ⟩
  zsmul := zsmulRec
  neg_add_cancel := fun F => by
    apply PreL1.ext
    funext x
    show (-F.f + F.f) x = (0 : EuclideanSpace' d → ℂ) x
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, neg_add_cancel]
  dist_self := fun F => by
    -- Goal: (F - F).integrable.norm = 0
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    have h_f_eq : (F - F).f = 0 := by
      funext x
      show F.f x - F.f x = 0
      ring
    have h_abs_zero : EReal.abs_fun (F - F).f = 0 := by
      rw [h_f_eq]; funext x; simp only [EReal.abs_fun, Pi.zero_apply]; norm_cast
    rw [h_abs_zero]
    -- Now need to show UnsignedLebesgueIntegral 0 = 0
    -- Use that EReal.abs_fun 0 = 0 to relate to norm_zero
    have h_abs_zero' : EReal.abs_fun (0 : EuclideanSpace' d → ℂ) = 0 := by
      funext x; simp only [EReal.abs_fun, Pi.zero_apply]; norm_cast
    calc (UnsignedLebesgueIntegral 0).toReal
        = (UnsignedLebesgueIntegral (EReal.abs_fun 0)).toReal := by rw [h_abs_zero']
      _ = ComplexAbsolutelyIntegrable.zero.norm := by rfl
      _ = 0 := ComplexAbsolutelyIntegrable.norm_zero
  dist_comm := fun F G => by
    -- Goal: (F - G).integrable.norm = (G - F).integrable.norm
    -- Key: ‖(G - F).f x‖ = ‖-(F - G).f x‖ = ‖(F - G).f x‖
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    congr 1
    -- Goal: UnsignedLebesgueIntegral (EReal.abs_fun (F - G).f) = UnsignedLebesgueIntegral (EReal.abs_fun (G - F).f)
    congr 1
    -- Goal: EReal.abs_fun (F - G).f = EReal.abs_fun (G - F).f
    funext x
    simp only [EReal.abs_fun]
    congr 1
    -- Goal: ‖(F - G).f x‖ = ‖(G - F).f x‖
    show ‖F.f x - G.f x‖ = ‖G.f x - F.f x‖
    rw [norm_sub_rev]
  dist_triangle := fun F G H => by
    -- Goal: (F - H).integrable.norm ≤ (F - G).integrable.norm + (G - H).integrable.norm
    -- Key: (F - H).f x = (F - G).f x + (G - H).f x
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    have h_eq : (F - H).f = (F - G).f + (G - H).f := by
      funext x
      show F.f x - H.f x = (F.f x - G.f x) + (G.f x - H.f x)
      ring
    -- Now use triangle inequality structure from ComplexAbsolutelyIntegrable.add
    have h_le : ∀ x, EReal.abs_fun (F - H).f x ≤ (EReal.abs_fun (F - G).f + EReal.abs_fun (G - H).f) x := fun x => by
      rw [h_eq]
      simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le ((F - G).f x) ((G - H).f x))
    have hfg_abs := (F - G).integrable.abs
    have hgh_abs := (G - H).integrable.abs
    have hfh_abs := (F - H).integrable.abs
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (F - H).f) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun (F - G).f + EReal.abs_fun (G - H).f) := by
      apply LowerUnsignedLebesgueIntegral.mono hfh_abs.1 (UnsignedMeasurable.add hfg_abs.1 hgh_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (F - G).f + EReal.abs_fun (G - H).f) =
                 UnsignedLebesgueIntegral (EReal.abs_fun (F - G).f) + UnsignedLebesgueIntegral (EReal.abs_fun (G - H).f) := by
      apply LowerUnsignedLebesgueIntegral.add hfg_abs.1 hgh_abs.1 (UnsignedMeasurable.add hfg_abs.1 hgh_abs.1)
    have h_ineq : UnsignedLebesgueIntegral (EReal.abs_fun (F - H).f) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun (F - G).f) + UnsignedLebesgueIntegral (EReal.abs_fun (G - H).f) := by
      rw [← h_add]; exact h_mono
    -- Now convert EReal inequality to Real inequality
    have h_finite_fh : UnsignedLebesgueIntegral (EReal.abs_fun (F - H).f) < ⊤ := hfh_abs.2
    have h_finite_fg : UnsignedLebesgueIntegral (EReal.abs_fun (F - G).f) < ⊤ := hfg_abs.2
    have h_finite_gh : UnsignedLebesgueIntegral (EReal.abs_fun (G - H).f) < ⊤ := hgh_abs.2
    -- Nonnegativity: integral of unsigned measurable function is ≥ 0, hence ≠ ⊥
    -- Since EReal.abs_fun values ≥ 0, integral is sup of nonneg simple integrals
    have h_nonneg_fh : UnsignedLebesgueIntegral (EReal.abs_fun (F - H).f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hfh_abs.1))
    have h_nonneg_fg : UnsignedLebesgueIntegral (EReal.abs_fun (F - G).f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hfg_abs.1))
    have h_nonneg_gh : UnsignedLebesgueIntegral (EReal.abs_fun (G - H).f) ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hgh_abs.1))
    have h_sum_ne_top : UnsignedLebesgueIntegral (EReal.abs_fun (F - G).f) + UnsignedLebesgueIntegral (EReal.abs_fun (G - H).f) ≠ ⊤ :=
      (EReal.add_lt_top h_finite_fg.ne_top h_finite_gh.ne_top).ne_top
    rw [← EReal.toReal_add h_finite_fg.ne_top h_nonneg_fg h_finite_gh.ne_top h_nonneg_gh]
    exact EReal.toReal_le_toReal h_ineq h_nonneg_fh h_sum_ne_top
}

instance PreL1.inst_normedSpace {d:ℕ} : NormedSpace ℂ (PreL1 d) := {
  norm_smul_le := fun a F => by
    -- Goal: ‖a • F‖ ≤ ‖a‖ * ‖F‖
    -- ‖F‖ = F.integrable.norm for PreL1
    show (a • F).integrable.norm ≤ ‖a‖ * F.integrable.norm
    simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
    -- Key fact: EReal.abs_fun (a • F.f) x = ‖a‖ * EReal.abs_fun F.f x
    have h_eq : ∀ x, EReal.abs_fun (a • F).f x = ‖a‖.toEReal * EReal.abs_fun F.f x := fun x => by
      simp only [EReal.abs_fun]
      -- Show ‖(a • F).f x‖ = ‖a‖ * ‖F.f x‖
      show (‖(a • F).f x‖ : EReal) = ‖a‖.toEReal * ‖F.f x‖.toEReal
      rw [show (a • F).f x = a * F.f x from rfl, norm_mul, EReal.coe_mul]
    have hf_abs := ComplexAbsolutelyIntegrable.abs F.f F.integrable
    have h_smul_eq : EReal.abs_fun (a • F).f = (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) =
                   ‖a‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun F.f) := by
      have h_eq' : (fun x => ‖a‖.toEReal * EReal.abs_fun F.f x) = (‖a‖.toEReal : EReal) • EReal.abs_fun F.f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      exact LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg a)
    rw [h_scale]
    -- Now we have: (‖a‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun F.f)).toReal ≤ ‖a‖ * (UnsignedLebesgueIntegral (EReal.abs_fun F.f)).toReal
    -- We actually have equality
    have h_finite : UnsignedLebesgueIntegral (EReal.abs_fun F.f) < ⊤ := hf_abs.2
    have h_nonneg : 0 ≤ UnsignedLebesgueIntegral (EReal.abs_fun F.f) := UnsignedLebesgueIntegral.nonneg hf_abs.1
    have h_ne_bot : UnsignedLebesgueIntegral (EReal.abs_fun F.f) ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero h_nonneg)
    rw [EReal.toReal_mul]
    simp only [EReal.toReal_coe, le_refl]
}

theorem PreL1.dist_eq {d:ℕ} (F G: PreL1 d) : dist F G = ‖F-G‖ := rfl

noncomputable abbrev L1 (d:ℕ) := SeparationQuotient (PreL1 d)

@[coe]
def PreL1.toL1 {d:ℕ} (F: PreL1 d) : L1 d := SeparationQuotient.mk F

instance PreL1.inst_coeL1 {d:ℕ} : Coe (PreL1 d) (L1 d) := ⟨ PreL1.toL1 ⟩

def ComplexAbsolutelyIntegrable.toL1 {d:ℕ} {f:EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : L1 d := SeparationQuotient.mk hf.to_PreL1

theorem L1.dist_eq {d:ℕ} (f g: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : dist hf.toL1 hg.toL1 = (hf.sub hg).norm := rfl

theorem L1.dist_eq_zero {d:ℕ} (f g: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : dist hf.toL1 hg.toL1 = 0 ↔ AlmostEverywhereEqual f g := by
  rw [L1.dist_eq]
  simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
  rw [EReal.toReal_eq_zero_iff]
  -- Eliminate ⊤ and ⊥ cases
  have h_finite : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) < ⊤ := (hf.sub hg).2
  have h_nonneg : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≥ 0 :=
    UnsignedLebesgueIntegral.nonneg (hf.sub hg).abs.1
  have h_ne_top : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≠ ⊤ := ne_of_lt h_finite
  have h_ne_bot : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≠ ⊥ := by
    intro h_eq_bot
    rw [h_eq_bot] at h_nonneg
    exact not_le.mpr EReal.bot_lt_zero h_nonneg
  simp only [h_ne_top, h_ne_bot, or_false]
  -- Now goal: UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) = 0 ↔ AlmostEverywhereEqual f g
  have h_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := (hf.sub hg).abs.1
  rw [show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) = h_meas.integ from rfl]
  rw [UnsignedLebesgueIntegral.eq_zero_aeZero h_meas]
  -- Goal: AlmostAlways (fun x ↦ EReal.abs_fun (f - g) x = 0) ↔ AlmostEverywhereEqual f g
  unfold AlmostEverywhereEqual AlmostAlways
  -- Goal: IsNull {x | ¬EReal.abs_fun (f - g) x = 0} ↔ IsNull {x | ¬f x = g x}
  -- Show the sets are equal
  have h_sets_eq : {x | ¬EReal.abs_fun (f - g) x = 0} = {x | ¬f x = g x} := by
    ext x
    simp only [Set.mem_setOf_eq, EReal.abs_fun]
    -- Goal: ¬‖(f - g) x‖.toEReal = 0 ↔ ¬f x = g x
    constructor
    · intro h hfg
      apply h
      simp only [Pi.sub_apply, hfg, sub_self, norm_zero, EReal.coe_zero]
    · intro h heq
      apply h
      have h_norm_zero : ‖(f - g) x‖ = 0 := by
        have : (‖(f - g) x‖ : EReal) = 0 := heq
        exact EReal.coe_eq_zero.mp this
      exact sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  rw [h_sets_eq]

/-- Exercise 1.3.19 (Integration is linear) -/
noncomputable def L1.integ {d:ℕ} : L1 d →ₗ[ℂ] ℂ := {
  toFun := Quotient.lift (fun F ↦ F.integrable.integ) (by sorry)
  map_smul' := by sorry
  map_add' := by sorry
}

noncomputable def L1.conj {d:ℕ} : L1 d → L1 d := Quotient.lift (fun F ↦ (F.conj : L1 d)) (by sorry)

theorem L1.integ_conj {d:ℕ} (F: L1 d) : L1.integ (L1.conj F) = starRingEnd ℂ (L1.integ F) := by sorry

/-- Exercise 1.3.20 (Translation invariance)-/
theorem RealAbsolutelyIntegrable.trans {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (a: EuclideanSpace' d) : RealAbsolutelyIntegrable (fun x ↦ f (x + a)) := by sorry

theorem RealAbsolutelyIntegrable.integ_trans {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (a: EuclideanSpace' d) : (hf.trans a).integ = hf.integ  := by sorry

theorem ComplexAbsolutelyIntegrable.trans {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (a: EuclideanSpace' d) : ComplexAbsolutelyIntegrable (fun x ↦ f (x + a)) := by sorry

theorem ComplexAbsolutelyIntegrable.integ_trans {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (a: EuclideanSpace' d) : (hf.trans a).integ = hf.integ  := by sorry

/-- Exercise 1.3.20 (Linear change of variables)-/
theorem RealAbsolutelyIntegrable.comp_linear {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    RealAbsolutelyIntegrable (fun x ↦ f (A x)) := by sorry

theorem RealAbsolutelyIntegrable.integ_comp_linear {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    (hf.comp_linear hA).integ = |A.det|⁻¹ * hf.integ := by sorry

theorem ComplexAbsolutelyIntegrable.comp_linear {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    ComplexAbsolutelyIntegrable (fun x ↦ f (A x)) := by sorry

theorem ComplexAbsolutelyIntegrable.integ_comp_linear {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    (hf.comp_linear hA).integ = |A.det|⁻¹ * hf.integ := by sorry

/-- Exercise 1.3.20 (Compatibility with the Riemann integral)-/
theorem RiemannIntegrableOn.realAbsolutelyIntegrable {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) : RealAbsolutelyIntegrable ((fun x ↦ (f x) * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real) := by sorry

theorem RiemannIntegral.eq_integ {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) :
    riemannIntegral f I  = hf.realAbsolutelyIntegrable.integ := by sorry

/-- Exercise 1.3.21 (Absolute summability is a special case of absolute integrability)-/
theorem AbsolutelySummable.realAbsolutelyIntegrable_iff {a: ℤ → ℝ} : ∑' n, |a n|.toEReal < ⊤ ↔ RealAbsolutelyIntegrable (fun x ↦ a ⌊EuclideanSpace'.equiv_Real x⌋) := by sorry

theorem AbsolutelySummable.complexAbsolutelyIntegrable_iff {a: ℤ → ℂ} : ∑' n, ‖a n‖.toEReal < ⊤ ↔ ComplexAbsolutelyIntegrable (fun x ↦ a ⌊EuclideanSpace'.equiv_Real x⌋) := by sorry

def ComplexAbsolutelyIntegrableOn {d:ℕ} (f: EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)) : Prop := ComplexAbsolutelyIntegrable (f * Complex.indicator E)

noncomputable def ComplexAbsolutelyIntegrableOn.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} {E: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) : ℂ :=
  ComplexAbsolutelyIntegrable.integ hf

/-- Exercise 1.3.22 -/
theorem ComplexAbsolutelyIntegrableOn.glue {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hdisj: Disjoint E F) (hf: ComplexAbsolutelyIntegrableOn f (E ∪ F)) : ∃ hE : ComplexAbsolutelyIntegrableOn f E, ∃ hF: ComplexAbsolutelyIntegrableOn f F, hf.integ = hE.integ + hF.integ := by sorry

def ComplexAbsolutelyIntegrableOn.restrict {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) (hF: LebesgueMeasurable F): ComplexAbsolutelyIntegrableOn (f * Complex.indicator F) E := by sorry

def ComplexAbsolutelyIntegrableOn.mono {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hsub: F ⊆ E): ComplexAbsolutelyIntegrableOn f F := by sorry

theorem ComplexAbsolutelyIntegrableOn.integ_restrict {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hsub: F ⊆ E) (hf: ComplexAbsolutelyIntegrableOn f E) : (hf.mono hE hF hsub).integ = (hf.restrict hF).integ:= by sorry

/-- Lemma 1.3.19 (Triangle inequality) -/

-- Helper: |∫f| ≤ ∫|f| for real absolutely integrable functions
lemma RealAbsolutelyIntegrable.abs_integ_le {d:ℕ} {f: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) : |hf.integ| ≤ hf.abs.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  have h_pos_nonneg := EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.pos.1)
  have h_neg_nonneg := EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.neg.1)
  -- |a - b| ≤ a + b when a, b ≥ 0
  have h_abs_ineq : |(UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal -
                     (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal| ≤
                    (UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal +
                    (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := by
    rw [abs_le]; constructor <;> linarith
  -- pos_fun + neg_fun = abs_fun pointwise
  have h_eq_pointwise : ∀ x, EReal.pos_fun f x + EReal.neg_fun f x = EReal.abs_fun f x := fun x => by
    simp only [EReal.pos_fun, EReal.neg_fun, EReal.abs_fun, ← EReal.coe_add]
    congr 1; rw [max_zero_add_max_neg_zero_eq_abs_self, Real.norm_eq_abs]
  have h_sum : UnsignedLebesgueIntegral (EReal.pos_fun f) + UnsignedLebesgueIntegral (EReal.neg_fun f) =
               UnsignedLebesgueIntegral (EReal.abs_fun f) := by
    have h_eq_fun : EReal.pos_fun f + EReal.neg_fun f = EReal.abs_fun f := funext h_eq_pointwise
    rw [← h_eq_fun]; symm
    apply LowerUnsignedLebesgueIntegral.add hf.pos.1 hf.neg.1
    rw [h_eq_fun]; exact hf.abs.1
  have h_pos_ne_top := hf.pos.2.ne_top
  have h_neg_ne_top := hf.neg.2.ne_top
  have h_pos_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.pos.1))
  have h_neg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.neg.1))
  calc |(UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal -
        (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal|
      ≤ (UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal +
        (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := h_abs_ineq
    _ = (UnsignedLebesgueIntegral (EReal.pos_fun f) + UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := by
        rw [EReal.toReal_add h_pos_ne_top h_pos_ne_bot h_neg_ne_top h_neg_ne_bot]
    _ = (UnsignedLebesgueIntegral (EReal.abs_fun f)).toReal := by rw [h_sum]

-- Helper: ∫|Re(f)| ≤ ∫|f| for complex absolutely integrable functions
lemma ComplexAbsolutelyIntegrable.re_abs_integ_le {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : hf.re.abs.integ ≤ hf.abs.integ := by
  simp only [UnsignedAbsolutelyIntegrable.integ]
  have h_le_pointwise : ∀ x, EReal.abs_fun (Complex.re_fun f) x ≤ EReal.abs_fun f x := fun x => by
    simp only [EReal.abs_fun, Complex.re_fun, EReal.coe_le_coe_iff, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm (f x)
  have h_mono := LowerUnsignedLebesgueIntegral.mono hf.re.abs.1 hf.abs.1 (AlmostAlways.ofAlways h_le_pointwise)
  have h_re_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.re.abs.1))
  exact EReal.toReal_le_toReal h_mono h_re_ne_bot hf.abs.2.ne_top

-- Key identity for pos/neg parts under addition
-- (f+g)⁺ + f⁻ + g⁻ = f⁺ + g⁺ + (f+g)⁻
lemma Real.pos_neg_add_identity (a b : ℝ) :
    max (a + b) 0 + max (-a) 0 + max (-b) 0 =
    max a 0 + max b 0 + max (-(a + b)) 0 := by
  rcases le_or_gt a 0 with ha | ha <;> rcases le_or_gt b 0 with hb | hb
  · have hab : a + b ≤ 0 := add_nonpos ha hb
    rw [max_eq_right hab, max_eq_right ha, max_eq_right hb,
        max_eq_left (neg_nonneg.mpr ha), max_eq_left (neg_nonneg.mpr hb),
        max_eq_left (neg_nonneg.mpr hab)]
    ring
  · rcases le_or_gt (a + b) 0 with hab | hab
    · rw [max_eq_right hab, max_eq_right ha, max_eq_left (le_of_lt hb),
          max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
          max_eq_left (neg_nonneg.mpr hab)]
      ring
    · rw [max_eq_left (le_of_lt hab), max_eq_right ha, max_eq_left (le_of_lt hb),
          max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
          max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
      ring
  · rcases le_or_gt (a + b) 0 with hab | hab
    · rw [max_eq_right hab, max_eq_left (le_of_lt ha), max_eq_right hb,
          max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_left (neg_nonneg.mpr hb),
          max_eq_left (neg_nonneg.mpr hab)]
      ring
    · rw [max_eq_left (le_of_lt hab), max_eq_left (le_of_lt ha), max_eq_right hb,
          max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_left (neg_nonneg.mpr hb),
          max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
      ring
  · have hab : 0 < a + b := add_pos ha hb
    rw [max_eq_left (le_of_lt hab), max_eq_left (le_of_lt ha), max_eq_left (le_of_lt hb),
        max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
        max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
    ring

lemma EReal.pos_neg_add_identity {X: Type*} (f g : X → ℝ) :
    EReal.pos_fun (f + g) + EReal.neg_fun f + EReal.neg_fun g =
    EReal.pos_fun f + EReal.pos_fun g + EReal.neg_fun (f + g) := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.add_apply]
  have h := Real.pos_neg_add_identity (f x) (g x)
  simp only [← EReal.coe_add, h]

-- Key lemmas about pos_fun and neg_fun under scaling
lemma EReal.pos_fun_smul_nonneg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: 0 ≤ c) :
    EReal.pos_fun (c • f) = (c : EReal) • EReal.pos_fun f := by
  funext x
  simp only [EReal.pos_fun, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← mul_zero c, (mul_max_of_nonneg (f x) 0 hc).symm, mul_zero]

lemma EReal.neg_fun_smul_nonneg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: 0 ≤ c) :
    EReal.neg_fun (c • f) = (c : EReal) • EReal.neg_fun f := by
  funext x
  simp only [EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [show -(c * f x) = c * (-f x) from by ring]
  rw [← mul_zero c, (mul_max_of_nonneg (-f x) 0 hc).symm, mul_zero]

lemma EReal.pos_fun_smul_neg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: c < 0) :
    EReal.pos_fun (c • f) = ((-c) : EReal) • EReal.neg_fun f := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
  congr 1
  rw [show c * f x = (-c) * (-f x) from by ring]
  rw [← mul_zero (-c), (mul_max_of_nonneg (-f x) 0 hnc).symm, mul_zero]

lemma EReal.neg_fun_smul_neg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: c < 0) :
    EReal.neg_fun (c • f) = ((-c) : EReal) • EReal.pos_fun f := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
  congr 1
  rw [show -(c * f x) = (-c) * f x from by ring]
  rw [← mul_zero (-c), (mul_max_of_nonneg (f x) 0 hnc).symm, mul_zero]

-- Helper: scalar multiplication linearity for real integral
lemma RealAbsolutelyIntegrable.integ_smul' {d:ℕ} {f: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (c: ℝ) : (hf.smul c).integ = c * hf.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  by_cases hc : 0 ≤ c
  · -- Case c ≥ 0
    have h_pos : EReal.pos_fun (c • f) = (c : EReal) • EReal.pos_fun f := EReal.pos_fun_smul_nonneg f c hc
    have h_neg : EReal.neg_fun (c • f) = (c : EReal) • EReal.neg_fun f := EReal.neg_fun_smul_nonneg f c hc
    have h_pos_scale : UnsignedLebesgueIntegral (EReal.pos_fun (c • f)) = c * UnsignedLebesgueIntegral (EReal.pos_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_pos]
      exact LowerUnsignedLebesgueIntegral.hom hf.pos.1 hc
    have h_neg_scale : UnsignedLebesgueIntegral (EReal.neg_fun (c • f)) = c * UnsignedLebesgueIntegral (EReal.neg_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_neg]
      exact LowerUnsignedLebesgueIntegral.hom hf.neg.1 hc
    rw [h_pos_scale, h_neg_scale, EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_coe]
    ring
  · -- Case c < 0
    push_neg at hc
    have h_pos : EReal.pos_fun (c • f) = ((-c) : EReal) • EReal.neg_fun f := EReal.pos_fun_smul_neg f c hc
    have h_neg : EReal.neg_fun (c • f) = ((-c) : EReal) • EReal.pos_fun f := EReal.neg_fun_smul_neg f c hc
    have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
    have h_pos_scale : UnsignedLebesgueIntegral (EReal.pos_fun (c • f)) = (-c) * UnsignedLebesgueIntegral (EReal.neg_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_pos]
      exact LowerUnsignedLebesgueIntegral.hom hf.neg.1 hnc
    have h_neg_scale : UnsignedLebesgueIntegral (EReal.neg_fun (c • f)) = (-c) * UnsignedLebesgueIntegral (EReal.pos_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_neg]
      exact LowerUnsignedLebesgueIntegral.hom hf.pos.1 hnc
    rw [h_pos_scale, h_neg_scale]
    simp only [EReal.toReal_mul, EReal.toReal_neg, EReal.toReal_coe]
    ring

-- Helper: addition linearity for real integral
lemma RealAbsolutelyIntegrable.integ_add' {d:ℕ} {f g: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) :
    (hf.add hg).integ = hf.integ + hg.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]

  have h_id := EReal.pos_neg_add_identity f g

  -- Measurability
  have hpos_fg := (hf.add hg).pos.1
  have hneg_fg := (hf.add hg).neg.1
  have hpos_f := hf.pos.1
  have hneg_f := hf.neg.1
  have hpos_g := hg.pos.1
  have hneg_g := hg.neg.1

  -- Finiteness: ne_top
  have hpos_fg_ne_top := (hf.add hg).pos.2.ne_top
  have hneg_fg_ne_top := (hf.add hg).neg.2.ne_top
  have hpos_f_ne_top := hf.pos.2.ne_top
  have hneg_f_ne_top := hf.neg.2.ne_top
  have hpos_g_ne_top := hg.pos.2.ne_top
  have hneg_g_ne_top := hg.neg.2.ne_top

  -- Nonnegativity → not bot
  have hpos_fg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_fg))
  have hneg_fg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_fg))
  have hpos_f_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_f))
  have hneg_f_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_f))
  have hpos_g_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_g))
  have hneg_g_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_g))

  simp only [UnsignedLebesgueIntegral] at *

  -- Apply integral additivity to the pointwise identity
  have h_lhs_add1 := LowerUnsignedLebesgueIntegral.add hpos_fg hneg_f
                       (UnsignedMeasurable.add hpos_fg hneg_f)
  have h_lhs_add2 := LowerUnsignedLebesgueIntegral.add
                       (UnsignedMeasurable.add hpos_fg hneg_f) hneg_g
                       (UnsignedMeasurable.add (UnsignedMeasurable.add hpos_fg hneg_f) hneg_g)
  have h_rhs_add1 := LowerUnsignedLebesgueIntegral.add hpos_f hpos_g
                       (UnsignedMeasurable.add hpos_f hpos_g)
  have h_rhs_add2 := LowerUnsignedLebesgueIntegral.add
                       (UnsignedMeasurable.add hpos_f hpos_g) hneg_fg
                       (UnsignedMeasurable.add (UnsignedMeasurable.add hpos_f hpos_g) hneg_fg)

  -- From the identity, integrals are equal
  have h_integ_eq : LowerUnsignedLebesgueIntegral (EReal.pos_fun (f + g)) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun f) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun g) =
                    LowerUnsignedLebesgueIntegral (EReal.pos_fun f) +
                    LowerUnsignedLebesgueIntegral (EReal.pos_fun g) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun (f + g)) := by
    rw [← h_lhs_add1, ← h_lhs_add2, ← h_rhs_add1, ← h_rhs_add2, h_id]

  -- Convert to Real arithmetic
  have h1 : (LowerUnsignedLebesgueIntegral (EReal.pos_fun (f + g)) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun f) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun g)).toReal =
            (LowerUnsignedLebesgueIntegral (EReal.pos_fun f) +
             LowerUnsignedLebesgueIntegral (EReal.pos_fun g) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun (f + g))).toReal := by
    rw [h_integ_eq]

  -- Expand toReal_add using the finiteness conditions
  have hsum1_ne_top := EReal.add_ne_top hpos_fg_ne_top hneg_f_ne_top
  have hsum1_ne_bot := EReal.add_ne_bot_iff.mpr ⟨hpos_fg_ne_bot, hneg_f_ne_bot⟩
  have hsum2_ne_top := EReal.add_ne_top hpos_f_ne_top hpos_g_ne_top
  have hsum2_ne_bot := EReal.add_ne_bot_iff.mpr ⟨hpos_f_ne_bot, hpos_g_ne_bot⟩

  rw [EReal.toReal_add hsum1_ne_top hsum1_ne_bot hneg_g_ne_top hneg_g_ne_bot,
      EReal.toReal_add hpos_fg_ne_top hpos_fg_ne_bot hneg_f_ne_top hneg_f_ne_bot] at h1
  rw [EReal.toReal_add hsum2_ne_top hsum2_ne_bot hneg_fg_ne_top hneg_fg_ne_bot,
      EReal.toReal_add hpos_f_ne_top hpos_f_ne_bot hpos_g_ne_top hpos_g_ne_bot] at h1

  linarith

-- Helper: subtraction linearity for real integral
lemma RealAbsolutelyIntegrable.integ_sub' {d:ℕ} {f g: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) :
    (hf.sub hg).integ = hf.integ - hg.integ := by
  -- f - g = f + (-1) • g pointwise
  have heq : f - g = f + (-1 : ℝ) • g := by funext x; simp [sub_eq_add_neg]
  -- The integral depends only on function values
  have h_integ_eq : (hf.sub hg).integ = (hf.add (hg.smul (-1 : ℝ))).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, heq]
  rw [h_integ_eq, RealAbsolutelyIntegrable.integ_add', RealAbsolutelyIntegrable.integ_smul']
  ring

-- Helper: scalar multiplication linearity for complex integral
lemma ComplexAbsolutelyIntegrable.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) (c: ℂ) : (hf.smul c).integ = c * hf.integ := by
  -- Expand the definition of complex integral
  simp only [ComplexAbsolutelyIntegrable.integ]
  -- Goal: (hf.smul c).re.integ + I * (hf.smul c).im.integ =
  --       c * (hf.re.integ + I * hf.im.integ)

  -- The function equalities (pointwise)
  have h_re_fun : Complex.re_fun (c • f) = c.re • Complex.re_fun f - c.im • Complex.im_fun f := by
    funext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.mul_re]
  have h_im_fun : Complex.im_fun (c • f) = c.re • Complex.im_fun f + c.im • Complex.re_fun f := by
    funext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.mul_im]

  -- Build the decomposed integrability proofs
  have h_re_decomp : RealAbsolutelyIntegrable (c.re • Complex.re_fun f - c.im • Complex.im_fun f) :=
    (hf.re.smul c.re).sub (hf.im.smul c.im)
  have h_im_decomp : RealAbsolutelyIntegrable (c.re • Complex.im_fun f + c.im • Complex.re_fun f) :=
    (hf.im.smul c.re).add (hf.re.smul c.im)

  -- The integrals of (hf.smul c).re and the decomposed form are equal
  -- because they're integrability proofs for the same function
  have h_re_integ : (hf.smul c).re.integ = h_re_decomp.integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_re_fun]
  have h_im_integ : (hf.smul c).im.integ = h_im_decomp.integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_im_fun]

  -- Use linearity of real integral for the decomposed forms
  have h_re_linear : h_re_decomp.integ = c.re * hf.re.integ - c.im * hf.im.integ := by
    rw [show h_re_decomp = (hf.re.smul c.re).sub (hf.im.smul c.im) from rfl]
    rw [RealAbsolutelyIntegrable.integ_sub', RealAbsolutelyIntegrable.integ_smul',
        RealAbsolutelyIntegrable.integ_smul']
  have h_im_linear : h_im_decomp.integ = c.re * hf.im.integ + c.im * hf.re.integ := by
    rw [show h_im_decomp = (hf.im.smul c.re).add (hf.re.smul c.im) from rfl]
    rw [RealAbsolutelyIntegrable.integ_add', RealAbsolutelyIntegrable.integ_smul',
        RealAbsolutelyIntegrable.integ_smul']

  rw [h_re_integ, h_im_integ, h_re_linear, h_im_linear]
  -- Need to simplify the imaginary part of (re_integ + I * im_integ)
  have h_integ_im : (↑hf.re.integ + Complex.I * ↑hf.im.integ : ℂ).im = hf.im.integ := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im]; ring
  have h_integ_re : (↑hf.re.integ + Complex.I * ↑hf.im.integ : ℂ).re = hf.re.integ := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im]; ring
  -- Now just complex algebra - compare re and im parts
  apply Complex.ext
  · -- Real parts
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im, mul_zero, sub_zero, h_integ_im, h_integ_re]
    ring
  · -- Imaginary parts
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im, mul_zero, zero_add, h_integ_im, h_integ_re]
    ring

-- Helper: |u*f| integral equals |f| integral when |u| = 1
lemma ComplexAbsolutelyIntegrable.abs_smul_unit {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) (c: ℂ) (hc: ‖c‖ = 1) :
    (hf.smul c).abs.integ = hf.abs.integ := by
  simp only [UnsignedAbsolutelyIntegrable.integ]
  congr 1; congr 1
  funext x
  simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]

-- Helper: integ.re = re.integ for complex absolutely integrable functions
lemma ComplexAbsolutelyIntegrable.integ_re_eq_re_integ {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : hf.integ.re = hf.re.integ := by
  simp only [ComplexAbsolutelyIntegrable.integ, Complex.add_re, Complex.mul_re,
             Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

-- Main theorem: ‖∫f‖ ≤ ∫|f| for complex absolutely integrable functions
theorem ComplexAbsolutelyIntegrable.abs_le {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : ‖hf.integ‖ ≤ hf.abs.integ := by
  by_cases h : hf.integ = 0
  · -- Case: ∫f = 0
    simp [h, UnsignedAbsolutelyIntegrable.integ]
    exact EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.abs.1)
  · -- Case: ∫f ≠ 0, use rotation trick
    -- Let u = conj(∫f) / ‖∫f‖ (a unit complex number)
    let u : ℂ := starRingEnd ℂ (hf.integ) / ‖hf.integ‖
    have hu_norm : ‖u‖ = 1 := by
      simp only [u, norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
                 abs_of_nonneg (norm_nonneg _)]
      exact div_self (norm_ne_zero_iff.mpr h)
    -- Show u * ∫f = ‖∫f‖ (a real positive number)
    have h_mul : u * hf.integ = ‖hf.integ‖ := by
      simp only [u]
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      rw [sq, mul_div_assoc, div_self, mul_one]
      exact_mod_cast norm_ne_zero_iff.mpr h
    -- By linearity: ∫(u*f) = u * ∫f = ‖∫f‖
    have h_integ_smul : (hf.smul u).integ = u * hf.integ := hf.integ_smul u
    have h_integ_eq : (hf.smul u).integ = ‖hf.integ‖ := by rw [h_integ_smul, h_mul]
    -- So (∫(u*f)).re = ‖∫f‖ and equals (hf.smul u).re.integ
    have h_re : (hf.smul u).integ.re = ‖hf.integ‖ := by rw [h_integ_eq]; simp
    have h_re_integ : (hf.smul u).integ.re = (hf.smul u).re.integ := (hf.smul u).integ_re_eq_re_integ
    have h_norm_eq : (‖hf.integ‖ : ℝ) = (hf.smul u).re.integ := by rw [← h_re, h_re_integ]
    -- Chain of inequalities: ‖∫f‖ = ∫Re(u * f) ≤ ∫|Re(u * f)| ≤ ∫|u*f| = ∫|f|
    calc (‖hf.integ‖ : ℝ)
        = (hf.smul u).re.integ := h_norm_eq
      _ ≤ |(hf.smul u).re.integ| := le_abs_self _
      _ ≤ (hf.smul u).re.abs.integ := (hf.smul u).re.abs_integ_le
      _ ≤ (hf.smul u).abs.integ := (hf.smul u).re_abs_integ_le
      _ = hf.abs.integ := hf.abs_smul_unit u hu_norm
