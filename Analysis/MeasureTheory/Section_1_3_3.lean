import Analysis.MeasureTheory.Section_1_3_2

/-!
# Introduction to Measure Theory, Section 1.3.3: Unsigned Lebesgue integrals

A companion to (the introduction to) Section 1.3.3 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.3.12 (Lower unsigned Lebesgue integral) -/
noncomputable def LowerUnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal) : EReal :=
  sSup { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ}

/-- Definition 1.3.12 (Upper unsigned Lebesgue integral) -/
noncomputable def UpperUnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal) : EReal :=
  sInf { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, ∀ x, g x ≥ f x ∧ R = hg.integ}

theorem LowerUnsignedLebesgueIntegral.eq {d:ℕ} {f: EuclideanSpace' d → EReal} (hf : ∀ x, 0 ≤ f x) : LowerUnsignedLebesgueIntegral f =
  sSup { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, (AlmostAlways (fun x ↦ g x ≤ f x)) ∧ R = hg.integ} := by
  -- Both sides are suprema over sets of integrals of simple functions g bounded by f.
  -- LHS: pointwise everywhere g ≤ f; RHS: almost everywhere g ≤ f.
  -- Equality follows since the simple integral is invariant under modification on null sets.
  unfold LowerUnsignedLebesgueIntegral
  -- First, simplify the weird definition: ∀ x, g x ≤ f x ∧ R = hg.integ is equivalent to
  -- (∀ x, g x ≤ f x) ∧ R = hg.integ (since R = hg.integ is constant in x)
  congr 1
  ext R
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨g, hg, hcond⟩
    -- Extract the pointwise bound and the equality
    have hle : ∀ x, g x ≤ f x := fun x ↦ (hcond x).1
    have hReq : R = hg.integ := by
      -- hcond gives us R = hg.integ for any x, so pick any x
      -- EuclideanSpace' d is always nonempty
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond (Classical.arbitrary _)).2
    exact ⟨g, hg, AlmostAlways.ofAlways hle, hReq⟩
  · intro ⟨g, hg, hae, hReq⟩
    -- Need to find g' with g' ≤ f everywhere and same integral
    -- Let N = {x | g x > f x} be the null set where g exceeds f
    let N := {x | ¬(g x ≤ f x)}
    have hN_null : IsNull N := hae
    have hN_meas : LebesgueMeasurable N := IsNull.measurable hN_null
    -- Define g' = g * indicator(Nᶜ) = g where g ≤ f, 0 elsewhere
    let g' := fun x => g x * (EReal.indicator Nᶜ x)
    -- g' is a simple function (product of simple function with indicator of measurable set)
    have hg'_simple : UnsignedSimpleFunction g' := by
      -- This follows from the definition of simple functions as linear combinations of indicators
      -- g = ∑ c_i • indicator(E_i), so g' = ∑ c_i • indicator(E_i ∩ Nᶜ)
      obtain ⟨k, c, E, ⟨hcE, hg_eq⟩⟩ := hg
      use k, c, fun i => E i ∩ Nᶜ
      constructor
      · intro i
        constructor
        · exact LebesgueMeasurable.inter (hcE i).1 (LebesgueMeasurable.complement hN_meas)
        · exact (hcE i).2
      · -- Prove g' = ∑ c_i • indicator(E_i ∩ Nᶜ) pointwise
        funext x
        simp only [g', hg_eq, EReal.indicator, Real.EReal_fun]
        -- Use Finset.sum_fn to convert (∑ i, f i) x to ∑ i, f i x
        conv_lhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
        conv_rhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
        by_cases hx : x ∈ Nᶜ
        · -- x ∈ Nᶜ: multiply by 1, and E_i ∩ Nᶜ membership reduces to E_i membership
          rw [Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Real.EReal_fun]
          by_cases hEi : x ∈ E i
          · rw [Set.indicator'_of_mem hEi, Set.indicator'_of_mem (Set.mem_inter hEi hx)]
          · have hnotinter : x ∉ E i ∩ Nᶜ := fun h => hEi (Set.mem_of_mem_inter_left h)
            rw [Set.indicator'_of_notMem hEi, Set.indicator'_of_notMem hnotinter]
        · -- x ∉ Nᶜ: multiply by 0, and E_i ∩ Nᶜ is empty at x
          rw [Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero]
          symm
          apply Finset.sum_eq_zero
          intro i _
          have hnotinter : x ∉ E i ∩ Nᶜ := fun h => hx (Set.mem_of_mem_inter_right h)
          simp only [Real.EReal_fun, Set.indicator'_of_notMem hnotinter, EReal.coe_zero, smul_zero]
    -- g' ≤ f everywhere
    have hg'_le_f : ∀ x, g' x ≤ f x := by
      intro x
      by_cases hx : x ∈ N
      · -- On N: g' x = g x * 0 = 0 ≤ f x (using hf)
        simp only [g', EReal.indicator, Real.EReal_fun]
        have hnotmem : x ∉ Nᶜ := by simp only [Set.mem_compl_iff, not_not]; exact hx
        rw [Set.indicator'_of_notMem hnotmem, EReal.coe_zero, mul_zero]
        exact hf x
      · -- On Nᶜ: g' x = g x * 1 = g x ≤ f x (by definition of N)
        simp only [N, Set.mem_setOf_eq] at hx
        push_neg at hx
        simp only [g', EReal.indicator, Real.EReal_fun]
        have hmem : x ∈ Nᶜ := by simp only [Set.mem_compl_iff, N, Set.mem_setOf_eq, hx, not_true_eq_false, not_false_eq_true]
        rw [Set.indicator'_of_mem hmem, EReal.coe_one, mul_one]
        exact hx
    -- g' = g almost everywhere (they differ only on N which is null)
    have hg'_ae : AlmostEverywhereEqual g' g := by
      unfold AlmostEverywhereEqual AlmostAlways IsNull
      -- {x | g' x ≠ g x} ⊆ N, and N is null
      have hsub : {x | g' x ≠ g x} ⊆ N := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        by_contra hxN
        -- If x ∉ N, then g' x = g x * 1 = g x
        have hmem : x ∈ Nᶜ := by simp only [Set.mem_compl_iff, N, Set.mem_setOf_eq]; exact hxN
        simp only [g', EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hmem,
                   EReal.coe_one, mul_one] at hx
        exact hx rfl
      have hle : Lebesgue_outer_measure {x | g' x ≠ g x} ≤ 0 :=
        calc Lebesgue_outer_measure {x | g' x ≠ g x}
            ≤ Lebesgue_outer_measure N := Lebesgue_outer_measure.mono hsub
          _ = 0 := hN_null
      exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)
    -- By Exercise 1.3.1(iv), same integral
    have hinteg_eq : hg'_simple.integ = hg.integ :=
      UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hg'_simple hg hg'_ae
    -- Now construct the witness
    use g', hg'_simple
    intro x
    constructor
    · exact hg'_le_f x
    · rw [hReq, ← hinteg_eq]

/-- Exercise 1.3.10(i) (Compatibility with the simple integral) -/
theorem LowerUnsignedLebesgueIntegral.eq_simpleIntegral {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
    LowerUnsignedLebesgueIntegral f = hf.integ := by sorry

/-- Exercise 1.3.10(ii) (Monotonicity) -/
theorem LowerUnsignedLebesgueIntegral.mono {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: AlmostAlways (fun x ↦ f x ≤ g x)) :
    LowerUnsignedLebesgueIntegral f ≤ LowerUnsignedLebesgueIntegral g := by sorry

/-- Exercise 1.3.10(iii) (Homogeneity) -/
theorem LowerUnsignedLebesgueIntegral.hom {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {c: ℝ} (hc: 0 ≤ c) :
    LowerUnsignedLebesgueIntegral ((c:EReal) • f) = c * LowerUnsignedLebesgueIntegral f := by sorry

/-- Exercise 1.3.10(iv) (Equivalence) -/
theorem LowerUnsignedLebesgueIntegral.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (heq: AlmostEverywhereEqual f g) :
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral g := by sorry

/-- Exercise 1.3.10(v) (Superadditivity) -/
theorem LowerUnsignedLebesgueIntegral.superadditive {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g) :
    LowerUnsignedLebesgueIntegral (f + g) ≥ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by sorry

/-- Exercise 1.3.10(vi) (Subadditivity of upper integral)-/
theorem UpperUnsignedLebesgueIntegral.subadditive {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g) :
    UpperUnsignedLebesgueIntegral (f + g) ≤ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g := by sorry

/-- Exercise 1.3.10(vii) (Divisibility) -/
theorem LowerUnsignedLebesgueIntegral.eq_add {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {E: Set (EuclideanSpace' d)} (hE: MeasurableSet E) :
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ E.indicator') +
      LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ Eᶜ.indicator') := by sorry

/-- Exercise 1.3.10(viii) (Vertical truncation)-/
theorem LowerUnsignedLebesgueIntegral.eq_lim_vert_trunc {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n:ℕ ↦ LowerUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (LowerUnsignedLebesgueIntegral f)) := by sorry

def UpperUnsignedLebesgueIntegral.eq_lim_vert_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 1.3.10(ix) (Horizontal truncation)-/
theorem LowerUnsignedLebesgueIntegral.eq_lim_horiz_trunc {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n:ℕ ↦ LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (LowerUnsignedLebesgueIntegral f)) := by sorry

def UpperUnsignedLebesgueIntegral.eq_lim_horiz_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 1.3.10(x) (Reflection) -/
theorem LowerUnsignedLebesgueIntegral.sum_of_reflect_eq {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: UnsignedSimpleFunction (f+g)) (hbound: EReal.BoundedFunction (f + g)) (hsupport: FiniteMeasureSupport (f + g)) :
    hfg.integ = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by sorry

/-- Definition 1.3.13 (Unsigned Lebesgue integral).  For Lean purposes it is convenient to assign a "junk" value to this integral when f is not unsigned measurable. -/
noncomputable def UnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal): EReal := LowerUnsignedLebesgueIntegral f

noncomputable def UnsignedMeasurable.integ {d:ℕ} (f: EuclideanSpace' d → EReal) (_: UnsignedMeasurable f) : EReal := UnsignedLebesgueIntegral f

/-- Exercise 1.3.11 -/
theorem LowerUnsignedLebesgueIntegral.eq_upperIntegral {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f) (hsupp: FiniteMeasureSupport f) :
    LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f := by sorry

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_unbounded : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hsupp: FiniteMeasureSupport f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_infinite_supp : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Multiplying an unsigned measurable function by a ball indicator preserves measurability.
    This is a key helper for the horizontal truncation argument in Corollary 1.3.14. -/
lemma UnsignedMeasurable.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (n : ℕ) :
    UnsignedMeasurable (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  -- The indicator of a ball is measurable (balls are open, hence measurable)
  -- Multiplication of measurable functions is measurable
  -- The product of nonnegative functions is nonnegative
  constructor
  · -- Unsigned: f x * ind x ≥ 0 since f x ≥ 0 and ind x ∈ {0, 1}
    intro x
    simp only [Pi.mul_apply, Function.comp_apply]
    apply mul_nonneg (hf.1 x)
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
    · simp [Set.indicator'_of_mem hx]
    · simp [Set.indicator'_of_notMem hx]
  · -- Measurable: follows from closure of measurable functions under multiplication
    -- and measurability of indicator functions
    sorry

/-- Helper: horizontal truncation produces functions with finite measure support. -/
lemma FiniteMeasureSupport.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (n : ℕ) : FiniteMeasureSupport (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  -- Support of f * ind is contained in ball 0 n, which has finite Lebesgue measure
  -- The key facts are:
  -- 1. If x ∉ ball 0 n, then ind x = 0, so f x * ind x = 0
  -- 2. So support ⊆ ball 0 n
  -- 3. Balls have finite Lebesgue measure
  sorry

/-- Additivity of lower integral for finite-support functions.
    This is the key step where we can apply {name}`eq_upperIntegral` and use the sandwich argument. -/
lemma LowerUnsignedLebesgueIntegral.add_of_finiteSupport {d : ℕ}
    {f g : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (hfg : UnsignedMeasurable (f + g))
    (hf_supp : FiniteMeasureSupport f) (hg_supp : FiniteMeasureSupport g) :
    LowerUnsignedLebesgueIntegral (f + g) =
      LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  -- For finite-support functions, use vertical truncation to reduce to bounded case,
  -- then apply eq_upperIntegral to show Lower = Upper, then sandwich:
  --   Lower(f+g) ≥ Lower(f) + Lower(g)  [superadditive]
  --   Lower(f+g) = Upper(f+g) ≤ Upper(f) + Upper(g) = Lower(f) + Lower(g)  [eq_upperIntegral + subadditive]
  apply le_antisymm
  · -- ≤ direction: use vertical truncation + eq_upperIntegral + subadditive
    -- For bounded finite-support: Lower = Upper by eq_upperIntegral
    -- Then Upper(f+g) ≤ Upper(f) + Upper(g) by subadditive
    -- Take vertical truncation limit to handle unbounded case
    sorry
  · -- ≥ direction: direct from superadditivity
    exact LowerUnsignedLebesgueIntegral.superadditive hf hg

/-- Corollary 1.3.14 (Finite additivity of Lebesgue integral )-/
theorem LowerUnsignedLebesgueIntegral.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: UnsignedMeasurable (f + g)) :
    LowerUnsignedLebesgueIntegral (f + g) = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  apply le_antisymm
  · -- ≤: horizontal truncation → finite support → additivity → limit
    let f_h := fun n : ℕ ↦ f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
    let g_h := fun n : ℕ ↦ g * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
    let fg_h := fun n : ℕ ↦ (f + g) * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'

    have hfg_lim := eq_lim_horiz_trunc hfg

    -- (f+g) * ind = f * ind + g * ind by right_distrib for nonneg
    have heq : ∀ n, fg_h n = f_h n + g_h n := by
      intro n; funext x
      simp only [f_h, g_h, fg_h, Pi.add_apply, Pi.mul_apply]
      exact EReal.right_distrib_of_nonneg (hf.1 x) (hg.1 x)

    -- Additivity for finite-support truncations
    have heq_integ : ∀ n, LowerUnsignedLebesgueIntegral (fg_h n) =
        LowerUnsignedLebesgueIntegral (f_h n) + LowerUnsignedLebesgueIntegral (g_h n) := by
      intro n
      rw [heq n]
      apply LowerUnsignedLebesgueIntegral.add_of_finiteSupport
      · exact UnsignedMeasurable.mul_indicator_ball hf n
      · exact UnsignedMeasurable.mul_indicator_ball hg n
      · exact UnsignedMeasurable.add (UnsignedMeasurable.mul_indicator_ball hf n)
            (UnsignedMeasurable.mul_indicator_ball hg n)
      · exact FiniteMeasureSupport.mul_indicator_ball n
      · exact FiniteMeasureSupport.mul_indicator_ball n

    conv at hfg_lim => arg 1; ext n; rw [heq_integ n]

    -- Use le_of_tendsto': Lower(f_h n) + Lower(g_h n) → Lower(f+g) and each term ≤ limit
    apply le_of_tendsto' hfg_lim
    intro n
    apply add_le_add
    · -- Lower(f_h n) ≤ Lower(f) by monotonicity (f_h n ≤ f pointwise)
      apply LowerUnsignedLebesgueIntegral.mono (UnsignedMeasurable.mul_indicator_ball hf n) hf
      apply AlmostAlways.ofAlways; intro x
      simp only [Pi.mul_apply, Function.comp_apply]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]; exact hf.1 x
    · -- Lower(g_h n) ≤ Lower(g) by monotonicity
      apply LowerUnsignedLebesgueIntegral.mono (UnsignedMeasurable.mul_indicator_ball hg n) hg
      apply AlmostAlways.ofAlways; intro x
      simp only [Pi.mul_apply, Function.comp_apply]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]; exact hg.1 x
  · -- ≥: from superadditivity
    exact LowerUnsignedLebesgueIntegral.superadditive hf hg

/-- Exercise 1.3.12 (Upper Lebesgue integral and outer measure)-/
theorem UpperUnsignedLebesgueIntegral.eq_outer_measure_integral {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: MeasurableSet E) :
    UpperUnsignedLebesgueIntegral (Real.toEReal ∘ E.indicator') = Lebesgue_outer_measure E := by sorry

theorem LowerUnsignedLebesgueIntegral.not_additive : ∃ (d:ℕ) (f g: EuclideanSpace' d → EReal) (hf: Unsigned f) (hg: Unsigned g), (LowerUnsignedLebesgueIntegral (f + g) ≠ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g) := by
    sorry

theorem UpperUnsignedLebesgueIntegral.not_additive : ∃ (d:ℕ) (f g: EuclideanSpace' d → EReal) (hf: Unsigned f) (hg: Unsigned g), (UpperUnsignedLebesgueIntegral (f + g) ≠ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g) := by
    sorry

/-- Exercise 1.3.13 (Area interpretation of integral)-/
theorem LowerUnsignedLebesgueIntegral.eq_area {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
    LowerUnsignedLebesgueIntegral f = Lebesgue_measure { p | ∃ x, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by sorry

/-- Exercise 1.3.14 (Uniqueness) -/
theorem UnsignedLebesgueIntegral.unique {d:ℕ} (integ: (EuclideanSpace' d → EReal) → EReal)
  (hsimple : ∀ f (hf: UnsignedSimpleFunction f), integ f = hf.integ)
  (hadd: ∀ f g (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g), integ (f + g) = integ f + integ g)
  (hvert: ∀ f (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (fun x ↦ min (f x) n)) (nhds (integ f)))
  (hhoriz: ∀ f (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (integ f)))
  : ∀ f, UnsignedMeasurable f → integ f = UnsignedLebesgueIntegral f := by sorry

/-- Exercise 1.3.15 (Translation invariance)-/
theorem UnsignedLebesgueIntegral.trans {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (a: EuclideanSpace' d) :
    UnsignedLebesgueIntegral (fun x ↦ f (x + a)) = hf.integ := by sorry

/-- Exercise 1.3.16 (Linear change of variables)-/
theorem UnsignedLebesgueIntegral.comp_linear {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d) (hA: A.det ≠ 0) :
    UnsignedLebesgueIntegral (fun x ↦ f (A x)) = |A.det|⁻¹ * hf.integ := by sorry

/-- Exercise 1.3.17 (Compatibility with the Riemann integral)-/
theorem RiemannIntegral.eq_UnsignedLebesgueIntegral {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) :
    (riemannIntegral f I : EReal) = UnsignedLebesgueIntegral (Real.toEReal ∘ (fun x ↦ (f x) * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real) := by sorry

/-- Lemma 1.3.15 (Markov's inequality) -/
theorem UnsignedLebesgueIntegral.markov_inequality {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {t:ℝ} (ht: 0 < t) :
    Lebesgue_measure { x | f x ≥ t } ≤ hf.integ / (t:EReal) := by
  sorry

/-- Exercise 1.3.18 (ii) -/
theorem UnsignedLebesgueIntegral.ae_finite {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hfin: UnsignedLebesgueIntegral f < ⊤) :
    AlmostAlways (fun x ↦ f x < ⊤) := by sorry

theorem UnsignedLebesgueIntegral.ae_finite_no_converse : ∃ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hfin: AlmostAlways (fun x ↦ f x < ⊤)), UnsignedLebesgueIntegral f = ⊤ := by sorry

/-- Exercise 1.3.18 (ii) -/
theorem UnsignedLebesgueIntegral.eq_zero_aeZero {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
     hf.integ = 0 ↔ AlmostAlways (fun x ↦ f x = 0) := by sorry
