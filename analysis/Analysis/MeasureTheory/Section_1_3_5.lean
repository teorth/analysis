import Analysis.MeasureTheory.Section_1_3_4
import Mathlib.Topology.UrysohnsLemma

/-!
# Introduction to Measure Theory, Section 1.3.5: Littlewood's three principles

A companion to (the introduction to) Section 1.3.5 of the book "An introduction to Measure Theory".

-/

/-- Helper: extract a simple function approximation from the sSup definition of the unsigned integral.
  Given an unsigned absolutely integrable f and ε > 0, there exists a simple g ≤ f pointwise
  whose integral is within ε of the integral of f. -/
private lemma unsigned_approx_from_sup {d:ℕ} {f: EuclideanSpace' d → EReal}
    (hf : UnsignedAbsolutelyIntegrable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → EReal) (hg : UnsignedSimpleFunction g),
      (∀ x, g x ≤ f x) ∧
      UnsignedLebesgueIntegral f ≤ hg.integ + ε := by
  set L := UnsignedLebesgueIntegral f with hL_def
  have hL_lt_top : L < ⊤ := hf.2
  have hL_ne_top : L ≠ ⊤ := ne_of_lt hL_lt_top
  have hL_nonneg : (0 : EReal) ≤ L := UnsignedLebesgueIntegral.nonneg hf.1
  have hL_ne_bot : L ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hL_nonneg)
  -- L - ε < L (since ε > 0 and L is finite)
  have hε_ne_bot : (ε : EReal) ≠ ⊥ := EReal.coe_ne_bot ε
  have hε_ne_top : (ε : EReal) ≠ ⊤ := EReal.coe_ne_top ε
  have hL_sub_lt : L - (ε : EReal) < L := by
    rw [EReal.sub_lt_iff (Or.inl hε_ne_bot) (Or.inl hε_ne_top)]
    calc L = 0 + L := (zero_add L).symm
      _ < (ε : EReal) + L := EReal.add_lt_add_of_lt_of_le
          (EReal.coe_pos.mpr hε) le_rfl hL_ne_bot hL_ne_top
      _ = L + (ε : EReal) := add_comm _ _
  -- Extract R from the sSup definition with R > L - ε
  -- L = sSup S by definition (after unfolding)
  have hR_exists : ∃ R ∈ { R : EReal | ∃ g : EuclideanSpace' d → EReal,
      ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ },
      L - (ε : EReal) < R := by
    by_contra h_all
    push_neg at h_all
    have h_le : L ≤ L - (ε : EReal) := by
      conv_lhs => rw [hL_def, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
      exact sSup_le fun R hR => h_all R hR
    exact absurd h_le (not_le.mpr hL_sub_lt)
  obtain ⟨R, hR_mem, hR_gt⟩ := hR_exists
  obtain ⟨g, hg, hcond⟩ := hR_mem
  have hg_le : ∀ x, g x ≤ f x := fun x => (hcond x).1
  have hR_eq : R = hg.integ := (hcond (0 : EuclideanSpace' d)).2
  refine ⟨g, hg, hg_le, ?_⟩
  rw [hR_eq] at hR_gt
  exact le_of_lt ((EReal.sub_lt_iff (Or.inl hε_ne_bot)
      (Or.inl hε_ne_top)).mp hR_gt)

/-- Helper: convert an unsigned simple function with finite values to a real simple function. -/
private lemma UnsignedSimpleFunction.toRealSimple {d:ℕ} {g: EuclideanSpace' d → EReal}
    (hg: UnsignedSimpleFunction g) (hfin: ∀ x, g x ≠ ⊤) :
    ∃ (h : EuclideanSpace' d → ℝ), RealSimpleFunction h ∧
      (∀ x, 0 ≤ h x) ∧ (∀ x, (h x : EReal) = g x) := by
  -- Unpack: g = ∑ i, c_i • indicator(E_i) with c_i ≥ 0, E_i measurable
  obtain ⟨k, c, E, hcond, heq⟩ := hg
  -- Define h = ∑ i, c_i.toReal • indicator'(E_i) as a real function
  set c' : Fin k → ℝ := fun i => (c i).toReal with hc'_def
  set h : EuclideanSpace' d → ℝ := fun x => ∑ i, c' i * (E i).indicator' x with hh_def
  refine ⟨h, ?_, ?_, ?_⟩
  · -- RealSimpleFunction h
    exact ⟨k, c', E, fun i => (hcond i).1, by ext x; simp [hh_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]⟩
  · -- h x ≥ 0 for all x
    intro x; simp only [hh_def]
    apply Finset.sum_nonneg; intro i _
    apply mul_nonneg
    · -- c'_i ≥ 0
      simp only [hc'_def]
      exact EReal.toReal_nonneg (hcond i).2
    · -- indicator' ≥ 0
      by_cases hx : x ∈ E i
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]
  · -- (h x : EReal) = g x
    intro x
    simp only [hh_def, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Show term-by-term that the real sum cast to EReal = the EReal sum
    -- First, prove the casting lemma for sums
    have hcoe_sum : ∀ (n : ℕ) (a : Fin n → ℝ),
        (↑(∑ i, a i) : EReal) = ∑ i, (↑(a i) : EReal) := by
      intro n a; induction n with
      | zero => simp [Finset.univ_eq_empty]
      | succ m ih =>
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, EReal.coe_add]
        congr 1; exact ih (fun i => a i.castSucc)
    rw [hcoe_sum]
    congr 1; ext i
    -- Need: (c'_i * indicator'(E_i)(x) : EReal) = c_i * EReal.indicator(E_i)(x)
    by_cases hx : x ∈ E i
    · -- x ∈ E i: both sides equal c_i (resp. c_i.toReal cast)
      simp only [hc'_def, Set.indicator'_of_mem hx, mul_one,
        EReal.indicator, Real.EReal_fun]
      -- Goal: ((c i).toReal : EReal) = c i
      have hci_ne_bot : c i ≠ ⊥ :=
        ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hcond i).2)
      have hci_ne_top : c i ≠ ⊤ := by
        intro hci_top
        apply hfin x
        rw [heq]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply eq_top_iff.mpr
        have : c i * EReal.indicator (E i) x = ⊤ := by
          simp only [hci_top, EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hx]
          simp
        rw [← this]
        apply Finset.single_le_sum (f := fun j => c j * EReal.indicator (E j) x)
          (fun j _ => mul_nonneg (hcond j).2 (by
            simp only [EReal.indicator, Real.EReal_fun]
            by_cases hxj : x ∈ E j
            · simp [Set.indicator'_of_mem hxj]
            · simp [Set.indicator'_of_notMem hxj])) (Finset.mem_univ i)
      rw [show (1 : ℝ).toEReal = (1 : EReal) from rfl, mul_one]
      exact EReal.coe_toReal hci_ne_top hci_ne_bot
    · -- x ∉ E i: both sides are 0
      simp only [Set.indicator'_of_notMem hx, mul_zero, EReal.coe_zero,
        EReal.indicator, Real.EReal_fun, MulZeroClass.mul_zero]

/-- Theorem 1.3.20(i) Approximation of $L^1$ functions by simple functions (real case) -/
theorem RealAbsolutelyIntegrable.approx_by_simple {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℝ), RealSimpleFunction g ∧ RealAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Step 1: Get approximations for positive and negative parts
  have hε2 : 0 < ε / 2 := half_pos hε
  have hf_pos := hf.pos  -- UnsignedAbsolutelyIntegrable (EReal.pos_fun f)
  have hf_neg := hf.neg  -- UnsignedAbsolutelyIntegrable (EReal.neg_fun f)
  obtain ⟨g_pos, hg_pos, hg_pos_le, hg_pos_bound⟩ := unsigned_approx_from_sup hf_pos (ε / 2) hε2
  obtain ⟨g_neg, hg_neg, hg_neg_le, hg_neg_bound⟩ := unsigned_approx_from_sup hf_neg (ε / 2) hε2
  -- Step 2: Convert to real simple functions
  have hg_pos_fin : ∀ x, g_pos x ≠ ⊤ := fun x =>
    ne_of_lt (lt_of_le_of_lt (hg_pos_le x) (by
      simp only [EReal.pos_fun]; exact EReal.coe_lt_top _))
  have hg_neg_fin : ∀ x, g_neg x ≠ ⊤ := fun x =>
    ne_of_lt (lt_of_le_of_lt (hg_neg_le x) (by
      simp only [EReal.neg_fun]; exact EReal.coe_lt_top _))
  obtain ⟨h_pos, hh_pos_simple, hh_pos_nonneg, hh_pos_eq⟩ :=
    UnsignedSimpleFunction.toRealSimple hg_pos hg_pos_fin
  obtain ⟨h_neg, hh_neg_simple, hh_neg_nonneg, hh_neg_eq⟩ :=
    UnsignedSimpleFunction.toRealSimple hg_neg hg_neg_fin
  -- Step 3: Define g = h_pos - h_neg
  set g : EuclideanSpace' d → ℝ := h_pos - h_neg with hg_def
  have hg_simple : RealSimpleFunction g := by
    rw [show g = h_pos + (-1 : ℝ) • h_neg from by ext x; simp [hg_def, sub_eq_add_neg]]
    exact RealSimpleFunction.add hh_pos_simple (RealSimpleFunction.smul hh_neg_simple (-1))
  -- Step 4: Show h_pos and h_neg are absolutely integrable
  have habs_fun_eq_pos : EReal.abs_fun h_pos = g_pos := by
    ext x; simp only [EReal.abs_fun, Real.norm_eq_abs, abs_of_nonneg (hh_pos_nonneg x)]
    exact hh_pos_eq x
  have habs_fun_eq_neg : EReal.abs_fun h_neg = g_neg := by
    ext x; simp only [EReal.abs_fun, Real.norm_eq_abs, abs_of_nonneg (hh_neg_nonneg x)]
    exact hh_neg_eq x
  have hh_pos_ai : RealAbsolutelyIntegrable h_pos := by
    constructor
    · exact ⟨fun _ => h_pos, fun _ => hh_pos_simple, fun _ => tendsto_const_nhds⟩
    · rw [UnsignedLebesgueIntegral, habs_fun_eq_pos,
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_pos]
      calc hg_pos.integ ≤ UnsignedLebesgueIntegral (EReal.pos_fun f) := by
            rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
            exact le_sSup ⟨g_pos, hg_pos, fun x => ⟨hg_pos_le x, rfl⟩⟩
        _ < ⊤ := hf_pos.2
  have hh_neg_ai : RealAbsolutelyIntegrable h_neg := by
    constructor
    · exact ⟨fun _ => h_neg, fun _ => hh_neg_simple, fun _ => tendsto_const_nhds⟩
    · rw [UnsignedLebesgueIntegral, habs_fun_eq_neg,
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_neg]
      calc hg_neg.integ ≤ UnsignedLebesgueIntegral (EReal.neg_fun f) := by
            rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
            exact le_sSup ⟨g_neg, hg_neg, fun x => ⟨hg_neg_le x, rfl⟩⟩
        _ < ⊤ := hf_neg.2
  have hg_ai : RealAbsolutelyIntegrable g := by
    rw [hg_def]; exact RealAbsolutelyIntegrable.sub hh_pos_ai hh_neg_ai
  -- Step 5: Show the norm bound PreL1.norm (f - g) ≤ ε
  refine ⟨g, hg_simple, hg_ai, ?_⟩
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  -- Auxiliary: h_pos, h_neg bounded by max(f,0), max(-f,0)
  have h_pos_le : ∀ x, h_pos x ≤ max (f x) 0 := fun x =>
    EReal.coe_le_coe_iff.mp (le_trans (le_of_eq (hh_pos_eq x)) (hg_pos_le x))
  have h_neg_le : ∀ x, h_neg x ≤ max (-(f x)) 0 := fun x =>
    EReal.coe_le_coe_iff.mp (le_trans (le_of_eq (hh_neg_eq x)) (hg_neg_le x))
  -- Pointwise bound: ‖(f - g) x‖ + h_pos x + h_neg x ≤ ‖f x‖
  have h_pw : ∀ x, ‖(f - g) x‖ + h_pos x + h_neg x ≤ ‖f x‖ := by
    intro x
    simp only [hg_def, Pi.sub_apply, Real.norm_eq_abs]
    rcases le_or_gt 0 (f x) with hfx | hfx
    · -- f x ≥ 0: max(-f x, 0) = 0, so h_neg x = 0
      have hb0 : h_neg x = 0 :=
        le_antisymm (by linarith [h_neg_le x, max_eq_right (neg_nonpos.mpr hfx)])
          (hh_neg_nonneg x)
      have ha_le_fx : h_pos x ≤ f x := by
        have := h_pos_le x; rwa [max_eq_left hfx] at this
      rw [hb0]; simp only [sub_zero, add_zero]
      rw [abs_of_nonneg hfx, abs_of_nonneg (sub_nonneg.mpr ha_le_fx)]
      linarith
    · -- f x < 0: max(f x, 0) = 0, so h_pos x = 0
      have ha0 : h_pos x = 0 :=
        le_antisymm (by linarith [h_pos_le x, max_eq_right (le_of_lt hfx)])
          (hh_pos_nonneg x)
      have hb_le_neg : h_neg x ≤ -(f x) := by
        have := h_neg_le x; rwa [max_eq_left (neg_nonneg.mpr (le_of_lt hfx))] at this
      rw [ha0]; simp only [zero_sub, add_zero]
      rw [abs_of_neg hfx, show f x - -h_neg x = f x + h_neg x from by ring,
          abs_of_nonpos (by linarith)]
      linarith
  -- Convert to EReal: abs_fun(f-g)(x) + (g_pos + g_neg)(x) ≤ abs_fun(f)(x)
  have h_pw_e : ∀ x, (EReal.abs_fun (f - g) + (g_pos + g_neg)) x ≤ EReal.abs_fun f x := by
    intro x
    simp only [Pi.add_apply, EReal.abs_fun]
    rw [← hh_pos_eq x, ← hh_neg_eq x, ← EReal.coe_add, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (by linarith [h_pw x])
  -- Measurability
  have hm_gp : UnsignedMeasurable g_pos := hg_pos.unsignedMeasurable
  have hm_gn : UnsignedMeasurable g_neg := hg_neg.unsignedMeasurable
  have hm_gp_gn : UnsignedMeasurable (g_pos + g_neg) := hm_gp.add hm_gn
  have hm_abs_fg : UnsignedMeasurable (EReal.abs_fun (f - g)) :=
    (RealAbsolutelyIntegrable.abs _ (hf.sub hg_ai)).1
  have hm_abs_f : UnsignedMeasurable (EReal.abs_fun f) :=
    (RealAbsolutelyIntegrable.abs _ hf).1
  have hm_sum : UnsignedMeasurable (EReal.abs_fun (f - g) + (g_pos + g_neg)) :=
    hm_abs_fg.add hm_gp_gn
  -- Monotonicity: ∫(abs_fun(f-g) + (g_pos + g_neg)) ≤ ∫(abs_fun f)
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + (g_pos + g_neg)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun f) :=
    LowerUnsignedLebesgueIntegral.mono hm_sum hm_abs_f (AlmostAlways.ofAlways h_pw_e)
  -- Additivity: ∫(abs_fun(f-g) + (g_pos + g_neg)) = ∫abs_fun(f-g) + ∫(g_pos + g_neg)
  have h_add_lhs : UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + (g_pos + g_neg)) =
      UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) +
      UnsignedLebesgueIntegral (g_pos + g_neg) :=
    LowerUnsignedLebesgueIntegral.add hm_abs_fg hm_gp_gn hm_sum
  -- ∫(g_pos + g_neg) = ∫g_pos + ∫g_neg
  have h_add_gp_gn : UnsignedLebesgueIntegral (g_pos + g_neg) =
      UnsignedLebesgueIntegral g_pos + UnsignedLebesgueIntegral g_neg :=
    LowerUnsignedLebesgueIntegral.add hm_gp hm_gn hm_gp_gn
  -- Simple integrals
  have h_gp_integ : UnsignedLebesgueIntegral g_pos = hg_pos.integ :=
    LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_pos
  have h_gn_integ : UnsignedLebesgueIntegral g_neg = hg_neg.integ :=
    LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_neg
  -- abs_fun f = pos_fun f + neg_fun f
  have h_abs_eq : EReal.abs_fun f = EReal.pos_fun f + EReal.neg_fun f := by
    ext x; simp only [EReal.abs_fun, EReal.pos_fun, EReal.neg_fun, Pi.add_apply,
      Real.norm_eq_abs]
    rw [show (↑|f x| : EReal) = ↑(max (f x) 0 + max (-(f x)) 0) from by
      congr 1; rcases le_or_gt 0 (f x) with hfx | hfx
      · simp [max_eq_left hfx, max_eq_right (neg_nonpos.mpr hfx), abs_of_nonneg hfx]
      · simp [max_eq_right (le_of_lt hfx), max_eq_left (neg_nonneg.mpr (le_of_lt hfx)),
              abs_of_neg hfx]]
    exact EReal.coe_add _ _
  have h_abs_add : UnsignedLebesgueIntegral (EReal.abs_fun f) =
      UnsignedLebesgueIntegral (EReal.pos_fun f) +
      UnsignedLebesgueIntegral (EReal.neg_fun f) := by
    rw [h_abs_eq]
    exact LowerUnsignedLebesgueIntegral.add hf_pos.1 hf_neg.1
      (by rw [← h_abs_eq]; exact hm_abs_f)
  -- Set C = ∫(g_pos + g_neg) = hg_pos.integ + hg_neg.integ
  set C := UnsignedLebesgueIntegral (g_pos + g_neg) with hC_def
  have hC_eq : C = hg_pos.integ + hg_neg.integ := by
    have := h_add_gp_gn; rw [h_gp_integ, h_gn_integ] at this; exact this
  have hC_lt_top : C < ⊤ := by
    rw [hC_eq]
    calc hg_pos.integ + hg_neg.integ
        ≤ UnsignedLebesgueIntegral (EReal.pos_fun f) +
          UnsignedLebesgueIntegral (EReal.neg_fun f) :=
          add_le_add
            (by rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
                exact le_sSup ⟨g_pos, hg_pos, fun x => ⟨hg_pos_le x, rfl⟩⟩)
            (by rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral]
                exact le_sSup ⟨g_neg, hg_neg, fun x => ⟨hg_neg_le x, rfl⟩⟩)
      _ = UnsignedLebesgueIntegral (EReal.abs_fun f) := h_abs_add.symm
      _ < ⊤ := hf.2
  have hC_ne_top : C ≠ ⊤ := ne_of_lt hC_lt_top
  have hC_nonneg : (0 : EReal) ≤ C := UnsignedLebesgueIntegral.nonneg hm_gp_gn
  have hC_ne_bot : C ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hC_nonneg)
  -- Upper bound: ∫|f| ≤ C + ε
  have h_upper : UnsignedLebesgueIntegral (EReal.abs_fun f) ≤ C + (ε : EReal) := by
    rw [h_abs_add, hC_eq]
    calc UnsignedLebesgueIntegral (EReal.pos_fun f) +
          UnsignedLebesgueIntegral (EReal.neg_fun f)
        ≤ (hg_pos.integ + (ε / 2 : ℝ)) + (hg_neg.integ + (ε / 2 : ℝ)) :=
          add_le_add hg_pos_bound hg_neg_bound
      _ = hg_pos.integ + hg_neg.integ + (ε : EReal) := by
          rw [show (ε : EReal) = (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) from by
            rw [← EReal.coe_add]; congr 1; linarith]
          abel
  -- Lower bound from monotonicity + additivity
  have h_lower : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + C ≤
      UnsignedLebesgueIntegral (EReal.abs_fun f) := by
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + C
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + (g_pos + g_neg)) := by
          rw [h_add_lhs]
      _ ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := h_mono
  -- Combine and cancel C
  have h_combined : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + C ≤ C + (ε : EReal) :=
    le_trans h_lower h_upper
  have hC_real : C = (C.toReal : EReal) := (EReal.coe_toReal hC_ne_top hC_ne_bot).symm
  rw [hC_real] at h_combined
  rw [add_comm (↑C.toReal : EReal) (↑ε : EReal)] at h_combined
  exact (EReal.addLECancellable_coe C.toReal).add_le_add_iff_right.mp h_combined

/-- Theorem 1.3.20(i) Approximation of $L^1$ functions by simple functions (complex case) -/
theorem ComplexAbsolutelyIntegrable.approx_by_simple {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexSimpleFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Approximate real and imaginary parts within ε/2
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g_re, hg_re_simple, hg_re_ai, hg_re_norm⟩ :=
    (ComplexAbsolutelyIntegrable.re f hf).approx_by_simple (ε / 2) hε2
  obtain ⟨g_im, hg_im_simple, hg_im_ai, hg_im_norm⟩ :=
    (ComplexAbsolutelyIntegrable.im f hf).approx_by_simple (ε / 2) hε2
  -- Construct complex approximation g = ↑g_re + I • ↑g_im
  set g : EuclideanSpace' d → ℂ :=
    Real.complex_fun g_re + Complex.I • Real.complex_fun g_im with hg_def
  have hg_re_eq : Complex.re_fun g = g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hg_im_eq : Complex.im_fun g = g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  have hg_simple : ComplexSimpleFunction g :=
    ComplexSimpleFunction.add
      (RealSimpleFunction.toComplex g_re hg_re_simple)
      (ComplexSimpleFunction.smul (RealSimpleFunction.toComplex g_im hg_im_simple) Complex.I)
  have hg_ai : ComplexAbsolutelyIntegrable g := by
    apply (ComplexAbsolutelyIntegrable.iff g).mpr
    exact ⟨hg_re_eq ▸ hg_re_ai, hg_im_eq ▸ hg_im_ai⟩
  refine ⟨g, hg_simple, hg_ai, ?_⟩
  -- Norm bound: PreL1.norm (f - g) ≤ ε
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  -- Re/Im of f - g
  have hfg_re : Complex.re_fun (f - g) = Complex.re_fun f - g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hfg_im : Complex.im_fun (f - g) = Complex.im_fun f - g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  -- Pointwise: |f-g| ≤ |Re(f-g)| + |Im(f-g)|
  have h_bound : ∀ x, EReal.abs_fun (f - g) x ≤
      (EReal.abs_fun (Complex.re_fun (f - g)) + EReal.abs_fun (Complex.im_fun (f - g))) x :=
    fun x => by
      simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by
        calc ‖(f - g) x‖ ≤ |((f - g) x).re| + |((f - g) x).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = ‖((f - g) x).re‖ + ‖((f - g) x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  -- Measurability
  have hfg_ai := hf.sub hg_ai
  have hfg_re_ai := ComplexAbsolutelyIntegrable.re (f - g) hfg_ai
  have hfg_im_ai := ComplexAbsolutelyIntegrable.im (f - g) hfg_ai
  -- Monotonicity: ∫|f-g| ≤ ∫(|Re(f-g)| + |Im(f-g)|)
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
                                EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.mono hfg_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1) (AlmostAlways.ofAlways h_bound)
  -- Additivity: ∫(|Re(f-g)| + |Im(f-g)|) = ∫|Re(f-g)| + ∫|Im(f-g)|
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
      EReal.abs_fun (Complex.im_fun (f - g))) =
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g))) +
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.add hfg_re_ai.abs.1 hfg_im_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1)
  rw [h_add] at h_mono
  -- Rewrite using hfg_re, hfg_im to connect to PreL1.norm
  rw [show EReal.abs_fun (Complex.re_fun (f - g)) =
        EReal.abs_fun (Complex.re_fun f - g_re) from by rw [hfg_re],
      show EReal.abs_fun (Complex.im_fun (f - g)) =
        EReal.abs_fun (Complex.im_fun f - g_im) from by rw [hfg_im]] at h_mono
  -- Combine: ≤ ε/2 + ε/2 = ε
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f - g_re)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f - g_im)) := h_mono
    _ ≤ (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) := add_le_add hg_re_norm hg_im_norm
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

def ComplexStepFunction {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop :=
  ∃ (S: Finset (Box d)) (c: S → ℂ), f = ∑ B, (c B • Complex.indicator (B.val.toSet))

def RealStepFunction {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop :=
  ∃ (S: Finset (Box d)) (c: S → ℝ), f = ∑ B, (c B • (B.val.toSet).indicator')

/-- Theorem 1.3.20(ii) Approximation of $L^1$ functions by step functions -/

-- Helper: indicator of an elementary set gives a step function
private lemma elementary_indicator_is_step {d:ℕ} {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) : RealStepFunction E.indicator' := by
  obtain ⟨T, hT_disj, hE_eq⟩ := hE.partition
  refine ⟨T, fun _ => 1, ?_⟩
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  rw [hE_eq]
  by_cases hx : x ∈ ⋃ B ∈ T, B.toSet
  · rw [Set.indicator'_of_mem hx]
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨B, hB_mem, hx_mem⟩ := hx
    have : ∑ B : T, (B.val.toSet).indicator' x = 1 := by
      rw [Finset.sum_eq_single ⟨B, hB_mem⟩]
      · exact Set.indicator'_of_mem hx_mem
      · intro ⟨B', hB'_mem⟩ _ hne
        apply Set.indicator'_of_notMem
        intro hx_B'
        have hBB' : B ≠ B' := fun h => hne (Subtype.ext h.symm)
        exact Set.disjoint_left.mp
          (hT_disj (Finset.mem_coe.mpr hB_mem) (Finset.mem_coe.mpr hB'_mem) hBB')
          hx_mem hx_B'
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]
  · rw [Set.indicator'_of_notMem hx]
    symm; apply Finset.sum_eq_zero
    intro ⟨B, hB_mem⟩ _
    apply Set.indicator'_of_notMem
    intro hx_mem
    exact hx (Set.mem_iUnion₂.mpr ⟨B, hB_mem, hx_mem⟩)

-- Helper: step functions are closed under scalar multiplication
private lemma RealStepFunction.smul' {d:ℕ} {f : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) (a : ℝ) : RealStepFunction (a • f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  exact ⟨S, fun B => a * c B, by
    rw [hf_eq]; ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext B; rw [mul_assoc]⟩

-- Helper: step functions are closed under addition
private lemma RealStepFunction.add' {d:ℕ} {f g : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) (hg : RealStepFunction g) : RealStepFunction (f + g) := by
  obtain ⟨S₁, c₁, hf_eq⟩ := hf
  obtain ⟨S₂, c₂, hg_eq⟩ := hg
  refine ⟨S₁ ∪ S₂, fun B =>
    (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) +
    (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0), ?_⟩
  -- Rewrite f as sum over S₁ ∪ S₂ (extending c₁ by 0 outside S₁)
  have hf_union : ∀ x, (∑ B : ↥S₁, c₁ B • (B.val.toSet).indicator') x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) •
        (B.val.toSet).indicator') x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Embed S₁ into S₁ ∪ S₂
    set ι : ↥S₁ → ↥(S₁ ∪ S₂) :=
      fun B => ⟨B.val, Finset.mem_union_left S₂ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    -- The sum over S₁ ∪ S₂ restricts to S₁
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) * (B.val.toSet).indicator' x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₁ := by
        intro hB₁
        exact hni ⟨⟨B, hB₁⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    -- Show the filter equals the image of univ under ι
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl
    intro ⟨B, hB⟩ _
    simp only [ι, hB, dite_true]
  have hg_union : ∀ x, (∑ B : ↥S₂, c₂ B • (B.val.toSet).indicator') x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) •
        (B.val.toSet).indicator') x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₂ → ↥(S₁ ∪ S₂) :=
      fun B => ⟨B.val, Finset.mem_union_right S₁ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) * (B.val.toSet).indicator' x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₂ := by
        intro hB₂
        exact hni ⟨⟨B, hB₂⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl
    intro ⟨B, hB⟩ _
    simp only [ι, hB, dite_true]
  ext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf_eq, hg_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ B : ↥S₁, c₁ B * (B.val.toSet).indicator' x) =
      (∑ B : ↥S₁, c₁ B • (B.val.toSet).indicator') x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [show (∑ B : ↥S₂, c₂ B * (B.val.toSet).indicator' x) =
      (∑ B : ↥S₂, c₂ B • (B.val.toSet).indicator') x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [hf_union x, hg_union x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← add_mul, ← Finset.sum_add_distrib]

-- Helper: lift a real step function to a complex step function
private lemma RealStepFunction.toComplexStep {d:ℕ} {f : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) : ComplexStepFunction (Real.complex_fun f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  refine ⟨S, fun B => ↑(c B), ?_⟩
  ext x
  simp only [Real.complex_fun, Complex.indicator, hf_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Complex.ofReal_sum]
  congr 1; ext B
  exact Complex.ofReal_mul (c B) ((B.val.toSet).indicator' x)

-- Helper: complex step functions are closed under addition
private lemma ComplexStepFunction.add {d:ℕ} {f g : EuclideanSpace' d → ℂ}
    (hf : ComplexStepFunction f) (hg : ComplexStepFunction g) :
    ComplexStepFunction (f + g) := by
  obtain ⟨S₁, c₁, hf_eq⟩ := hf
  obtain ⟨S₂, c₂, hg_eq⟩ := hg
  refine ⟨S₁ ∪ S₂, fun B =>
    (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) +
    (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0), ?_⟩
  -- Extend f-sum from S₁ to S₁ ∪ S₂
  have hf_union : ∀ x, (∑ B : ↥S₁, c₁ B • Complex.indicator (B.val.toSet)) x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) •
        Complex.indicator (B.val.toSet)) x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₁ → ↥(S₁ ∪ S₂) := fun B => ⟨B.val, Finset.mem_union_left S₂ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) * Complex.indicator (B.val.toSet) x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₁ := by intro hB₁; exact hni ⟨⟨B, hB₁⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl; intro ⟨B, hB⟩ _; simp only [ι, hB, dite_true]
  -- Extend g-sum from S₂ to S₁ ∪ S₂
  have hg_union : ∀ x, (∑ B : ↥S₂, c₂ B • Complex.indicator (B.val.toSet)) x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) •
        Complex.indicator (B.val.toSet)) x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₂ → ↥(S₁ ∪ S₂) := fun B => ⟨B.val, Finset.mem_union_right S₁ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) * Complex.indicator (B.val.toSet) x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₂ := by intro hB₂; exact hni ⟨⟨B, hB₂⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl; intro ⟨B, hB⟩ _; simp only [ι, hB, dite_true]
  ext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf_eq, hg_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ B : ↥S₁, c₁ B * Complex.indicator (B.val.toSet) x) =
      (∑ B : ↥S₁, c₁ B • Complex.indicator (B.val.toSet)) x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [show (∑ B : ↥S₂, c₂ B * Complex.indicator (B.val.toSet) x) =
      (∑ B : ↥S₂, c₂ B • Complex.indicator (B.val.toSet)) x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [hf_union x, hg_union x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← add_mul, ← Finset.sum_add_distrib]

-- Helper: complex step functions are closed under scalar multiplication
private lemma ComplexStepFunction.smul {d:ℕ} {f : EuclideanSpace' d → ℂ}
    (hf : ComplexStepFunction f) (a : ℂ) : ComplexStepFunction (a • f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  exact ⟨S, fun B => a * c B, by
    rw [hf_eq]; ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext B; rw [mul_assoc]⟩

-- Helper: the zero function is real absolutely integrable
private lemma RealAbsolutelyIntegrable.zero_fun {d:ℕ} :
    RealAbsolutelyIntegrable (0 : EuclideanSpace' d → ℝ) := by
  constructor
  · exact ⟨fun _ => 0, fun _ => ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩,
      fun _ => tendsto_const_nhds⟩
  · have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℝ) = 0 := by
      funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
    rw [h_zero, UnsignedLebesgueIntegral]
    have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    calc h_simple.integ = 0 := UnsignedSimpleFunction.integ_zero
      _ < ⊤ := EReal.zero_lt_top

-- Helper: PreL1.norm of zero ≤ any nonneg EReal value
private lemma PreL1.norm_zero_le {d:ℕ} {a : EReal} (ha : 0 ≤ a) :
    PreL1.norm (0 : EuclideanSpace' d → ℝ) ≤ a := by
  unfold PreL1.norm
  have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℝ) = 0 := by
    funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
  rw [h_zero, UnsignedLebesgueIntegral]
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple,
    UnsignedSimpleFunction.integ_zero]
  exact ha

-- Helper: smul indicator is absolutely integrable when support has finite measure
private lemma RealAbsolutelyIntegrable.smul_indicator {d:ℕ}
    {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E)
    (c : ℝ) (hfin : c ≠ 0 → Lebesgue_measure E < ⊤) :
    RealAbsolutelyIntegrable (c • E.indicator') := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul]; exact RealAbsolutelyIntegrable.zero_fun
  · have h_simple : RealSimpleFunction (c • E.indicator') :=
      ⟨1, fun _ => c, fun _ => E, fun _ => hE, by
        ext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_one]⟩
    exact h_simple.absolutelyIntegrable_iff'.mp (h_simple.absolutelyIntegrable_iff.mpr (by
      calc Lebesgue_measure (Support (c • E.indicator'))
          ≤ Lebesgue_outer_measure E := Lebesgue_outer_measure.mono (fun x hx => by
            rw [Support, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hx
            by_contra h_not
            exact hx (by rw [Set.indicator'_of_notMem h_not, mul_zero]))
        _ < ⊤ := hfin hc))

-- Helper: PreL1.norm of scalar * indicator of symmDiff
private lemma PreL1.norm_smul_indicator_symmDiff_le {d:ℕ}
    {E F : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) (hF : LebesgueMeasurable F)
    (c : ℝ) :
    PreL1.norm (c • E.indicator' - c • F.indicator') ≤
      ↑(|c|) * Lebesgue_outer_measure (symmDiff E F) := by
  have hSD : LebesgueMeasurable (symmDiff E F) :=
    (hE.inter hF.complement).union (hF.inter hE.complement)
  have hSD_simple := UnsignedSimpleFunction.indicator hSD
  have hc_nn : (Real.toEReal |c|) ≥ 0 := by exact_mod_cast abs_nonneg c
  have h_simple := hSD_simple.smul hc_nn
  -- Pointwise: |c * indicator'_E(x) - c * indicator'_F(x)| = |c| * indicator'_{E△F}(x)
  have h_pw : EReal.abs_fun (c • E.indicator' - c • F.indicator') =
      (Real.toEReal |c|) • (Real.toEReal ∘ (symmDiff E F).indicator') := by
    funext x
    simp only [EReal.abs_fun, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp]
    by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;>
      simp [symmDiff_def, hxE, hxF]
  -- Compute: ∫|f| = |c| • ∫indicator(E△F) = |c| * μ(E△F)
  unfold PreL1.norm UnsignedLebesgueIntegral
  rw [h_pw, LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple,
    UnsignedSimpleFunction.integral_smul hSD_simple hc_nn,
    UnsignedSimpleFunction.integral_indicator hSD]
  unfold Lebesgue_measure; exact le_refl _

-- Helper: triangle inequality for PreL1.norm
private lemma PreL1.norm_sub_le_add {d:ℕ} {f g h : EuclideanSpace' d → ℝ}
    (hfg_ai : RealAbsolutelyIntegrable (f - g))
    (hgh_ai : RealAbsolutelyIntegrable (g - h))
    (hfg : PreL1.norm (f - g) ≤ a) (hgh : PreL1.norm (g - h) ≤ b) :
    PreL1.norm (f - h) ≤ a + b := by
  -- Key: f - h = (f - g) + (g - h), so |f-h| ≤ |f-g| + |g-h| pointwise
  have h_eq : f - h = (f - g) + (g - h) := by ext x; simp [Pi.sub_apply]
  have hfh_ai : RealAbsolutelyIntegrable (f - h) := h_eq ▸ hfg_ai.add hgh_ai
  have h_le : ∀ x, EReal.abs_fun (f - h) x ≤
      (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) x := fun x => by
    rw [h_eq]
    simp only [EReal.abs_fun, Pi.add_apply]
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (norm_add_le ((f - g) x) ((g - h) x))
  have hfg_abs := RealAbsolutelyIntegrable.abs _ hfg_ai
  have hgh_abs := RealAbsolutelyIntegrable.abs _ hgh_ai
  have hfh_abs := RealAbsolutelyIntegrable.abs _ hfh_ai
  -- Monotonicity: ∫|f-h| ≤ ∫(|f-g| + |g-h|)
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - h)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) :=
    LowerUnsignedLebesgueIntegral.mono hfh_abs.1 (hfg_abs.1.add hgh_abs.1)
      (AlmostAlways.ofAlways h_le)
  -- Additivity: ∫(|f-g| + |g-h|) = ∫|f-g| + ∫|g-h|
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) =
      UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + UnsignedLebesgueIntegral (EReal.abs_fun (g - h)) :=
    LowerUnsignedLebesgueIntegral.add hfg_abs.1 hgh_abs.1 (hfg_abs.1.add hgh_abs.1)
  -- Combine
  unfold PreL1.norm at hfg hgh ⊢
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - h))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (g - h)) := by rw [← h_add]; exact h_mono
    _ ≤ a + b := add_le_add hfg hgh

-- Main helper: every absolutely integrable simple function can be approximated by a step function
private lemma RealSimpleFunction.approx_by_step_aux {d:ℕ} {g : EuclideanSpace' d → ℝ}
    (hg_simple : RealSimpleFunction g) (hg_ai : RealAbsolutelyIntegrable g)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (h : EuclideanSpace' d → ℝ), RealStepFunction h ∧ RealAbsolutelyIntegrable h ∧
      PreL1.norm (g - h) ≤ δ := by
  obtain ⟨k, c, E, hE_meas, hg_eq⟩ := hg_simple
  by_cases hk : k = 0
  · subst hk
    have hg_zero : g = 0 := by rw [hg_eq]; funext x; simp [Finset.univ_eq_empty]
    refine ⟨0, ?_, RealAbsolutelyIntegrable.zero_fun, ?_⟩
    · exact ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
    · rw [hg_zero, sub_zero]
      exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  · -- Case k ≠ 0: use disjoint representation and approximate each atom
    -- Step 1: Get disjoint representation of g
    have hg_simple' : RealSimpleFunction g := ⟨k, c, E, hE_meas, hg_eq⟩
    obtain ⟨n, v, A, hA_meas, hA_disj, hg_eq'⟩ := hg_simple'.disjoint_representation
    -- Step 2: Show Lebesgue_measure (Support g) < ⊤
    have hg_abs_int : hg_simple'.AbsolutelyIntegrable :=
      hg_simple'.absolutelyIntegrable_iff'.mpr hg_ai
    have hg_support_fin : Lebesgue_measure (Support g) < ⊤ :=
      hg_simple'.absolutelyIntegrable_iff.mp hg_abs_int
    -- Step 3: For each j with v j ≠ 0, A j ⊆ Support g, hence finite measure
    have hA_sub_support : ∀ j, v j ≠ 0 → A j ⊆ Support g := by
      intro j hvj x hx
      rw [Support, Set.mem_setOf_eq, hg_eq']
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · exact mul_ne_zero hvj (Set.indicator'_of_mem hx ▸ one_ne_zero)
      · intro i _ hij
        rw [Set.indicator'_of_notMem]
        · ring
        · intro hxi
          exact absurd hxi (Set.disjoint_left.mp
            (hA_disj (Set.mem_univ j) (Set.mem_univ i) (Ne.symm hij)) hx)
      · intro h; exact absurd (Finset.mem_univ j) h
    have hA_fin : ∀ j, v j ≠ 0 → Lebesgue_measure (A j) < ⊤ := by
      intro j hvj
      calc Lebesgue_measure (A j)
          ≤ Lebesgue_outer_measure (Support g) := Lebesgue_outer_measure.mono (hA_sub_support j hvj)
        _ < ⊤ := hg_support_fin
    -- Handle n = 0 separately (g = 0 in this case)
    by_cases hn : n = 0
    · -- If n = 0, g = 0, so h = 0 works
      have hg_zero : g = 0 := by
        rw [hg_eq']; subst hn; funext x; simp [Finset.univ_eq_empty]
      refine ⟨0, ?_, RealAbsolutelyIntegrable.zero_fun, ?_⟩
      · exact ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
      · rw [hg_zero, sub_zero]
        exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
    -- Step 4: n ≠ 0, choose elementary approximations for each A j
    · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      -- For each j with v j ≠ 0, use TFAE to get elementary F j with small symmDiff
      have hε_j : ∀ j : Fin n, 0 < δ / (↑n * (|v j| + 1)) := by
        intro j; apply div_pos hδ
        exact mul_pos hn_pos (by linarith [abs_nonneg (v j)])
      have hF_exists : ∀ j : Fin n, ∃ F : Set (EuclideanSpace' d),
          IsElementary F ∧
          (v j ≠ 0 → Lebesgue_outer_measure (symmDiff F (A j)) ≤
            ↑(δ / (↑n * (|v j| + 1)))) := by
        intro j
        by_cases hvj : v j = 0
        · exact ⟨∅, IsElementary.empty d, fun h => absurd hvj h⟩
        · have h_tfae := (LebesgueMeasurable.finite_TFAE (A j)).out 0 7
          have h_approx := h_tfae.mp ⟨hA_meas j, hA_fin j hvj⟩
          obtain ⟨F, hF_elem, hF_bound⟩ :=
            h_approx (↑(δ / (↑n * (|v j| + 1))))
              (EReal.coe_pos.mpr (hε_j j))
          exact ⟨F, hF_elem, fun _ => hF_bound⟩
      choose F hF_elem hF_bound using hF_exists
      -- Step 5: Define h = ∑ j : Fin n, v j • (F j).indicator'
      set h : EuclideanSpace' d → ℝ := ∑ j : Fin n, v j • (F j).indicator' with hh_def
      -- Each F j is elementary, so Lebesgue_outer_measure (F j) < ⊤
      have hF_fin : ∀ j : Fin n, Lebesgue_outer_measure (F j) < ⊤ := by
        intro j
        rw [Lebesgue_outer_measure.elementary (F j) (hF_elem j)]
        exact EReal.coe_lt_top _
      refine ⟨h, ?_, ?_, ?_⟩
      -- Step 6: h is a step function (by Finset induction)
      · rw [hh_def]; exact Finset.sum_induction _
          (fun f => RealStepFunction f)
          (fun f g hf hg => RealStepFunction.add' hf hg)
          ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
          (fun j _ => RealStepFunction.smul'
            (elementary_indicator_is_step (hF_elem j)) (v j))
      -- Step 7: h is absolutely integrable
      · have hh_simple : RealSimpleFunction h :=
          ⟨n, v, fun j => F j,
           fun j => Jordan_measurable.lebesgue
             (IsElementary.jordanMeasurable (hF_elem j)),
           by rw [hh_def]⟩
        exact hh_simple.absolutelyIntegrable_iff'.mp
          ((hh_simple.absolutelyIntegrable_iff).mpr (by
            have h_support_sub : Support h ⊆ ⋃ j : Fin n, F j := by
              intro x hx
              rw [Support, Set.mem_setOf_eq] at hx
              rw [Set.mem_iUnion]
              by_contra h_not; push_neg at h_not; apply hx
              rw [hh_def]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
              exact Finset.sum_eq_zero fun j _ =>
                by rw [Set.indicator'_of_notMem (h_not j)]; ring
            calc Lebesgue_measure (Support h)
                ≤ Lebesgue_outer_measure (⋃ j : Fin n, F j) :=
                  Lebesgue_outer_measure.mono h_support_sub
              _ ≤ ∑ j : Fin n, Lebesgue_outer_measure (F j) :=
                  Lebesgue_outer_measure.finite_union_le F
              _ < ⊤ := by
                  have : ∀ j : Fin n, Lebesgue_outer_measure (F j) =
                      ↑((hF_elem j).measure) :=
                    fun j => Lebesgue_outer_measure.elementary (F j) (hF_elem j)
                  simp_rw [this]
                  rw [← EReal.coe_finset_sum
                    (fun j _ => IsElementary.measure_nonneg (hF_elem j))]
                  exact EReal.coe_lt_top _))
      -- Step 8: Bound PreL1.norm (g - h) ≤ δ via induction on Finset
      · have hgh_eq : g - h = ∑ j : Fin n, (v j • (A j).indicator' - v j • (F j).indicator') := by
          rw [hg_eq', hh_def, ← Finset.sum_sub_distrib]
        suffices h_bound : ∀ (S : Finset (Fin n)),
            RealAbsolutelyIntegrable (∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator')) ∧
            PreL1.norm (∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator'))
            ≤ ∑ j ∈ S, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))) by
          rw [hgh_eq]
          have h1 := (h_bound Finset.univ).2
          calc PreL1.norm (∑ j : Fin n, (v j • (A j).indicator' - v j • (F j).indicator'))
              ≤ ∑ j : Fin n, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))) := h1
            _ ≤ ∑ j : Fin n, (↑(δ / ↑n) : EReal) := by
                apply Finset.sum_le_sum
                intro j _
                by_cases hvj : v j = 0
                · simp [hvj]
                  exact le_of_lt (div_pos hδ hn_pos)
                · have h_symmDiff := hF_bound j hvj
                  rw [symmDiff_comm] at h_symmDiff
                  calc ↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))
                      ≤ ↑(|v j|) * ↑(δ / (↑n * (|v j| + 1))) :=
                        mul_le_mul_of_nonneg_left h_symmDiff
                          (EReal.coe_nonneg.mpr (abs_nonneg _))
                    _ = ↑(|v j| * (δ / (↑n * (|v j| + 1)))) := by
                        rw [← EReal.coe_mul]
                    _ ≤ ↑(δ / ↑n) := by
                        rw [EReal.coe_le_coe_iff]
                        have hab : 0 < |v j| + 1 := by linarith [abs_nonneg (v j)]
                        calc |v j| * (δ / (↑n * (|v j| + 1)))
                            = |v j| * δ / (↑n * (|v j| + 1)) := by ring
                          _ ≤ (|v j| + 1) * δ / (↑n * (|v j| + 1)) := by
                              apply div_le_div_of_nonneg_right
                              · exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
                              · exact (mul_pos hn_pos hab).le
                          _ = δ / ↑n := by
                              rw [mul_comm (|v j| + 1) δ, mul_div_mul_right _ _
                                (ne_of_gt hab)]
            _ = ↑δ := by
                rw [← EReal.coe_finset_sum (fun _ _ => le_of_lt (div_pos hδ hn_pos))]
                congr 1
                rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
                    mul_div_cancel₀ δ (Nat.cast_ne_zero.mpr hn)]
        -- Each term v j • (A j).indicator' - v j • (F j).indicator' is absolutely integrable
        have hterm_ai : ∀ j : Fin n, RealAbsolutelyIntegrable
            (v j • (A j).indicator' - v j • (F j).indicator') := fun j =>
          (RealAbsolutelyIntegrable.smul_indicator (hA_meas j) (v j) (hA_fin j)).sub
            (RealAbsolutelyIntegrable.smul_indicator
              (Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (hF_elem j)))
              (v j) (fun _ => hF_fin j))
        -- Prove the suffices: induction on S
        intro S
        induction S using Finset.induction with
        | empty =>
          simp only [Finset.sum_empty]
          exact ⟨RealAbsolutelyIntegrable.zero_fun, PreL1.norm_zero_le le_rfl⟩
        | @insert a S haS ih =>
          rw [Finset.sum_insert haS, Finset.sum_insert haS]
          have h_single := PreL1.norm_smul_indicator_symmDiff_le (hA_meas a)
            (Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (hF_elem a))) (v a)
          set f_a := v a • (A a).indicator' - v a • (F a).indicator'
          set sum_S := ∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator')
          have hfa_ai : RealAbsolutelyIntegrable f_a := hterm_ai a
          have hsum_ai : RealAbsolutelyIntegrable sum_S := ih.1
          -- Triangle inequality via PreL1.norm_sub_le_add
          have h_eq1 : f_a + sum_S - sum_S = f_a := by
            ext x; simp [f_a, sum_S, Pi.add_apply, Pi.sub_apply]
          have h_eq2 : sum_S - 0 = sum_S := by ext x; simp
          have h_eq3 : f_a + sum_S - 0 = f_a + sum_S := by ext x; simp
          have h_triangle : PreL1.norm (f_a + sum_S) ≤
              PreL1.norm f_a + PreL1.norm sum_S := by
            have hfg : PreL1.norm ((f_a + sum_S) - sum_S) ≤ PreL1.norm f_a := by
              rw [show (f_a + sum_S) - sum_S = f_a from h_eq1]
            have hgh : PreL1.norm (sum_S - 0) ≤ PreL1.norm sum_S := by
              rw [show sum_S - 0 = sum_S from h_eq2]
            have hfg_ai' : RealAbsolutelyIntegrable ((f_a + sum_S) - sum_S) := by
              rw [show (f_a + sum_S) - sum_S = f_a from h_eq1]; exact hfa_ai
            have hgh_ai' : RealAbsolutelyIntegrable (sum_S - 0) := by
              rw [show sum_S - 0 = sum_S from h_eq2]; exact hsum_ai
            calc PreL1.norm (f_a + sum_S)
                = PreL1.norm ((f_a + sum_S) - 0) := by congr 1; exact h_eq3.symm
              _ ≤ PreL1.norm f_a + PreL1.norm sum_S :=
                  PreL1.norm_sub_le_add hfg_ai' hgh_ai' hfg hgh
          constructor
          · exact hfa_ai.add hsum_ai
          · calc PreL1.norm (f_a + sum_S)
                ≤ PreL1.norm f_a + PreL1.norm sum_S := h_triangle
              _ ≤ (↑(|v a|) * Lebesgue_outer_measure (symmDiff (A a) (F a))) +
                  (∑ j ∈ S, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j)))) :=
                  add_le_add h_single ih.2

theorem RealAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), RealStepFunction g ∧ RealAbsolutelyIntegrable g ∧
        PreL1.norm (f - g) ≤ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g₁, hg₁_simple, hg₁_ai, hg₁_norm⟩ := hf.approx_by_simple (ε / 2) hε2
  obtain ⟨g₂, hg₂_step, hg₂_ai, hg₂_norm⟩ :=
    RealSimpleFunction.approx_by_step_aux hg₁_simple hg₁_ai (ε / 2) hε2
  refine ⟨g₂, hg₂_step, hg₂_ai, ?_⟩
  have h_combined := PreL1.norm_sub_le_add (hf.sub hg₁_ai) (hg₁_ai.sub hg₂_ai) hg₁_norm hg₂_norm
  calc PreL1.norm (f - g₂) ≤ ↑(ε / 2) + ↑(ε / 2) := h_combined
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

theorem ComplexAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexStepFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Approximate real and imaginary parts within ε/2
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g_re, hg_re_step, hg_re_ai, hg_re_norm⟩ :=
    (ComplexAbsolutelyIntegrable.re f hf).approx_by_step (ε / 2) hε2
  obtain ⟨g_im, hg_im_step, hg_im_ai, hg_im_norm⟩ :=
    (ComplexAbsolutelyIntegrable.im f hf).approx_by_step (ε / 2) hε2
  -- Construct complex approximation g = ↑g_re + I • ↑g_im
  set g : EuclideanSpace' d → ℂ :=
    Real.complex_fun g_re + Complex.I • Real.complex_fun g_im with hg_def
  have hg_re_eq : Complex.re_fun g = g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hg_im_eq : Complex.im_fun g = g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  -- g is a complex step function
  have hg_step : ComplexStepFunction g :=
    ComplexStepFunction.add
      (RealStepFunction.toComplexStep hg_re_step)
      (ComplexStepFunction.smul (RealStepFunction.toComplexStep hg_im_step) Complex.I)
  -- g is absolutely integrable
  have hg_ai : ComplexAbsolutelyIntegrable g := by
    apply (ComplexAbsolutelyIntegrable.iff g).mpr
    exact ⟨hg_re_eq ▸ hg_re_ai, hg_im_eq ▸ hg_im_ai⟩
  refine ⟨g, hg_step, hg_ai, ?_⟩
  -- Norm bound: PreL1.norm (f - g) ≤ ε
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  have hfg_re : Complex.re_fun (f - g) = Complex.re_fun f - g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hfg_im : Complex.im_fun (f - g) = Complex.im_fun f - g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  have h_bound : ∀ x, EReal.abs_fun (f - g) x ≤
      (EReal.abs_fun (Complex.re_fun (f - g)) + EReal.abs_fun (Complex.im_fun (f - g))) x :=
    fun x => by
      simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by
        calc ‖(f - g) x‖ ≤ |((f - g) x).re| + |((f - g) x).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = ‖((f - g) x).re‖ + ‖((f - g) x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  have hfg_ai := hf.sub hg_ai
  have hfg_re_ai := ComplexAbsolutelyIntegrable.re (f - g) hfg_ai
  have hfg_im_ai := ComplexAbsolutelyIntegrable.im (f - g) hfg_ai
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
                                EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.mono hfg_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1) (AlmostAlways.ofAlways h_bound)
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
      EReal.abs_fun (Complex.im_fun (f - g))) =
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g))) +
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.add hfg_re_ai.abs.1 hfg_im_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1)
  rw [h_add] at h_mono
  rw [show EReal.abs_fun (Complex.re_fun (f - g)) =
        EReal.abs_fun (Complex.re_fun f - g_re) from by rw [hfg_re],
      show EReal.abs_fun (Complex.im_fun (f - g)) =
        EReal.abs_fun (Complex.im_fun f - g_im) from by rw [hfg_im]] at h_mono
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f - g_re)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f - g_im)) := h_mono
    _ ≤ (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) := add_le_add hg_re_norm hg_im_norm
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

def CompactlySupported {X Y:Type*} [TopologicalSpace X] [Zero Y] (f: X → Y) : Prop :=
  ∃ (K: Set X), IsCompact K ∧ ∀ x, x ∉ K → f x = 0

-- Helper: approximate a scaled box indicator by a continuous compactly supported function
private lemma Box.scaled_indicator_approx_continuous {d:ℕ} (B : Box d) (c : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
      RealAbsolutelyIntegrable g ∧ PreL1.norm (c • B.toSet.indicator' - g) ≤ δ := by
  -- Case 1: c = 0, then g = 0 works
  by_cases hc : c = 0
  · refine ⟨0, continuous_const, ⟨∅, isCompact_empty, fun x _ => rfl⟩,
      RealAbsolutelyIntegrable.zero_fun, ?_⟩
    have : c • B.toSet.indicator' - (0 : EuclideanSpace' d → ℝ) = 0 := by
      ext x; simp [hc]
    rw [this]
    exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  -- Case 2: c ≠ 0
  · -- B.toSet is elementary, hence Lebesgue measurable with finite measure
    have hB_elem : IsElementary B.toSet := IsElementary.box B
    have hB_meas : LebesgueMeasurable B.toSet :=
      Jordan_measurable.lebesgue (IsElementary.jordanMeasurable hB_elem)
    have hB_fin : Lebesgue_measure B.toSet < ⊤ := by
      unfold Lebesgue_measure
      rw [Lebesgue_outer_measure.elementary B.toSet hB_elem]
      exact EReal.coe_lt_top _
    -- Choose ε₀ = δ / (2 * |c|) > 0
    have hc_abs_pos : 0 < |c| := abs_pos.mpr hc
    set ε₀ : ℝ := δ / (2 * |c|) with hε₀_def
    have hε₀ : 0 < ε₀ := div_pos hδ (mul_pos two_pos hc_abs_pos)
    -- Get compact K ⊆ B.toSet with measure(B.toSet \ K) ≤ ε₀
    have h_tfae_03 := (LebesgueMeasurable.finite_TFAE B.toSet).out 0 3
    obtain ⟨K, hK_compact, hK_sub, hK_bound⟩ :=
      h_tfae_03.mp ⟨hB_meas, hB_fin⟩ (↑ε₀) (EReal.coe_pos.mpr hε₀)
    -- Get open U ⊇ B.toSet with measure(U \ B.toSet) ≤ ε₀ and finite measure
    have h_tfae_01 := (LebesgueMeasurable.finite_TFAE B.toSet).out 0 1
    obtain ⟨U, hU_open, hB_sub_U, hU_fin, hU_diff_bound⟩ :=
      h_tfae_01.mp ⟨hB_meas, hB_fin⟩ (↑ε₀) (EReal.coe_pos.mpr hε₀)
    -- K ⊆ U (since K ⊆ B.toSet ⊆ U)
    have hKU : K ⊆ U := hK_sub.trans hB_sub_U
    -- K and Uᶜ are disjoint
    have hKU_disj : Disjoint K Uᶜ :=
      Set.disjoint_compl_right_iff_subset.mpr hKU
    -- Apply Urysohn: get continuous φ with HasCompactSupport, φ=1 on K, φ=0 outside U
    obtain ⟨φ, hφ_one, hφ_zero, hφ_cs, hφ_range⟩ :=
      exists_continuous_one_zero_of_isCompact hK_compact hU_open.isClosed_compl hKU_disj
    -- Define g = c • φ
    set g : EuclideanSpace' d → ℝ := fun x => c * φ x with hg_def
    -- Set up notation for the difference
    set diff : EuclideanSpace' d → ℝ := c • B.toSet.indicator' - g with hdiff_def
    -- Key properties of φ
    have hφ_zero' : ∀ x, x ∉ U → φ x = 0 := by
      intro x hxU
      have := hφ_zero (show x ∈ Uᶜ from hxU)
      simp at this; exact this
    -- Pointwise bound: |diff(x)| ≤ |c| and diff = 0 outside U
    have hdiff_bound : ∀ x, ‖diff x‖ ≤ |c| := by
      intro x
      simp only [diff, hdiff_def, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hφ_bdd := hφ_range x
      rw [show c * B.toSet.indicator' x - c * φ x = c * (B.toSet.indicator' x - φ x) by ring]
      rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_of_le_one_right (abs_nonneg c)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · by_cases hxB : x ∈ B.toSet
        · rw [Set.indicator'_of_mem hxB]; linarith [hφ_bdd.2]
        · rw [Set.indicator'_of_notMem hxB]; linarith [hφ_bdd.2]
      · by_cases hxB : x ∈ B.toSet
        · rw [Set.indicator'_of_mem hxB]; linarith [hφ_bdd.1]
        · rw [Set.indicator'_of_notMem hxB]; linarith [hφ_bdd.1]
    have hdiff_support : ∀ x, x ∉ U → diff x = 0 := by
      intro x hxU
      simp only [diff, hdiff_def, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Set.indicator'_of_notMem (fun h => hxU (hB_sub_U h)), mul_zero,
        hφ_zero' x hxU, mul_zero, sub_self]
    -- Measurability
    have hg_meas : RealMeasurable g :=
      (continuous_const.mul φ.continuous).RealMeasurable
    have hcB_ai : RealAbsolutelyIntegrable (c • B.toSet.indicator') :=
      RealAbsolutelyIntegrable.smul_indicator hB_meas c (fun _ => hB_fin)
    have hdiff_meas : RealMeasurable diff := RealMeasurable.sub hcB_ai.1 hg_meas
    -- Measurability of sets involved
    have hBK_meas : LebesgueMeasurable (B.toSet \ K) :=
      hB_meas.inter (hK_compact.isClosed.measurable).complement
    have hUB_meas : LebesgueMeasurable (U \ B.toSet) :=
      (IsOpen.measurable hU_open).inter hB_meas.complement
    -- Key pointwise bound: |diff(x)| ≤ |c| * (1_{B\K}(x) + 1_{U\B}(x))
    -- Also: simpler bound |diff(x)| ≤ |c| * 1_U(x) for AI proof
    have h_pw_U : ∀ x, EReal.abs_fun diff x ≤
        ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) x := by
      intro x
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, Function.comp]
      by_cases hxU : x ∈ U
      · rw [Set.indicator'_of_mem hxU]
        have : Real.toEReal 1 = (1 : EReal) := rfl
        rw [this, mul_one]
        exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
      · rw [hdiff_support x hxU, norm_zero, Set.indicator'_of_notMem hxU]
        have : Real.toEReal 0 = (0 : EReal) := rfl
        rw [this, mul_zero]
    -- Tighter pointwise bound (for the norm bound)
    have h_pw_tight : ∀ x, EReal.abs_fun diff x ≤
        ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                (Real.toEReal ∘ (U \ B.toSet).indicator'))) x := by
      intro x
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, Function.comp, Pi.add_apply]
      by_cases hxK : x ∈ K
      · -- On K: diff = 0
        have hdx : diff x = 0 := by
          simp only [diff, hdiff_def, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have h1 := hφ_one hxK; simp only [Pi.one_apply] at h1
          rw [Set.indicator'_of_mem (hK_sub hxK), mul_one, h1, mul_one, sub_self]
        rw [hdx, norm_zero]
        apply mul_nonneg (EReal.coe_nonneg.mpr (abs_nonneg c))

        apply add_nonneg <;> exact EReal.coe_nonneg.mpr ((Set.indicator_nonneg (fun _ _ => zero_le_one) x))
      · by_cases hxB : x ∈ B.toSet
        · -- On B \ K: |diff| ≤ |c|, bound by |c| * 1
          rw [Set.indicator'_of_mem (show x ∈ B.toSet \ K from ⟨hxB, hxK⟩),
            Set.indicator'_of_notMem (show x ∉ U \ B.toSet from fun h => h.2 hxB)]
          have h0 : Real.toEReal 0 = (0 : EReal) := rfl
          have h1 : Real.toEReal 1 = (1 : EReal) := rfl
          rw [h1, h0, add_zero, mul_one]
          exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
        · by_cases hxU : x ∈ U
          · -- On U \ B: |diff| ≤ |c|, bound by |c| * 1
            rw [Set.indicator'_of_notMem (show x ∉ B.toSet \ K from fun h => hxB h.1),
              Set.indicator'_of_mem (show x ∈ U \ B.toSet from ⟨hxU, hxB⟩)]
            have h0 : Real.toEReal 0 = (0 : EReal) := rfl
            have h1 : Real.toEReal 1 = (1 : EReal) := rfl
            rw [h0, h1, zero_add, mul_one]
            exact EReal.coe_le_coe_iff.mpr (hdiff_bound x)
          · -- Outside U: diff = 0
            rw [hdiff_support x hxU, norm_zero]
            apply mul_nonneg (EReal.coe_nonneg.mpr (abs_nonneg c))
            apply add_nonneg <;> exact EReal.coe_nonneg.mpr ((Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    -- Derive AI for diff (using the U bound)
    have hU_meas : LebesgueMeasurable U := IsOpen.measurable hU_open
    have hU_simple := UnsignedSimpleFunction.indicator hU_meas
    have hc_nn : (Real.toEReal |c|) ≥ 0 := by exact_mod_cast abs_nonneg c
    have hdiff_abs_meas : UnsignedMeasurable (EReal.abs_fun diff) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := hdiff_meas
        exact ⟨fun n => EReal.abs_fun (g n), fun n => (hg_simple n).abs, fun x => by
          simp only [EReal.abs_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)⟩
    have hdiff_ai : RealAbsolutelyIntegrable diff := by
      constructor
      · exact hdiff_meas
      · have hbound_simple := hU_simple.smul hc_nn
        have hbound_meas := UnsignedSimpleFunction.unsignedMeasurable hbound_simple
        have h_mono := LowerUnsignedLebesgueIntegral.mono
          hdiff_abs_meas hbound_meas
          (AlmostAlways.ofAlways h_pw_U)
        have h_integ : LowerUnsignedLebesgueIntegral
            ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) =
            (Real.toEReal |c|) * Lebesgue_measure U := by
          rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hbound_simple,
            UnsignedSimpleFunction.integral_smul hU_simple hc_nn,
            UnsignedSimpleFunction.integral_indicator hU_meas]
        rw [UnsignedLebesgueIntegral]
        calc LowerUnsignedLebesgueIntegral (EReal.abs_fun diff)
            ≤ LowerUnsignedLebesgueIntegral
                ((Real.toEReal |c|) • (Real.toEReal ∘ U.indicator')) := h_mono
          _ = (Real.toEReal |c|) * Lebesgue_measure U := h_integ
          _ < ⊤ := by
              apply Ne.lt_top
              rw [EReal.mul_ne_top]
              exact ⟨Or.inl (EReal.coe_ne_bot _),
                Or.inl (le_of_lt (EReal.coe_pos.mpr hc_abs_pos)),
                Or.inl (EReal.coe_ne_top _),
                Or.inr (ne_of_lt hU_fin)⟩
    -- g = (c • B.toSet.indicator') - diff, so g is AI
    have hg_ai : RealAbsolutelyIntegrable g := by
      have : g = c • B.toSet.indicator' - diff := by
        ext x; simp [diff, hdiff_def, hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact hcB_ai.sub hdiff_ai
    refine ⟨g, ?_, ?_, hg_ai, ?_⟩
    -- g is continuous
    · exact continuous_const.mul φ.continuous
    -- g is compactly supported
    · refine ⟨tsupport φ, hφ_cs, fun x hx => ?_⟩
      simp only [hg_def]
      have : φ x = 0 := by
        by_contra h
        exact hx (subset_tsupport φ (Function.mem_support.mpr h))
      rw [this, mul_zero]
    -- PreL1.norm bound: PreL1.norm diff ≤ δ
    · -- Use the tight pointwise bound
      have hBK_simple := UnsignedSimpleFunction.indicator hBK_meas
      have hUB_simple := UnsignedSimpleFunction.indicator hUB_meas
      have hsum_simple : UnsignedSimpleFunction
          ((Real.toEReal ∘ (B.toSet \ K).indicator') +
           (Real.toEReal ∘ (U \ B.toSet).indicator')) :=
        UnsignedSimpleFunction.add hBK_simple hUB_simple
      have hbound_simple := hsum_simple.smul hc_nn
      have hbound_meas2 := UnsignedSimpleFunction.unsignedMeasurable hbound_simple
      have h_mono := LowerUnsignedLebesgueIntegral.mono
        hdiff_abs_meas hbound_meas2
        (AlmostAlways.ofAlways h_pw_tight)
      have h_integ_bound : LowerUnsignedLebesgueIntegral
          ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                  (Real.toEReal ∘ (U \ B.toSet).indicator'))) =
          (Real.toEReal |c|) * (Lebesgue_measure (B.toSet \ K) +
                                 Lebesgue_measure (U \ B.toSet)) := by
        rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral hbound_simple,
          UnsignedSimpleFunction.integral_smul hsum_simple hc_nn]
        congr 1
        rw [← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hsum_simple,
          LowerUnsignedLebesgueIntegral.add
          (UnsignedSimpleFunction.unsignedMeasurable hBK_simple)
          (UnsignedSimpleFunction.unsignedMeasurable hUB_simple)
          (UnsignedSimpleFunction.unsignedMeasurable hsum_simple),
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hBK_simple,
          LowerUnsignedLebesgueIntegral.eq_simpleIntegral hUB_simple,
          UnsignedSimpleFunction.integral_indicator hBK_meas,
          UnsignedSimpleFunction.integral_indicator hUB_meas]
      unfold PreL1.norm UnsignedLebesgueIntegral
      calc LowerUnsignedLebesgueIntegral (EReal.abs_fun diff)
          ≤ LowerUnsignedLebesgueIntegral
              ((Real.toEReal |c|) • ((Real.toEReal ∘ (B.toSet \ K).indicator') +
                                      (Real.toEReal ∘ (U \ B.toSet).indicator'))) := h_mono
        _ = (Real.toEReal |c|) * (Lebesgue_measure (B.toSet \ K) +
                                   Lebesgue_measure (U \ B.toSet)) := h_integ_bound
        _ ≤ (Real.toEReal |c|) * (↑ε₀ + ↑ε₀) := by
            apply mul_le_mul_of_nonneg_left _ hc_nn.le
            unfold Lebesgue_measure
            exact add_le_add hK_bound hU_diff_bound
        _ = ↑δ := by
            rw [← EReal.coe_add, ← EReal.coe_mul]
            congr 1
            rw [hε₀_def]
            field_simp
            ring

-- Helper: a step function can be approximated by a continuous compactly supported function
private lemma RealStepFunction.approx_by_continuous_compact_aux {d:ℕ}
    {h : EuclideanSpace' d → ℝ} (hh : RealStepFunction h) (hh_ai : RealAbsolutelyIntegrable h)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
      RealAbsolutelyIntegrable g ∧ PreL1.norm (h - g) ≤ δ := by
  obtain ⟨S, c, hh_eq⟩ := hh
  -- Handle empty finset
  by_cases hS : S = ∅
  · have hh_zero : h = 0 := by
      subst hS; rw [hh_eq]; simp [Finset.univ_eq_empty]
    refine ⟨0, continuous_const, ⟨∅, isCompact_empty, fun x _ => rfl⟩,
      RealAbsolutelyIntegrable.zero_fun, ?_⟩
    rw [hh_zero, sub_zero]
    exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  -- S is nonempty
  · have hS_nonempty : S.Nonempty := Finset.nonempty_of_ne_empty hS
    have hS_card_pos : 0 < S.card := Finset.Nonempty.card_pos hS_nonempty
    have hS_card_pos_real : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS_card_pos
    -- Budget per box
    have hδ_per : 0 < δ / S.card := div_pos hδ hS_card_pos_real
    -- For each box B ∈ S, approximate c B • B.val.toSet.indicator' by continuous g_B
    have h_approx : ∀ B : S, ∃ (g_B : EuclideanSpace' d → ℝ),
        Continuous g_B ∧ CompactlySupported g_B ∧
        RealAbsolutelyIntegrable g_B ∧
        PreL1.norm (c B • B.val.toSet.indicator' - g_B) ≤ δ / S.card :=
      fun B => Box.scaled_indicator_approx_continuous B.val (c B) (δ / S.card) hδ_per
    choose g_B hg_cont hg_cs hg_ai hg_norm using h_approx
    -- Define g = ∑ B ∈ S, g_B
    set g : EuclideanSpace' d → ℝ := fun x => ∑ B : S, g_B B x with hg_def
    -- h - g = ∑ B ∈ S, (c B • B.val.toSet.indicator' - g_B B)
    have hfg_eq : h - g = fun x => ∑ B : S, (c B • B.val.toSet.indicator' - g_B B) x := by
      ext x
      simp only [Pi.sub_apply, hg_def, hh_eq, Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_sub_distrib]
    -- Each term is AI
    have hterm_ai : ∀ B : S,
        RealAbsolutelyIntegrable (c B • B.val.toSet.indicator' - g_B B) :=
      fun B => by
        have hB_meas : LebesgueMeasurable B.val.toSet :=
          Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (IsElementary.box B.val))
        have hB_fin : Lebesgue_measure B.val.toSet < ⊤ := by
          unfold Lebesgue_measure
          rw [Lebesgue_outer_measure.elementary B.val.toSet (IsElementary.box B.val)]
          exact EReal.coe_lt_top _
        exact (RealAbsolutelyIntegrable.smul_indicator hB_meas (c B) (fun _ => hB_fin)).sub
          (hg_ai B)
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    -- g is continuous
    · show Continuous g
      apply continuous_finset_sum
      intro B _
      exact hg_cont B
    -- g is compactly supported
    · obtain ⟨B₀, hB₀⟩ := hS_nonempty
      -- Each g_B has compact support K_B
      choose K hK_compact hK_support using fun B => (hg_cs B)
      refine ⟨⋃ B : S, K B, ?_, ?_⟩
      · exact isCompact_iUnion (fun B => (hK_compact B))
      · intro x hx
        rw [Set.mem_iUnion] at hx
        push_neg at hx
        simp only [hg_def]
        exact Finset.sum_eq_zero (fun B _ => hK_support B x (hx B))
    -- g is AI (sum of AI functions)
    · show RealAbsolutelyIntegrable g
      have hg_eq_sum : g = ∑ B : S, g_B B := by
        ext x; simp [hg_def]
      rw [hg_eq_sum]
      exact Finset.sum_induction _ RealAbsolutelyIntegrable
        (fun f g hf hg => hf.add hg) RealAbsolutelyIntegrable.zero_fun
        (fun B _ => hg_ai B)
    -- PreL1.norm (h - g) ≤ δ
    · -- Set up difference terms
      set diff_term : S → (EuclideanSpace' d → ℝ) :=
        fun B => c B • B.val.toSet.indicator' - g_B B with hdiff_term_def
      -- h - g = ∑ diff_term
      have hfg_eq' : h - g = ∑ B : S, diff_term B := by
        ext x
        simp only [Pi.sub_apply, hh_eq, hg_def, hdiff_term_def, Finset.sum_apply,
          Pi.smul_apply, Pi.sub_apply]
        rw [Finset.sum_sub_distrib]
      -- Prove by finset induction: AI of partial sum and norm bound
      suffices h_bound : ∀ (T : Finset S),
          RealAbsolutelyIntegrable (∑ B ∈ T, diff_term B) ∧
          PreL1.norm (∑ B ∈ T, diff_term B) ≤
          ∑ B ∈ T, PreL1.norm (diff_term B) by
        rw [hfg_eq']
        have h1 := (h_bound Finset.univ).2
        calc PreL1.norm (∑ B : S, diff_term B)
            ≤ ∑ B : S, PreL1.norm (diff_term B) := h1
          _ ≤ ∑ _B : S, (↑(δ / ↑S.card) : EReal) :=
              Finset.sum_le_sum (fun B _ => hg_norm B)
          _ = ↑δ := by
              rw [← EReal.coe_finset_sum (fun _ _ => le_of_lt hδ_per)]
              congr 1
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
                nsmul_eq_mul, mul_div_cancel₀ δ
                  (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hS_card_pos))]
      -- Prove the suffices by induction
      intro T
      induction T using Finset.induction with
      | empty =>
        simp only [Finset.sum_empty]
        exact ⟨RealAbsolutelyIntegrable.zero_fun, PreL1.norm_zero_le le_rfl⟩
      | @insert a T' haT ih =>
        rw [Finset.sum_insert haT, Finset.sum_insert haT]
        set f_a := diff_term a
        set sum_T := ∑ B ∈ T', diff_term B
        have hfa_ai : RealAbsolutelyIntegrable f_a := hterm_ai a
        have hsum_ai : RealAbsolutelyIntegrable sum_T := ih.1
        constructor
        · exact hfa_ai.add hsum_ai
        · -- Triangle inequality
          have h_eq1 : (f_a + sum_T) - sum_T = f_a := by
            ext x; simp [f_a, sum_T, Pi.add_apply, Pi.sub_apply]
          have h_eq2 : sum_T - 0 = sum_T := by ext x; simp
          have h_eq3 : (f_a + sum_T) - 0 = f_a + sum_T := by ext x; simp
          have hfg_ai' : RealAbsolutelyIntegrable ((f_a + sum_T) - sum_T) := by
            rw [h_eq1]; exact hfa_ai
          have hgh_ai' : RealAbsolutelyIntegrable (sum_T - 0) := by
            rw [h_eq2]; exact hsum_ai
          have hfg : PreL1.norm ((f_a + sum_T) - sum_T) ≤ PreL1.norm f_a := by rw [h_eq1]
          have hgh : PreL1.norm (sum_T - 0) ≤ PreL1.norm sum_T := by rw [h_eq2]
          calc PreL1.norm (f_a + sum_T)
              = PreL1.norm ((f_a + sum_T) - 0) := by congr 1; exact h_eq3.symm
            _ ≤ PreL1.norm f_a + PreL1.norm sum_T :=
                PreL1.norm_sub_le_add hfg_ai' hgh_ai' hfg hgh
            _ ≤ PreL1.norm f_a +
                ∑ B ∈ T', PreL1.norm (diff_term B) :=
                add_le_add le_rfl ih.2

/-- Theorem 1.3.20(iii) Approximation of $L^1$ functions by continuous compactly supported functions -/
theorem RealAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
        PreL1.norm (f - g) ≤ ε := by
  -- Step 1: approximate f by step function h
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨h, hh_step, hh_ai, hh_norm⟩ := hf.approx_by_step (ε / 2) hε2
  -- Step 4: approximate step function h by continuous compactly supported g
  obtain ⟨g, hg_cont, hg_cs, hg_ai, hg_norm⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_step hh_ai (ε / 2) hε2
  -- Step 5: combine via triangle inequality
  refine ⟨g, hg_cont, hg_cs, ?_⟩
  have h_combined := PreL1.norm_sub_le_add (hf.sub hh_ai) (hh_ai.sub hg_ai) hh_norm hg_norm
  calc PreL1.norm (f - g) ≤ ↑(ε / 2) + ↑(ε / 2) := h_combined
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

theorem ComplexAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), Continuous g ∧ CompactlySupported g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Approximate real and imaginary parts within ε/2
  -- Use internal aux helpers to also get RealAbsolutelyIntegrable
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε4 : 0 < ε / 2 / 2 := half_pos hε2
  -- Real part: step function approximation then continuous approximation
  obtain ⟨h_re, hh_re_step, hh_re_ai, hh_re_norm⟩ :=
    (ComplexAbsolutelyIntegrable.re f hf).approx_by_step (ε / 2 / 2) hε4
  obtain ⟨g_re, hg_re_cont, hg_re_cs, hg_re_ai, hg_re_norm'⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_re_step hh_re_ai (ε / 2 / 2) hε4
  have hg_re_norm : PreL1.norm (Complex.re_fun f - g_re) ≤ ↑(ε / 2) := by
    have := PreL1.norm_sub_le_add ((ComplexAbsolutelyIntegrable.re f hf).sub hh_re_ai)
      (hh_re_ai.sub hg_re_ai) hh_re_norm hg_re_norm'
    calc PreL1.norm (Complex.re_fun f - g_re)
        ≤ ↑(ε / 2 / 2) + ↑(ε / 2 / 2) := this
      _ = ↑(ε / 2) := by rw [← EReal.coe_add]; congr 1; linarith
  -- Imaginary part: step function approximation then continuous approximation
  obtain ⟨h_im, hh_im_step, hh_im_ai, hh_im_norm⟩ :=
    (ComplexAbsolutelyIntegrable.im f hf).approx_by_step (ε / 2 / 2) hε4
  obtain ⟨g_im, hg_im_cont, hg_im_cs, hg_im_ai, hg_im_norm'⟩ :=
    RealStepFunction.approx_by_continuous_compact_aux hh_im_step hh_im_ai (ε / 2 / 2) hε4
  have hg_im_norm : PreL1.norm (Complex.im_fun f - g_im) ≤ ↑(ε / 2) := by
    have := PreL1.norm_sub_le_add ((ComplexAbsolutelyIntegrable.im f hf).sub hh_im_ai)
      (hh_im_ai.sub hg_im_ai) hh_im_norm hg_im_norm'
    calc PreL1.norm (Complex.im_fun f - g_im)
        ≤ ↑(ε / 2 / 2) + ↑(ε / 2 / 2) := this
      _ = ↑(ε / 2) := by rw [← EReal.coe_add]; congr 1; linarith
  -- Construct complex approximation g = ↑g_re + I • ↑g_im
  set g : EuclideanSpace' d → ℂ :=
    Real.complex_fun g_re + Complex.I • Real.complex_fun g_im with hg_def
  have hg_re_eq : Complex.re_fun g = g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hg_im_eq : Complex.im_fun g = g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  -- g is continuous
  have hg_cont : Continuous g := by
    apply Continuous.add
    · exact Complex.continuous_ofReal.comp hg_re_cont
    · exact continuous_const.mul (Complex.continuous_ofReal.comp hg_im_cont)
  -- g is compactly supported
  have hg_cs : CompactlySupported g := by
    obtain ⟨K_re, hK_re_compact, hK_re_supp⟩ := hg_re_cs
    obtain ⟨K_im, hK_im_compact, hK_im_supp⟩ := hg_im_cs
    refine ⟨K_re ∪ K_im, hK_re_compact.union hK_im_compact, fun x hx => ?_⟩
    rw [Set.mem_union] at hx; push_neg at hx
    simp only [hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.complex_fun]
    rw [hK_re_supp x hx.1, hK_im_supp x hx.2]
    simp
  -- g is absolutely integrable
  have hg_ai : ComplexAbsolutelyIntegrable g := by
    apply (ComplexAbsolutelyIntegrable.iff g).mpr
    exact ⟨hg_re_eq ▸ hg_re_ai, hg_im_eq ▸ hg_im_ai⟩
  refine ⟨g, hg_cont, hg_cs, ?_⟩
  -- Norm bound: PreL1.norm (f - g) ≤ ε
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  have hfg_re : Complex.re_fun (f - g) = Complex.re_fun f - g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hfg_im : Complex.im_fun (f - g) = Complex.im_fun f - g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  have h_bound : ∀ x, EReal.abs_fun (f - g) x ≤
      (EReal.abs_fun (Complex.re_fun (f - g)) + EReal.abs_fun (Complex.im_fun (f - g))) x :=
    fun x => by
      simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by
        calc ‖(f - g) x‖ ≤ |((f - g) x).re| + |((f - g) x).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = ‖((f - g) x).re‖ + ‖((f - g) x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  have hfg_ai := hf.sub hg_ai
  have hfg_re_ai := ComplexAbsolutelyIntegrable.re (f - g) hfg_ai
  have hfg_im_ai := ComplexAbsolutelyIntegrable.im (f - g) hfg_ai
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
                                EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.mono hfg_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1) (AlmostAlways.ofAlways h_bound)
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
      EReal.abs_fun (Complex.im_fun (f - g))) =
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g))) +
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.add hfg_re_ai.abs.1 hfg_im_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1)
  rw [h_add] at h_mono
  rw [show EReal.abs_fun (Complex.re_fun (f - g)) =
        EReal.abs_fun (Complex.re_fun f - g_re) from by rw [hfg_re],
      show EReal.abs_fun (Complex.im_fun (f - g)) =
        EReal.abs_fun (Complex.im_fun f - g_im) from by rw [hfg_im]] at h_mono
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f - g_re)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f - g_im)) := h_mono
    _ ≤ (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) := add_le_add hg_re_norm hg_im_norm
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

def UniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop := ∀ ε>0, ∃ N, ∀ n ≥ N, ∀ x, dist (f n x) (g x) ≤ ε

def UniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) (S: Set X): Prop := UniformlyConvergesTo (fun n (x:S) ↦ f n x.val) (fun x ↦ g x.val)

/-- Definition 1.3.21 (Locally uniform convergence) -/
def LocallyUniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop :=
  ∀ (K: Set X), Bornology.IsBounded K → UniformlyConvergesToOn f g K

/-- Remark 1.3.22 -/
theorem LocallyUniformlyConvergesTo.iff {d:ℕ} {Y:Type*} [PseudoMetricSpace Y] (f: ℕ → EuclideanSpace' d → Y) (g: EuclideanSpace' d → Y) :
  LocallyUniformlyConvergesTo f g ↔
  ∀ x₀, ∃ U: Set (EuclideanSpace' d), x₀ ∈ U ∧ IsOpen U → UniformlyConvergesToOn f g U := by sorry

def LocallyUniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) (S: Set X): Prop :=
  LocallyUniformlyConvergesTo (fun n (x:S) ↦ f n x.val) (fun x ↦ g x.val)

/-- Example 1.3.23 -/
example : LocallyUniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ x.toReal / n) (fun x ↦ 0) := by sorry

example : ¬ UniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ x.toReal / n) (fun x ↦ 0) := by sorry

/-- Example 1.3.24 -/
example : LocallyUniformlyConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

example : PointwiseConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

example : ¬ UniformlyConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

/-- Example 1.3.25 -/
example : PointwiseConvergesTo (fun n (x:EuclideanSpace' 1) ↦ if x.toReal > 0 then 1 / (n * x.toReal) else 0) (fun x ↦ 0) := by sorry

example : ¬ LocallyUniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ if x.toReal > 0 then 1 / (n * x.toReal) else 0) (fun x ↦ 0) := by sorry

/-- Theorem 1.3.26 (Egorov's theorem)-/
theorem PointwiseAeConvergesTo.locallyUniformlyConverges_outside_small {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
  (hf: ∀ n, ComplexMeasurable (f n))
  (hfg: PointwiseAeConvergesTo f g)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
    Lebesgue_measure E ≤ ε ∧
    LocallyUniformlyConvergesToOn f g Eᶜ := by sorry

/-- The exceptional set in Egorov's theorem cannot be taken to be null -/
example : ∃ (d:ℕ) (f : ℕ → EuclideanSpace' d → ℝ) (g : EuclideanSpace' d → ℝ),
    (∀ n, RealMeasurable (f n)) ∧
    PointwiseAeConvergesTo f g ∧
    ∀ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
      Lebesgue_measure E = 0 →
      ¬ LocallyUniformlyConvergesToOn f g Eᶜ := by sorry

/-- Remark 1.3.27: Local uniform convergence in Egorov's theorem cannot be upgraded to uniform convergence -/
example : ∃ (d:ℕ) (f : ℕ → EuclideanSpace' d → ℝ) (g : EuclideanSpace' d → ℝ),
    (∀ n, RealMeasurable (f n)) ∧
    PointwiseAeConvergesTo f g ∧
    ∃ (ε : ℝ) (hε : 0 < ε),
      ∀ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
        Lebesgue_measure E ≤ ε →
        ¬ UniformlyConvergesToOn f g Eᶜ := by sorry

/-- But uniform convergence can be recovered on a fixed set of finite measure -/
theorem PointwiseAeConvergesTo.uniformlyConverges_outside_small {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
  (hf: ∀ n, ComplexMeasurable (f n))
  (hfg: PointwiseAeConvergesTo f g)
  (S: Set (EuclideanSpace' d))
  (hS: Lebesgue_measure S < ⊤)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
    Lebesgue_measure E ≤ ε ∧
    UniformlyConvergesToOn f g (Sᶜ ∪ E) := by sorry

/-- Theorem 1.3.28 (Lusin's theorem) -/
theorem ComplexAbsolutelyIntegrable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ MeasurableSet E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Lusin's theorem does not make the original function continuous outside of E -/
example : ∃ (d:ℕ) (f : EuclideanSpace' d → ℝ),
    RealMeasurable f ∧
    ∀ (E: Set (EuclideanSpace' d)), MeasurableSet E → Lebesgue_measure E ≤ 1 → ¬ ContinuousOn f Eᶜ := by sorry

def LocallyComplexAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop :=
  ∀ (S: Set (EuclideanSpace' d)), MeasurableSet S ∧ Bornology.IsBounded S → ComplexAbsolutelyIntegrableOn f S

/-- Exercise 1.3.23 (Lusin's theorem only requires local absolute integrability )-/
theorem LocallyComplexAbsolutelyIntegrable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: LocallyComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ MeasurableSet E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

theorem ComplexMeasurable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexMeasurable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ MeasurableSet E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Exercise 1.3.24 -/
theorem ComplexMeasurable.iff_pointwiseae_of_continuous {d:ℕ} {f : EuclideanSpace' d → ℂ} :
  ComplexMeasurable f ↔
  ∃ (g : ℕ → EuclideanSpace' d → ℂ), (∀ n, Continuous (g n)) ∧ PointwiseAeConvergesTo g f := by sorry

/-- Remark 1.3.29 -/
theorem UnsignedMeasurable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → EReal}
  (hf: UnsignedMeasurable f) (hfin: AlmostAlways (fun x ↦ f x < ⊤))
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℝ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ MeasurableSet E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Exercise 1.3.25 (a) (Littlewood-like principle) -/
theorem ComplexAbsolutelyIntegrable.almost_bounded_support {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (R: ℝ), PreL1.norm (f * Complex.indicator (Metric.ball 0 R)ᶜ) ≤ ε := by sorry

def BoundedOn {X Y:Type*} [PseudoMetricSpace Y] (f: X → Y) (S: Set X) : Prop := Bornology.IsBounded (f '' S)

/-- Exercise 1.3.25 (b) (Littlewood-like principle) -/
theorem ComplexAbsolutelyIntegrable.almost_bounded {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
    Lebesgue_measure E ≤ ε ∧
    BoundedOn f Eᶜ := by sorry
