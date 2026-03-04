import Analysis.MeasureTheory.Section_1_3_4

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
theorem ComplexAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexStepFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by sorry

theorem RealAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), RealStepFunction g ∧ RealAbsolutelyIntegrable g ∧
        PreL1.norm (f - g) ≤ ε := by sorry

def CompactlySupported {X Y:Type*} [TopologicalSpace X] [Zero Y] (f: X → Y) : Prop :=
  ∃ (K: Set X), IsCompact K ∧ ∀ x, x ∉ K → f x = 0

/-- Theorem 1.3.20(iii) Approximation of $L^1$ functions by continuous compactly supported functions -/
theorem ComplexAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), Continuous g ∧ CompactlySupported g ∧
    PreL1.norm (f - g) ≤ ε := by sorry

theorem RealAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
        PreL1.norm (f - g) ≤ ε := by sorry

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
