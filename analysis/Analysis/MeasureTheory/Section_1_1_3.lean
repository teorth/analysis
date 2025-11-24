import Analysis.MeasureTheory.Section_1_1_2

/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Definition 1.1.5.  (Riemann integrability) The interval `I` should be closed, though we will not enforce this.  We also permit the length to be 0. We index the tags and deltas starting from 0 rather than 1
in the text as this is slightly more convenient in Lean. -/
@[ext]
structure TaggedPartition (I: BoundedInterval) (n:ℕ) where
  x : Fin (n+1) → ℝ
  x_tag : Fin n → ℝ
  x_start : x 0 = I.a
  x_end : x (Fin.last n) = I.b
  x_mono : StrictMono x
  x_tag_between (i: Fin n) : x i.castSucc ≤ x_tag i ∧ x_tag i ≤ x i.succ

def TaggedPartition.delta {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) (i:Fin n): ℝ :=
 P.x i.succ - P.x i.castSucc

noncomputable def TaggedPartition.norm {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) : ℝ := iSup P.delta

def TaggedPartition.RiemannSum {I: BoundedInterval} {n:ℕ} (f: ℝ → ℝ) (P: TaggedPartition I n) : ℝ :=
  ∑ i, f (P.x_tag i) * P.delta i

/-- `Sigma (TaggedPartition I)` is the type of all partitions of `I` with an unspecified number `n` of components.  Here we define what it means to converge to zero in this type. -/
instance TaggedPartition.nhds_zero (I: BoundedInterval) : Filter (Sigma (TaggedPartition I)) := Filter.comap (fun P ↦ P.snd.norm) (nhds 0)

def riemann_integral_eq (f: ℝ → ℝ) (I: BoundedInterval) (R: ℝ) : Prop := (TaggedPartition.nhds_zero I).Tendsto (fun P ↦ TaggedPartition.RiemannSum f P.snd) (nhds R)

/-- Construct a uniform partition of `[a,b]` into `n` equal pieces with left endpoint tags. -/
noncomputable def TaggedPartition.uniform (I: BoundedInterval) (n: ℕ) (hn: n > 0) (_: I = Icc I.a I.b) (hab: I.a < I.b) : TaggedPartition I n where
  x := fun i => I.a + (I.b - I.a) * (i.val : ℝ) / n
  x_tag := fun i => I.a + (I.b - I.a) * (i.castSucc.val : ℝ) / n
  x_start := by simp
  x_end := by
    show I.a + (I.b - I.a) * ((Fin.last n).val : ℝ) / n = I.b
    rw [Fin.val_last]
    field_simp
  x_mono i j hij := by
    have h_width_pos : 0 < I.b - I.a := by linarith
    have h_n_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have : (i.val : ℝ) < (j.val : ℝ) := Nat.cast_lt.mpr hij
    apply add_lt_add_left
    apply div_lt_div_of_pos_right
    · exact mul_lt_mul_of_pos_left this h_width_pos
    · exact h_n_pos
  x_tag_between i := by
    constructor
    · -- i.castSucc.val = i.val
      rfl
    · -- i.castSucc.val ≤ i.succ.val
      have h_width_nonneg : 0 ≤ I.b - I.a := by linarith
      have h_n_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      show I.a + (I.b - I.a) * (i.castSucc.val : ℝ) / n ≤ I.a + (I.b - I.a) * (i.succ.val : ℝ) / n
      rw [show i.castSucc.val = i.val from rfl, Fin.val_succ]
      apply add_le_add_left
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left _ h_width_nonneg
        norm_num
      · linarith

/-- The norm of a uniform partition is (b-a)/n. -/
lemma TaggedPartition.uniform_norm (I: BoundedInterval) (n: ℕ) (hn: n > 0) (hI: I = Icc I.a I.b) (hab: I.a < I.b) :
    (TaggedPartition.uniform I n hn hI hab).norm = (I.b - I.a) / n := by
  let P := TaggedPartition.uniform I n hn hI hab
  unfold TaggedPartition.norm
  -- All deltas are equal to (b-a)/n
  have h_eq : ∀ i : Fin n, P.delta i = (I.b - I.a) / n := by
    intro i
    unfold TaggedPartition.delta
    show P.x i.succ - P.x i.castSucc = (I.b - I.a) / n
    -- Unfold the definition of P.x from uniform
    show (I.a + (I.b - I.a) * (i.succ.val : ℝ) / n) - (I.a + (I.b - I.a) * (i.castSucc.val : ℝ) / n) = (I.b - I.a) / n
    rw [show i.castSucc.val = i.val from rfl, Fin.val_succ]
    field_simp
    ring
  -- The supremum of a constant function is that constant
  have h_bdd : BddAbove (Set.range P.delta) := Set.Finite.bddAbove (Set.finite_range P.delta)
  have h_le : ∀ i, P.delta i ≤ (I.b - I.a) / n := by
    intro i
    rw [h_eq]
  have h_nonempty : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h_ge : (I.b - I.a) / n ≤ iSup P.delta := by
    have : ∃ i, P.delta i = (I.b - I.a) / n := ⟨⟨0, hn⟩, h_eq ⟨0, hn⟩⟩
    obtain ⟨i, hi⟩ := this
    calc (I.b - I.a) / n = P.delta i := hi.symm
      _ ≤ iSup P.delta := le_ciSup h_bdd i
  have h_le_sup : iSup P.delta ≤ (I.b - I.a) / n := by
    haveI : Nonempty (Fin n) := h_nonempty
    exact ciSup_le h_le
  linarith

/-- For any positive interval and δ > 0, there exists a tagged partition with norm ≤ δ. -/
lemma TaggedPartition.exists_norm_le (I: BoundedInterval) (hI: I = Icc I.a I.b) (hab: I.a < I.b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (P : TaggedPartition I n), P.norm ≤ δ := by
  -- Choose n large enough that (b-a)/n < δ
  obtain ⟨N, hN⟩ := exists_nat_gt ((I.b - I.a) / δ)
  have h_width_pos : 0 < I.b - I.a := by linarith
  have h_ratio_pos : 0 < (I.b - I.a) / δ := div_pos h_width_pos hδ
  have hN_pos : N > 0 := Nat.pos_of_ne_zero (fun h => by
    rw [h] at hN
    simp at hN
    linarith)
  use N, TaggedPartition.uniform I N hN_pos hI hab
  rw [TaggedPartition.uniform_norm]
  -- We have: (b-a)/δ < N, so (b-a) < N*δ, so (b-a)/N < δ
  have : (I.b - I.a) / (N : ℝ) < δ := by
    calc (I.b - I.a) / (N : ℝ)
        < (I.b - I.a) / ((I.b - I.a) / δ) := by
          apply div_lt_div_of_pos_left h_width_pos h_ratio_pos hN
      _ = δ := by field_simp
  linarith

/-- The filter TaggedPartition.nhds_zero is non-trivial when the interval has positive length. -/
instance TaggedPartition.nhds_zero_neBot (I: BoundedInterval) (hI: I = Icc I.a I.b) (hab: I.a < I.b) :
    Filter.NeBot (TaggedPartition.nhds_zero I) := by
  unfold TaggedPartition.nhds_zero
  rw [Filter.comap_neBot_iff]
  intro t ht
  -- t is a neighborhood of 0, so it contains some ball around 0
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := ht
  -- Construct a partition with norm < δ
  obtain ⟨n, P, hP_norm⟩ := TaggedPartition.exists_norm_le I hI hab (δ / 2) (half_pos hδ_pos)
  use ⟨n, P⟩
  apply hδ_sub
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg]
  · calc P.norm ≤ δ / 2 := hP_norm
      _ < δ := half_lt_self hδ_pos
  · -- Show P.norm is nonnegative
    unfold TaggedPartition.norm
    by_cases h_n_zero : n = 0
    · subst h_n_zero
      simp [iSup]
    · have h_n_pos : n > 0 := Nat.pos_of_ne_zero h_n_zero
      let i0 : Fin n := ⟨0, h_n_pos⟩
      have h_delta_nonneg : 0 ≤ P.delta i0 := by
        unfold TaggedPartition.delta
        have h_lt : i0.castSucc < i0.succ := Fin.castSucc_lt_succ i0
        have h_x_lt : P.x i0.castSucc < P.x i0.succ := P.x_mono.imp h_lt
        linarith
      have h_bdd : BddAbove (Set.range P.delta) := Set.Finite.bddAbove (Set.finite_range P.delta)
      have h_le_sup : P.delta i0 ≤ iSup P.delta := le_ciSup h_bdd i0
      linarith

/-- We enforce `I` to be closed for the definition of Riemann integrability. -/
abbrev RiemannIntegrableOn (f: ℝ → ℝ) (I: BoundedInterval) : Prop := I = Icc I.a I.b ∧ ∃ R, riemann_integral_eq f I R

open Classical in
noncomputable def riemannIntegral (f: ℝ → ℝ) (I: BoundedInterval) : ℝ := if h:RiemannIntegrableOn f I then h.2.choose else 0

/-- When an interval has zero length, all Riemann sums equal zero. -/
lemma riemann_sum_eq_zero_of_zero_length {f : ℝ → ℝ} {I : BoundedInterval} (h_len : |I|ₗ = 0)
    {n : ℕ} (P : TaggedPartition I n) : P.RiemannSum f = 0 := by
  unfold TaggedPartition.RiemannSum
  by_cases hn : n = 0
  · -- When n = 0, the sum is empty
    subst hn
    rfl
  · -- When n > 0 and |I| = 0, we derive a contradiction from StrictMono
    exfalso
    have h_n_pos : 0 < n := Nat.pos_of_ne_zero hn
    -- Fin.last n has value n, so 0 < n means 0 < (Fin.last n).val
    have h_last_pos : 0 < (Fin.last n).val := by rw [Fin.val_last]; exact h_n_pos
    -- This means (0 : Fin (n+1)) < Fin.last n as Fin values
    have h_fin_lt : (0 : Fin (n+1)) < Fin.last n := h_last_pos
    have : P.x 0 < P.x (Fin.last n) := P.x_mono.imp h_fin_lt
    rw [P.x_start, P.x_end] at this
    unfold BoundedInterval.length at h_len
    simp at h_len
    linarith

/-- When an interval has zero length and Riemann sums converge to R, then R = 0.
    This requires that the filter is non-trivial (NeBot), which holds when `I.a = I.b`. -/
lemma riemann_integral_eq_zero_of_zero_length {f : ℝ → ℝ} {I : BoundedInterval} {R : ℝ}
    (h_eq : I.a = I.b) (h_len : |I|ₗ = 0) (hR : riemann_integral_eq f I R) : R = 0 := by
  -- All Riemann sums are 0
  have h_zero : ∀ P : Sigma (TaggedPartition I), P.snd.RiemannSum f = 0 :=
    fun ⟨_, P⟩ => riemann_sum_eq_zero_of_zero_length h_len P
  -- Since all sums are 0, the function is constantly 0
  have h_const : (fun P : Sigma (TaggedPartition I) => P.snd.RiemannSum f) = fun _ => 0 := by
    ext P; exact h_zero P
  -- Rewrite hR using h_const: constant 0 function tends to R
  rw [riemann_integral_eq, h_const] at hR
  -- Constant function 0 also tends to 0
  haveI : Filter.NeBot (TaggedPartition.nhds_zero I) := by
    -- When I.a = I.b, we can construct a partition with n = 0
    -- This shows Sigma (TaggedPartition I) is nonempty, hence filter is NeBot
    let P0 : TaggedPartition I 0 := {
      x := fun _ => I.a
      x_tag := fun i => i.elim0
      x_start := rfl
      x_end := by show I.a = I.b; exact h_eq
      x_mono := fun i j hij => by
        have hi : i = 0 := Fin.eq_zero i
        have hj : j = 0 := Fin.eq_zero j
        rw [hi, hj] at hij
        exact absurd rfl (ne_of_lt hij)
      x_tag_between := fun i => i.elim0
    }
    -- Show the comap filter is NeBot using the nonempty type
    apply Filter.comap_neBot_iff.mpr
    intro s hs
    -- We need to show ∃ a, a.snd.norm ∈ s
    -- The n=0 partition P0 has norm 0 (supremum over empty Fin 0)
    -- Since s ∈ nhds 0 and 0 ∈ s, we can use P0
    use ⟨0, P0⟩
    -- Show P0.norm ∈ s
    -- For n=0, norm = iSup of empty set = 0 ∈ s (since s is nbhd of 0)
    -- P0.norm = 0 because iSup over Fin 0 is 0
    have h_P0_norm : P0.norm = 0 := by
      unfold TaggedPartition.norm
      -- iSup over empty Fin 0 → ℝ equals sSup ∅ = 0
      rw [iSup_of_empty']
      exact Real.sSup_empty
    rw [h_P0_norm]
    exact mem_of_mem_nhds hs
  have h_zero_to_zero : Filter.Tendsto (fun _ : Sigma (TaggedPartition I) => (0 : ℝ)) (TaggedPartition.nhds_zero I) (nhds 0) :=
    tendsto_const_nhds
  -- By uniqueness of limits in Hausdorff spaces (ℝ is Hausdorff)
  exact tendsto_nhds_unique hR h_zero_to_zero

/-- When an interval has zero length and Riemann sums converge, the endpoints are equal.
    This follows from the fact that partitions can only exist when I.a ≤ I.b. -/
lemma eq_of_length_zero_and_riemann_integral_eq {f : ℝ → ℝ} {I : BoundedInterval} {R : ℝ}
    (h_len : |I|ₗ = 0) (hR : riemann_integral_eq f I R) : I.a = I.b := by
  -- From zero length, we get I.b ≤ I.a
  have h_ba : I.b ≤ I.a := by
    unfold BoundedInterval.length at h_len
    simp at h_len
    linarith
  -- We need to show I.a ≤ I.b for antisymmetry
  -- If I.a > I.b, no TaggedPartition can exist, contradicting the convergence
  by_contra h_ne
  push_neg at h_ne
  -- h_ne: ¬(I.a = I.b), combined with h_ba: I.b ≤ I.a, gives I.b < I.a
  have h_lt : I.b < I.a := Ne.lt_of_le (Ne.symm h_ne) h_ba
  have h_partition_0_impossible : ¬ Nonempty (TaggedPartition I 0) := by
    intro ⟨P⟩
    -- P.x_start : P.x 0 = I.a
    -- P.x_end : P.x (Fin.last 0) = I.b
    -- But Fin.last 0 = 0
    have h_last : (Fin.last 0) = 0 := Fin.ext (by simp)
    -- So P.x 0 = I.a and P.x 0 = I.b, giving I.a = I.b
    have h_eq : I.a = I.b := by
      calc I.a = P.x 0 := P.x_start.symm
        _ = P.x (Fin.last 0) := by rw [h_last]
        _ = I.b := P.x_end
    -- But we have h_lt : I.b < I.a, contradiction
    linarith

  -- For n > 0, partitions also can't exist since x would need to satisfy
  -- I.a = x 0 < x n = I.b (by StrictMono), giving I.a < I.b, contradicting h_lt
  have h_partition_succ_impossible : ∀ n : ℕ, ¬ Nonempty (TaggedPartition I (n + 1)) := by
    intro n ⟨P⟩
    -- P.x_start : P.x 0 = I.a
    -- P.x_end : P.x (Fin.last (n+1)) = I.b
    -- P.x_mono : StrictMono P.x
    have h_last_pos : 0 < (Fin.last (n + 1)).val := by
      rw [Fin.val_last]
      omega
    have h_fin_lt : (0 : Fin (n + 2)) < Fin.last (n + 1) := h_last_pos
    have h_x_lt : P.x 0 < P.x (Fin.last (n + 1)) := P.x_mono.imp h_fin_lt
    rw [P.x_start, P.x_end] at h_x_lt
    -- So I.a < I.b, contradicting h_lt : I.b < I.a
    linarith

  -- Since no partition exists for any n, Sigma (TaggedPartition I) is empty
  -- This means the filter domain is empty
  have h_empty : IsEmpty (Sigma (TaggedPartition I)) := by
    constructor
    intro ⟨n, P⟩
    cases n with
    | zero => exact h_partition_0_impossible ⟨P⟩
    | succ n => exact h_partition_succ_impossible n ⟨P⟩

  sorry

/-- Definition 1.1.15 (Riemann integrability) -/
lemma riemann_integral_of_integrable {f:ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) : riemann_integral_eq f I (riemannIntegral f I) := by
  -- Strategy: Since `h : RiemannIntegrableOn f I` means `∃ R, riemann_integral_eq f I R`,
  -- and `riemannIntegral f I` is defined as `h.2.choose` (the witness chosen by Classical.choose),
  -- we need to show that `riemann_integral_eq f I h.2.choose`, which is exactly `h.2.choose_spec`.
  unfold riemannIntegral
  convert h.2.choose_spec using 2
  -- Split on the if condition (which is `RiemannIntegrableOn f I`, true by hypothesis `h`)
  split_ifs
  -- In the `then` branch, we have `h.2.choose = h.2.choose` by reflexivity
  · rfl

/-- Definition 1.1.15 (Riemann integrability) -/
lemma riemann_integral_eq_iff_of_integrable {f:ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) (R:ℝ): riemann_integral_eq f I R ↔ R = riemannIntegral f I := by
  constructor
  · -- Forward direction: uniqueness of limits in Hausdorff space
    intro hR
    -- We know riemann_integral_eq f I (riemannIntegral f I) from riemann_integral_of_integrable
    have hRI := riemann_integral_of_integrable h
    -- Handle two cases: I.a < I.b or I.a = I.b
    by_cases hab : I.a < I.b
    · -- Case: I.a < I.b (positive length interval)
      -- The filter is non-trivial, so we can apply Hausdorff limit uniqueness
      haveI : Filter.NeBot (TaggedPartition.nhds_zero I) := TaggedPartition.nhds_zero_neBot I h.1 hab
      -- Both Riemann sums converge: one to R, one to riemannIntegral f I
      -- In a Hausdorff space (ℝ is metric hence Hausdorff), limits are unique
      exact tendsto_nhds_unique hR hRI
    · -- Case: ¬(I.a < I.b) means I.a ≥ I.b (zero or negative length interval)
      -- In either case, the length is 0
      have h_len : |I|ₗ = 0 := by
        unfold BoundedInterval.length
        simp
        -- ¬(I.a < I.b) means I.a ≥ I.b, so max(0, I.b - I.a) = 0
        have : I.b ≤ I.a := le_of_not_gt hab
        linarith
      -- When I = Icc I.a I.b and length is 0, we have I.a = I.b
      have h_eq : I.a = I.b := eq_of_length_zero_and_riemann_integral_eq h_len hR
      -- Both R and riemannIntegral f I equal 0 when length is 0 and I.a = I.b
      have hR_zero : R = 0 := riemann_integral_eq_zero_of_zero_length h_eq h_len hR
      have hRI_zero : riemannIntegral f I = 0 := riemann_integral_eq_zero_of_zero_length h_eq h_len hRI
      -- Therefore R = riemannIntegral f I
      rw [hR_zero, hRI_zero]
  · -- Backward direction: substitution
    intro hRe
    rw [hRe]
    exact riemann_integral_of_integrable h

/-- Definition 1.1.15 (Riemann integrability)-/
lemma riemann_integral_eq_iff {f:ℝ → ℝ} {I: BoundedInterval} (R:ℝ): riemann_integral_eq f I R ↔ ∀ ε>0, ∃ δ>0, ∀ n, ∀ P: TaggedPartition I n, P.norm ≤ δ → |P.RiemannSum f - R| ≤ ε := by
  -- Show equivalence between filter convergence and ε-δ definition.
  -- Forward (→): Use `LinearOrderedAddCommGroup.tendsto_nhds` and `Filter.eventually_comap` to extract ε-δ.
  -- Backward (←): Given ε-δ, show filter convergence
  unfold riemann_integral_eq TaggedPartition.nhds_zero
  -- Use LinearOrderedAddCommGroup.tendsto_nhds to characterize filter convergence
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  -- Use Filter.eventually_comap to relate comap filter to nhds 0
  simp_rw [Filter.eventually_comap]
  constructor
  · -- Forward direction: filter convergence → ε-δ
    intro h_tendsto ε hε
    -- Get eventually condition from filter convergence
    have h_eventually : ∀ᶠ (x : ℝ) in nhds 0, ∀ (a : Sigma (TaggedPartition I)), a.snd.norm = x → |TaggedPartition.RiemannSum f a.snd - R| < ε := h_tendsto ε hε
    -- Extract δ from nhds 0: use Metric.mem_nhds_iff to get a ball
    rw [Metric.eventually_nhds_iff] at h_eventually
    obtain ⟨δ, hδ_pos, hδ_ball⟩ := h_eventually
    -- Use δ/2 to ensure strict inequality, then strengthen to ≤
    use δ / 2, half_pos hδ_pos
    intro n P hP_norm
    -- Show |RiemannSum - R| ≤ ε using the filter condition
    -- First show P.norm < δ (since P.norm ≤ δ/2 < δ)
    have h_norm_lt : P.norm < δ := by
      linarith [hP_norm]
    -- P.norm is nonnegative (each delta is nonnegative by monotonicity)
    have h_norm_nonneg : 0 ≤ P.norm := by
      unfold TaggedPartition.norm
      -- Show that 0 ≤ iSup by showing each delta ≥ 0
      by_cases h_n_empty : n = 0
      · -- If n = 0, the range is empty, so iSup = 0
        subst h_n_empty
        simp [iSup]
      · -- If n > 0, pick any index and show its delta ≥ 0
        have h_n_pos : n > 0 := Nat.pos_of_ne_zero h_n_empty
        -- Construct Fin n element for index 0
        have h_fin_zero : 0 < n := h_n_pos
        let i0 : Fin n := Fin.mk 0 h_fin_zero
        have h_delta_nonneg : 0 ≤ P.delta i0 := by
          unfold TaggedPartition.delta
          -- Show P.x i0.castSucc ≤ P.x i0.succ using strict monotonicity
          have h_lt : i0.castSucc < i0.succ := Fin.castSucc_lt_succ i0
          have h_x_lt : P.x i0.castSucc < P.x i0.succ := P.x_mono.imp h_lt
          linarith
        -- Show 0 ≤ iSup by showing 0 ≤ some element in the range
        -- The range is bounded above since Fin n is finite
        have h_bdd : BddAbove (Set.range P.delta) := by
          -- Fin n is finite, so the range is finite and bounded
          have h_finite : (Set.range P.delta).Finite := Set.finite_range P.delta
          exact Set.Finite.bddAbove h_finite
        -- Use le_trans: 0 ≤ P.delta i0 ≤ iSup P.delta
        have h_le_sup : P.delta i0 ≤ iSup P.delta := le_ciSup h_bdd i0
        linarith [h_delta_nonneg, h_le_sup]
    -- Apply filter condition: if dist P.norm 0 < δ, then for all P with P.norm = P.norm, |RiemannSum - R| < ε
    -- Note: ⟨n, P⟩.snd.norm = P.norm, and dist P.norm 0 = |P.norm| = P.norm (since nonnegative)
    -- Show dist P.norm 0 < δ
    have h_dist : dist P.norm 0 < δ := by
      rw [Real.dist_eq]
      simp [sub_zero]
      rw [abs_of_nonneg h_norm_nonneg]
      exact h_norm_lt
    -- Apply hδ_ball with P.norm and show ⟨n, P⟩.snd.norm = P.norm
    have h_eq : (⟨n, P⟩ : Sigma (TaggedPartition I)).snd.norm = P.norm := rfl
    have h_applied := hδ_ball h_dist ⟨n, P⟩ h_eq
    -- Convert < to ≤
    linarith
  · -- Backward direction: ε-δ → filter convergence
    intro h_eps_delta ε hε
    -- Use ε/2 to get strict inequality from ≤ condition
    obtain ⟨δ, hδ_pos, hδ⟩ := h_eps_delta (ε / 2) (half_pos hε)
    -- Show eventually condition using Metric.eventually_nhds_iff
    rw [Metric.eventually_nhds_iff]
    use δ, hδ_pos
    -- Show that if |x| < δ and P.norm = x, then |RiemannSum - R| < ε
    intro x hx_abs a hP_eq
    -- Show a.snd.norm ≤ δ
    have hP_norm_le : a.snd.norm ≤ δ := by
      -- Use hP_eq: a.snd.norm = x, and hx_abs: dist x 0 < δ
      -- Convert dist to abs
      rw [Real.dist_eq, sub_zero] at hx_abs
      rw [abs_lt] at hx_abs
      -- Use hP_eq to substitute: a.snd.norm = x, so |a.snd.norm| < δ
      rw [←hP_eq] at hx_abs
      -- a.snd.norm is nonnegative (as partition norm), so |a.snd.norm| = a.snd.norm
      -- Extract n and P from a to show nonnegativity
      have h_norm_nonneg : 0 ≤ a.snd.norm := by
        -- Use the same approach as forward direction
        unfold TaggedPartition.norm
        -- Destructure a to get n as a variable
        cases a with | mk n P =>
        -- Simplify ⟨n, P⟩.snd to P in the goal
        simp
        by_cases h_n_empty : n = 0
        · -- If n = 0, the range is empty, so iSup = 0
          subst h_n_empty
          simp [iSup]
        · have h_n_pos : n > 0 := Nat.pos_of_ne_zero h_n_empty
          have h_fin_zero : 0 < n := h_n_pos
          let i0 : Fin n := Fin.mk 0 h_fin_zero
          have h_delta_nonneg : 0 ≤ P.delta i0 := by
            unfold TaggedPartition.delta
            have h_lt : i0.castSucc < i0.succ := Fin.castSucc_lt_succ i0
            have h_x_lt : P.x i0.castSucc < P.x i0.succ := P.x_mono.imp h_lt
            linarith
          have h_bdd : BddAbove (Set.range P.delta) := by
            have h_finite : (Set.range P.delta).Finite := Set.finite_range P.delta
            exact Set.Finite.bddAbove h_finite
          have h_le_sup : P.delta i0 ≤ iSup P.delta := le_ciSup h_bdd i0
          linarith [h_delta_nonneg, h_le_sup]
      -- hx_abs is already in the form -δ < a.snd.norm ∧ a.snd.norm < δ from abs_lt
      -- So we can directly use hx_abs.2: a.snd.norm < δ, which implies a.snd.norm ≤ δ
      linarith [hx_abs.2]
    -- Apply ε-δ condition: need to extract n and P from a
    have h_applied := hδ (Sigma.fst a) a.snd hP_norm_le
    linarith

/-- Definition 1.1.15.  (Riemann integrability) I *think* this follows from the "junk" definitions of various Mathlib operations, but needs to be checked. If not, then the above definitions need to be adjusted appropriately. -/
lemma RiemannIntegrable.of_zero_length (f: ℝ → ℝ) {I: BoundedInterval} (h: |I|ₗ = 0) : RiemannIntegrableOn f I ∧ riemannIntegral f I = 0 := by sorry

/-- Definition 1.1.15 -/
theorem RiemannIntegrable.bounded {f: ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) : ∃ M, ∀ x ∈ I, |f x| ≤ M := by sorry

@[ext]
structure PiecewiseConstantFunction (I: BoundedInterval) where
  f : ℝ → ℝ
  T : Finset BoundedInterval
  c : T → ℝ
  disjoint: T.toSet.PairwiseDisjoint BoundedInterval.toSet
  cover : I.toSet = ⋃ J ∈ T, J.toSet
  const : ∀ J:T, ∀ x ∈ J.val, f x = c J

abbrev PiecewiseConstantFunction.agreesWith {I: BoundedInterval} (F: PiecewiseConstantFunction I) (f: ℝ → ℝ) : Prop := I.toSet.EqOn f F.f

def PiecewiseConstantOn (f: ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ F: PiecewiseConstantFunction I, F.agreesWith f

def PiecewiseConstantFunction.integral {I: BoundedInterval} (g: PiecewiseConstantFunction I) : ℝ :=
  ∑ J : g.T, g.c J * |J|ₗ

/-- Exercise 1.1.20 (Piecewise constant functions) -/
theorem PiecewiseConstantFunction.integral_eq (f: ℝ → ℝ) {I: BoundedInterval} (F F': PiecewiseConstantFunction I) (hF: F.agreesWith f) (hF': F'.agreesWith f) : F.integral = F'.integral := by sorry

noncomputable def PiecewiseConstantOn.integral (f: ℝ → ℝ) {I: BoundedInterval} (h: PiecewiseConstantOn f I) : ℝ := h.choose.integral

/-- Exercise 1.1.20 (Piecewise constant functions) -/
theorem PiecewiseConstantOn.integral_eq (f: ℝ → ℝ) {I: BoundedInterval} (h: PiecewiseConstantOn f I) (F: PiecewiseConstantFunction I) (hF: F.agreesWith f) : h.integral = F.integral := by sorry

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
theorem PiecewiseConstantOn.smul {I: BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by sorry

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
theorem PiecewiseConstantFunction.integral_smul {I:BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) : (h.smul c).integral = h.integral := by sorry

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
theorem PiecewiseConstantOn.add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I := by sorry

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
theorem PiecewiseConstantFunction.integral_add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : (hf.add hg).integral = hf.integral + hg.integral := by sorry

/-- Exercise 1.1.21 (b) (Monotonicity of the piecewise constant integral) -/
theorem PiecewiseConstantFunction.integral_mono {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x): hf.integral ≤ hg.integral := by sorry

/-- Exercise 1.1.21 (c) (Piecewise constant integral of indicator functions) -/
theorem PiecewiseConstantOn.indicator_of_elem (I: BoundedInterval) {E:Set ℝ} (hE: IsElementary (Real.equiv_EuclideanSpace' '' E) ) : PiecewiseConstantOn E.indicator' I := by sorry

/-- Exercise 1.1.21 (c) (Piecewise constant integral of indicator functions) -/
theorem PiecewiseConstantFunction.integral_of_elem {I: BoundedInterval} {E:Set ℝ} (hE: IsElementary (Real.equiv_EuclideanSpace' '' E) ) (hsub: E ⊆ I.toSet) : (PiecewiseConstantOn.indicator_of_elem I hE).integral = hE.measure := by sorry

/-- Definition 1.1.6 (Darboux integral) -/
noncomputable def LowerDarbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := sSup { R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x }

/-- Definition 1.1.6 (Darboux integral) -/
noncomputable def UpperDarbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := sInf { R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, f x ≤ h.f x }

/-- Helper: Construct a constant piecewise constant function with a given value -/
def PiecewiseConstantFunction.mkConst (I: BoundedInterval) (c: ℝ) : PiecewiseConstantFunction I where
  f := fun _ => c
  T := {I}
  c := fun _ => c
  disjoint := by simp [Set.pairwiseDisjoint_singleton]
  cover := by simp
  const := by intro J x hx; rfl

/-- Helper: The integral of a constant piecewise constant function -/
lemma PiecewiseConstantFunction.integral_mkConst (I: BoundedInterval) (c: ℝ) :
    (PiecewiseConstantFunction.mkConst I c).integral = c * |I|ₗ := by
  unfold PiecewiseConstantFunction.integral PiecewiseConstantFunction.mkConst
  simp [Finset.sum_singleton]

/-- Helper: Construct the negation of a piecewise constant function -/
def PiecewiseConstantFunction.neg {I: BoundedInterval} (g: PiecewiseConstantFunction I) : PiecewiseConstantFunction I where
  f := fun x => -g.f x
  T := g.T
  c := fun J => -g.c J
  disjoint := g.disjoint
  cover := g.cover
  const := by
    intro J x hx
    have h_const : g.f x = g.c J := g.const J x hx
    simp [h_const]

/-- Helper: The integral of a negated piecewise constant function -/
lemma PiecewiseConstantFunction.integral_neg {I: BoundedInterval} (g: PiecewiseConstantFunction I) :
    g.neg.integral = -g.integral := by
  unfold PiecewiseConstantFunction.integral PiecewiseConstantFunction.neg
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext J
  ring

/-- Helper: Convert a PiecewiseConstantFunction to PiecewiseConstantOn and relate integrals -/
lemma PiecewiseConstantFunction.to_PiecewiseConstantOn {I: BoundedInterval} (g: PiecewiseConstantFunction I) :
    ∃ (h: PiecewiseConstantOn g.f I), h.integral = g.integral := by
  have hg_agrees : g.agreesWith g.f := fun x hx => rfl
  use ⟨g, hg_agrees⟩
  exact PiecewiseConstantOn.integral_eq g.f ⟨g, hg_agrees⟩ g hg_agrees

/-- Helper: Apply integral_mono between two PiecewiseConstantFunctions via PiecewiseConstantOn -/
lemma PiecewiseConstantFunction.integral_mono' {I: BoundedInterval}
    (g h: PiecewiseConstantFunction I) (h_pointwise: ∀ x ∈ I.toSet, g.f x ≤ h.f x) :
    g.integral ≤ h.integral := by
  have hg_agrees : g.agreesWith g.f := fun x hx => rfl
  have hh_agrees : h.agreesWith h.f := fun x hx => rfl
  have hg_pc : PiecewiseConstantOn g.f I := ⟨g, hg_agrees⟩
  have hh_pc : PiecewiseConstantOn h.f I := ⟨h, hh_agrees⟩
  have h_integral_eq_g : hg_pc.integral = g.integral :=
    PiecewiseConstantOn.integral_eq g.f hg_pc g hg_agrees
  have h_integral_eq_h : hh_pc.integral = h.integral :=
    PiecewiseConstantOn.integral_eq h.f hh_pc h hh_agrees
  have h_mono : hg_pc.integral ≤ hh_pc.integral :=
    PiecewiseConstantFunction.integral_mono hg_pc hh_pc h_pointwise
  rw [h_integral_eq_g, h_integral_eq_h] at h_mono
  exact h_mono

/-- Helper: The lower Darboux set is bounded above -/
lemma LowerDarbouxIntegral.bddAbove {f:ℝ → ℝ} {I: BoundedInterval} (M: ℝ) (hM: ∀ x ∈ I, |f x| ≤ M) :
    BddAbove ({ R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x } : Set ℝ) := by
  rw [bddAbove_def]
  use M * |I|ₗ
  intro R hR
  obtain ⟨g, rfl, hg_lower⟩ := hR
  let g_const := PiecewiseConstantFunction.mkConst I M
  have h_pointwise : ∀ x ∈ I.toSet, g.f x ≤ g_const.f x := by
    intro x hx
    have h_abs : |f x| ≤ M := hM x hx
    rw [abs_le] at h_abs
    simp [g_const, PiecewiseConstantFunction.mkConst]
    have h_g_f : g.f x ≤ f x := hg_lower x hx
    have h_f_M : f x ≤ M := h_abs.2
    linarith
  have h_mono := PiecewiseConstantFunction.integral_mono' g g_const h_pointwise
  rw [PiecewiseConstantFunction.integral_mkConst] at h_mono
  exact h_mono

/-- Helper: The upper Darboux set is bounded below -/
lemma UpperDarbouxIntegral.bddBelow {f:ℝ → ℝ} {I: BoundedInterval} (M: ℝ) (hM: ∀ x ∈ I, |f x| ≤ M) :
    BddBelow ({ R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, f x ≤ h.f x } : Set ℝ) := by
  rw [bddBelow_def]
  use -M * |I|ₗ
  intro R hR
  obtain ⟨h, rfl, hh_upper⟩ := hR
  let h_const := PiecewiseConstantFunction.mkConst I (-M)
  have h_pointwise : ∀ x ∈ I.toSet, h_const.f x ≤ h.f x := by
    intro x hx
    have h_abs : |f x| ≤ M := hM x hx
    rw [abs_le] at h_abs
    simp [h_const, PiecewiseConstantFunction.mkConst]
    have h_ineq : f x ≤ h.f x := hh_upper x hx
    calc -M ≤ f x := h_abs.1
      _ ≤ h.f x := h_ineq
  have h_mono := PiecewiseConstantFunction.integral_mono' h_const h h_pointwise
  rw [PiecewiseConstantFunction.integral_mkConst] at h_mono
  exact h_mono

/-- Definition 1.1.6 (Darboux integral) -/
lemma lower_darboux_le_upper_darboux {f:ℝ → ℝ} {I: BoundedInterval} (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) : LowerDarbouxIntegral f I ≤ UpperDarbouxIntegral f I := by
  obtain ⟨M, hM⟩ := hbound
  unfold LowerDarbouxIntegral UpperDarbouxIntegral
  apply csSup_le
  · -- Show lower set is nonempty
    let g_const := PiecewiseConstantFunction.mkConst I (-M)
    use g_const.integral, g_const, rfl
    intro x hx
    have h_abs : |f x| ≤ M := hM x hx
    rw [abs_le] at h_abs
    simp [g_const, PiecewiseConstantFunction.mkConst]
    linarith [h_abs.1]
  · -- Show every lower element ≤ UpperDarbouxIntegral
    intro R hR
    obtain ⟨g, rfl, hg_lower⟩ := hR
    apply le_csInf
    · -- Show upper set is nonempty
      let h_const := PiecewiseConstantFunction.mkConst I M
      use h_const.integral, h_const, rfl
      intro x hx
      have h_abs : |f x| ≤ M := hM x hx
      rw [abs_le] at h_abs
      simp [h_const, PiecewiseConstantFunction.mkConst]
      linarith [h_abs.2]
    · -- Show g.integral is a lower bound for upper set
      intro b hb
      obtain ⟨h, rfl, hh_upper⟩ := hb
      have h_pointwise : ∀ x ∈ I.toSet, g.f x ≤ h.f x := by
        intro x hx
        have hg : g.f x ≤ f x := hg_lower x hx
        have hh : f x ≤ h.f x := hh_upper x hx
        linarith
      exact PiecewiseConstantFunction.integral_mono' g h h_pointwise

/-- Definition 1.1.6 (Darboux integral) -/
noncomputable def DarbouxIntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop := (I = Icc I.a I.b) ∧ ∃ M, ∀ x ∈ I, |f x| ≤ M ∧ LowerDarbouxIntegral f I = UpperDarbouxIntegral f I

/-- We give the Darboux integral the "junk" value of the lower Darboux integral when the function is not integrable. -/
noncomputable def darbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := LowerDarbouxIntegral f I

/-- Helper: The upper Darboux set for -f is bounded below -/
lemma UpperDarbouxIntegral.bddBelow_neg {f:ℝ → ℝ} {I: BoundedInterval} (M: ℝ) (hM: ∀ x ∈ I, |f x| ≤ M) :
    BddBelow ({ R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, (-f) x ≤ h.f x } : Set ℝ) := by
  rw [bddBelow_def]
  use -M * |I|ₗ
  intro R hR
  obtain ⟨h, rfl, hh_upper⟩ := hR
  let h_const := PiecewiseConstantFunction.mkConst I (-M)
  have h_pointwise : ∀ x ∈ I.toSet, h_const.f x ≤ h.f x := by
    intro x hx
    have h_abs : |f x| ≤ M := hM x hx
    rw [abs_le] at h_abs
    simp [h_const, PiecewiseConstantFunction.mkConst]
    have h_ineq : (-f) x ≤ h.f x := hh_upper x hx
    calc -M ≤ -f x := by linarith [h_abs.2]
      _ ≤ h.f x := h_ineq
  have h_mono := PiecewiseConstantFunction.integral_mono' h_const h h_pointwise
  rw [PiecewiseConstantFunction.integral_mkConst] at h_mono
  exact h_mono

/-- Definition 1.1.6 (Darboux integral) -/
lemma UpperDarbouxIntegral.neg {f:ℝ → ℝ} {I: BoundedInterval} (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) : UpperDarbouxIntegral (-f) I = -LowerDarbouxIntegral f I := by
  obtain ⟨M, hM⟩ := hbound
  unfold UpperDarbouxIntegral LowerDarbouxIntegral
  apply le_antisymm
  · -- Show UpperDarbouxIntegral (-f) I ≤ -LowerDarbouxIntegral f I
    rw [← neg_le_neg_iff, neg_neg]
    apply csSup_le
    · -- Show lower set is nonempty
      let g_const := PiecewiseConstantFunction.mkConst I (-M)
      use g_const.integral, g_const, rfl
      intro x hx
      have h_abs : |f x| ≤ M := hM x hx
      rw [abs_le] at h_abs
      simp [g_const, PiecewiseConstantFunction.mkConst]
      linarith [h_abs.1]
    · -- Show -sInf (upper set) is an upper bound for lower set
      intro b hb
      obtain ⟨g, rfl, hg_lower⟩ := hb
      -- Key: -g is an upper approximation for -f since g ≤ f implies -f ≤ -g
      let neg_g := g.neg
      have h_neg_upper : ∀ x ∈ I.toSet, (-f) x ≤ neg_g.f x := by
        intro x hx
        have h_ineq : g.f x ≤ f x := hg_lower x hx
        simp [neg_g, PiecewiseConstantFunction.neg]
        linarith
      have h_neg_in_set : -g.integral ∈ { R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, (-f) x ≤ h.f x } := by
        use neg_g, g.integral_neg, h_neg_upper
      have h_bdd_below := UpperDarbouxIntegral.bddBelow_neg M hM
      have h_inf_le : sInf { R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, (-f) x ≤ h.f x } ≤ -g.integral :=
        csInf_le h_bdd_below h_neg_in_set
      linarith
  · -- Show -LowerDarbouxIntegral f I ≤ UpperDarbouxIntegral (-f) I
    apply le_csInf
    · -- Show upper set for -f is nonempty
      let h_const := PiecewiseConstantFunction.mkConst I M
      use h_const.integral, h_const, rfl
      intro x hx
      have h_abs : |f x| ≤ M := hM x hx
      rw [abs_le] at h_abs
      simp [h_const, PiecewiseConstantFunction.mkConst]
      linarith [h_abs.1]
    · -- Show -sSup (lower set) is a lower bound for upper set
      intro b hb
      obtain ⟨h, rfl, hh_upper⟩ := hb
      -- Key: -h is a lower approximation for f since -f ≤ h implies -h ≤ f
      let neg_h := h.neg
      have h_neg_lower : ∀ x ∈ I.toSet, neg_h.f x ≤ f x := by
        intro x hx
        have h_ineq : (-f) x ≤ h.f x := hh_upper x hx
        simp only [neg_h, PiecewiseConstantFunction.neg]
        have h1 : -f x ≤ h.f x := h_ineq
        nlinarith [h1]
      have h_neg_in_set : -h.integral ∈ { R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x } := by
        use neg_h, h.integral_neg, h_neg_lower
      have h_bdd := LowerDarbouxIntegral.bddAbove M hM
      have h_le_sup : -h.integral ≤ sSup { R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x } :=
        le_csSup h_bdd h_neg_in_set
      linarith

/-- Exercise 1.1.22 -/
lemma RiemannIntegrableOn.iff_darbouxIntegrable {f:ℝ → ℝ} {I: BoundedInterval} (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) : RiemannIntegrableOn f I ↔ DarbouxIntegrableOn f I := by sorry

/-- Exercise 1.1.22 -/
lemma riemann_integral_eq_darboux_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: RiemannIntegrableOn f I) : riemannIntegral f I = darbouxIntegral f I := by sorry

/-- Exercise 1.1.23 -/
lemma RiemannIntegrableOn.continuous {f:ℝ → ℝ} {I: BoundedInterval} (hI: I = Icc I.a I.b) (hcont: ContinuousOn f I.toSet) : RiemannIntegrableOn f I := by sorry

lemma RiemannIntegrableOn.piecewise_continuous {f:ℝ → ℝ} {I: BoundedInterval} (hI: I = Icc I.a I.b)
 (T: Finset BoundedInterval)  (hdisjoint: T.toSet.PairwiseDisjoint BoundedInterval.toSet)
 (hcover : I.toSet = ⋃ J ∈ T, J.toSet) (hcont: ∀ J ∈ T, ContinuousOn f J.toSet) : RiemannIntegrableOn f I := by sorry

/-- Exercise 1.1.24 (a) (Linearity of the piecewise constant integral) -/
theorem RiemannIntegrableOn.smul {I: BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: RiemannIntegrableOn f I) : RiemannIntegrableOn (c • f) I := by sorry

/-- Exercise 1.1.24 (a) (Linearity of the piecewise constant integral) -/
theorem riemann_integral_smul {I:BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: RiemannIntegrableOn f I) : riemannIntegral (c • f) = c • (riemannIntegral f) := by sorry

/-- Exercise 1.1.24 (a) (Linearity of the piecewise constant integral) -/
theorem RiemannIntegrableOn.add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) : RiemannIntegrableOn (f + g) I := by sorry

/-- Exercise 1.1.24 (a) (Linearity of the piecewise constant integral) -/
theorem riemann_integral_add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) : riemannIntegral (f+g) = riemannIntegral f + riemannIntegral g := by sorry

/-- Exercise 1.1.24 (b) (Monotonicity of the piecewise constant integral) -/
theorem riemann_integral_mono {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x): riemannIntegral f ≤ riemannIntegral g := by sorry

/-- Exercise 1.1.24 (c) (Indicator functions) -/
theorem RiemannIntegrableOn.indicator_of_elem (I: BoundedInterval) {E:Set ℝ} (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E) ) : RiemannIntegrableOn E.indicator' I := by sorry

/-- Exercise 1.1.24 (c) (Piecewise constant integral of indicator functions) -/
theorem riemann_integral_of_elem {I: BoundedInterval} {E:Set ℝ} (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E) ) (hsub: E ⊆ I.toSet) : riemannIntegral E.indicator' I = hE.measure := by sorry

/-- Exercise 1.1.24 (Uniqueness) -/
theorem riemann_integral_unique {I: BoundedInterval} (integ: (ℝ → ℝ) → ℝ)
  (hsmul: ∀ (c:ℝ) (f: ℝ → ℝ) (hf: RiemannIntegrableOn f I), integ (c • f) = c • (integ f))
  (hadd: ∀ (f g: ℝ → ℝ) (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I), integ (f + g) = integ f + integ g)
  (hmono: ∀ (f g: ℝ → ℝ) (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x), integ f ≤ integ g)
  (hindicator: ∀ (E:Set ℝ) (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E) ) (hsub: E ⊆ I.toSet), integ E.indicator' = hE.measure) :
  ∀ f, RiemannIntegrableOn f I → integ f = riemannIntegral f I := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
theorem RiemannIntegrableOn.measurable_upper {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ 0 ≤ p 1 ∧ p 1 ≤ f (p 0) } := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
theorem RiemannIntegrableOn.measurable_lower {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ f (p 0) ≤ p 1 ∧ p 1 ≤ 0 } := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
theorem JordanMeasurable.iff_integrable {I: BoundedInterval} (hI: I = Icc I.a I.b)
  {f: ℝ → ℝ} (hf: ∃ M, ∀ x ∈ I.toSet, |f x| ≤ M) : RiemannIntegrableOn f I ↔
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ 0 ≤ p 1 ∧ p 1 ≤ f (p 0) } ∧
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ f (p 0) ≤ p 1 ∧ p 1 ≤ 0 }
  := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
theorem RiemannIntegrableOn.eq_measure {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  riemannIntegral f I = hfint.measurable_upper.measure - hfint.measurable_lower.measure := by sorry

/- Exercise 1.1.26: Extend the definition of the Riemann and Darboux integrals to higher dimensions, in such a way that analogues of all the previous results hold; state and prove those analogues. -/
