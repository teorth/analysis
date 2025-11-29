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

-- The width of the i-th subinterval in a tagged partition.
def TaggedPartition.delta {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) (i:Fin n): ℝ :=
 P.x i.succ - P.x i.castSucc

-- The mesh size (supremum of subinterval widths) of a tagged partition.
noncomputable def TaggedPartition.norm {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) : ℝ := iSup P.delta

-- The Riemann sum of f with respect to a tagged partition: sum of f(tag_i) * delta_i.
def TaggedPartition.RiemannSum {I: BoundedInterval} {n:ℕ} (f: ℝ → ℝ) (P: TaggedPartition I n) : ℝ :=
  ∑ i, f (P.x_tag i) * P.delta i

/-- `Sigma (TaggedPartition I)` is the type of all partitions of `I` with an unspecified number `n` of components.  Here we define what it means to converge to zero in this type. -/
-- A filter on Sigma (TaggedPartition I) converging to zero as the partition norm shrinks.
instance TaggedPartition.nhds_zero (I: BoundedInterval) : Filter (Sigma (TaggedPartition I)) := Filter.comap (fun P ↦ P.snd.norm) (nhds 0)

-- Riemann integrability: Riemann sums converge to R as the partition norm tends to zero.
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

/-- We enforce `I` to be closed and nonempty for the definition of Riemann integrability.
    The nonempty constraint ensures meaningful integration and excludes degenerate cases. -/
-- A function is Riemann integrable on a closed interval if Riemann sums converge to some value.
abbrev RiemannIntegrableOn (f: ℝ → ℝ) (I: BoundedInterval) : Prop :=
  I = Icc I.a I.b ∧ I.toSet.Nonempty ∧ ∃ R, riemann_integral_eq f I R

open Classical in
-- The Riemann integral value: the limit of Riemann sums (zero if not integrable).
noncomputable def riemannIntegral (f: ℝ → ℝ) (I: BoundedInterval) : ℝ := if h:RiemannIntegrableOn f I then h.2.2.choose else 0

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

/-- When a nonempty closed interval [a,b] has zero length, then a = b. -/
lemma eq_of_length_zero_of_Icc {I : BoundedInterval}
    (hI : I = Icc I.a I.b) (h_len : |I|ₗ = 0) (h_nonempty : I.toSet.Nonempty) : I.a = I.b := by
  -- From zero length, we get I.b ≤ I.a
  have h_ba : I.b ≤ I.a := by
    unfold BoundedInterval.length at h_len
    simp at h_len
    linarith
  -- We need to show I.a ≤ I.b for antisymmetry
  -- Key: When I = Icc I.a I.b, the set is either empty (if I.a > I.b) or a singleton (if I.a = I.b)
  -- Since length is 0, if the set were empty, we'd have issues, but actually we can just use the fact
  -- that for a closed interval to make sense with zero length, we need a = b

  -- Use le_antisymm if we can show I.a ≤ I.b
  by_cases hab : I.a ≤ I.b
  · -- If I.a ≤ I.b, then with I.b ≤ I.a, we get I.a = I.b
    exact le_antisymm hab h_ba
  · -- If ¬(I.a ≤ I.b), then I.a > I.b
    push_neg at hab
    -- When I = Icc I.a I.b with I.a > I.b, we have I.toSet = ∅
    have h_empty : I.toSet = ∅ := by
      rw [hI]
      simp [BoundedInterval.toSet]
      exact Set.Icc_eq_empty (not_le.mpr hab)
    -- But this contradicts the nonempty hypothesis!
    exfalso
    rw [h_empty] at h_nonempty
    exact Set.not_nonempty_empty h_nonempty

/-- Definition 1.1.15 (Riemann integrability) -/
-- For a Riemann integrable function, the Riemann sums converge to the integral value.
lemma riemann_integral_of_integrable {f:ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) : riemann_integral_eq f I (riemannIntegral f I) := by
  -- Strategy: Since `h : RiemannIntegrableOn f I` means `∃ R, riemann_integral_eq f I R`,
  -- and `riemannIntegral f I` is defined as `h.2.2.choose` (the witness chosen by Classical.choose),
  -- we need to show that `riemann_integral_eq f I h.2.2.choose`, which is exactly `h.2.2.choose_spec`.
  unfold riemannIntegral
  convert h.2.2.choose_spec using 2
  -- Split on the if condition (which is `RiemannIntegrableOn f I`, true by hypothesis `h`)
  split_ifs
  -- In the `then` branch, we have `h.2.choose = h.2.choose` by reflexivity
  · rfl

/-- Definition 1.1.15 (Riemann integrability) -/
-- Characterization of the Riemann integral: R is the integral iff the Riemann sums converge to R.
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
      have h_eq : I.a = I.b := eq_of_length_zero_of_Icc h.1 h_len h.2.1
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
-- ε-δ characterization: Riemann sums converge to R iff for all ε > 0, there exists δ > 0 such that partitions with norm ≤ δ have Riemann sums within ε of R.
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

/-- Definition 1.1.15.  (Riemann integrability)  -/
-- Any function is Riemann integrable on a degenerate interval [a,a] with integral zero.
lemma RiemannIntegrable.of_zero_length (f: ℝ → ℝ) {I: BoundedInterval} {a : ℝ} (h: I = Icc a a) : RiemannIntegrableOn f I ∧ riemannIntegral f I = 0 := by
  -- First establish basic facts from h : I = Icc a a
  have ha : I.a = a := by simp [h]
  have hb : I.b = a := by simp [h]
  have h_eq : I.a = I.b := by rw [ha, hb]
  have h_len : |I|ₗ = 0 := by
    unfold BoundedInterval.length
    simp [ha, hb]
  -- Show I = Icc I.a I.b
  have hIcc : I = Icc I.a I.b := by rw [ha, hb]; exact h
  -- Show I.toSet is nonempty (it's {a})
  have h_nonempty : I.toSet.Nonempty := by
    rw [h]
    simp [BoundedInterval.toSet]
  -- Show riemann_integral_eq f I 0 (all Riemann sums are 0, so limit is 0)
  have h_integral_zero : riemann_integral_eq f I 0 := by
    rw [riemann_integral_eq_iff]
    intro ε hε
    use 1, one_pos
    intro n P _
    have h_sum_zero : P.RiemannSum f = 0 := riemann_sum_eq_zero_of_zero_length h_len P
    simp [h_sum_zero]
    linarith
  -- Construct RiemannIntegrableOn
  have h_integrable : RiemannIntegrableOn f I := ⟨hIcc, h_nonempty, 0, h_integral_zero⟩
  constructor
  · exact h_integrable
  · -- Show riemannIntegral f I = 0 using uniqueness
    exact ((riemann_integral_eq_iff_of_integrable h_integrable 0).mp h_integral_zero).symm

/-- Helper: Modify a tagged partition by changing one tag -/
def TaggedPartition.changeTag {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n)
    (k: Fin n) (t: ℝ) (ht: P.x k.castSucc ≤ t ∧ t ≤ P.x k.succ) : TaggedPartition I n where
  x := P.x
  x_tag := Function.update P.x_tag k t
  x_start := P.x_start
  x_end := P.x_end
  x_mono := P.x_mono
  x_tag_between := fun i => by
    by_cases hik : i = k
    · subst hik; rw [Function.update_self]; exact ht
    · rw [Function.update_of_ne hik]; exact P.x_tag_between i

/-- The Riemann sum difference when changing one tag -/
lemma TaggedPartition.RiemannSum_changeTag_sub {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n)
    (f: ℝ → ℝ) (k: Fin n) (t: ℝ) (ht: P.x k.castSucc ≤ t ∧ t ≤ P.x k.succ) :
    (P.changeTag k t ht).RiemannSum f - P.RiemannSum f = (f t - f (P.x_tag k)) * P.delta k := by
  -- delta is unchanged by changeTag since x is unchanged
  have h_delta : ∀ i, (P.changeTag k t ht).delta i = P.delta i := fun _ => rfl
  unfold TaggedPartition.RiemannSum
  rw [← Finset.sum_sub_distrib]
  have h_terms : ∀ i, f ((P.changeTag k t ht).x_tag i) * (P.changeTag k t ht).delta i - f (P.x_tag i) * P.delta i =
      if i = k then (f t - f (P.x_tag k)) * P.delta k else 0 := by
    intro i
    rw [h_delta]
    simp only [TaggedPartition.changeTag]
    by_cases hik : i = k
    · subst hik; simp only [Function.update_self, if_true]; ring
    · simp only [Function.update_of_ne hik, hik, if_false]; ring
  conv_lhs => rw [Finset.sum_congr rfl (fun i _ => h_terms i)]
  rw [Finset.sum_ite_eq' Finset.univ k]
  simp

/-- For a uniform partition, delta is constant -/
lemma TaggedPartition.uniform_delta {I: BoundedInterval} {n: ℕ} (hn: n > 0) (hI: I = Icc I.a I.b)
    (hab: I.a < I.b) (i: Fin n) :
    (TaggedPartition.uniform I n hn hI hab).delta i = (I.b - I.a) / n := by
  unfold TaggedPartition.delta TaggedPartition.uniform
  simp only
  rw [Fin.val_succ, show i.castSucc.val = i.val from rfl]
  field_simp
  ring

/-- For any x in [a,b], find the subinterval index containing x -/
noncomputable def findSubintervalIndex (lo hi : ℝ) (n : ℕ) (hn : n > 0) (x : ℝ) (_hx : lo ≤ x ∧ x ≤ hi) : Fin n :=
  let k := min (Nat.floor ((x - lo) / ((hi - lo) / n))) (n - 1)
  ⟨k, by omega⟩

/-- The found index correctly brackets x -/
lemma findSubintervalIndex_spec (lo hi : ℝ) (n : ℕ) (hn : n > 0) (hlohi : lo < hi) (x : ℝ) (hx : lo ≤ x ∧ x ≤ hi) :
    let k := findSubintervalIndex lo hi n hn x hx
    let Δ := (hi - lo) / n
    lo + k.val * Δ ≤ x ∧ x ≤ lo + (k.val + 1) * Δ := by
  simp only [findSubintervalIndex]
  set Δ := (hi - lo) / n with hΔ_def
  have hΔ_pos : 0 < Δ := div_pos (sub_pos.mpr hlohi) (Nat.cast_pos.mpr hn)
  set k := min (Nat.floor ((x - lo) / Δ)) (n - 1) with hk_def
  constructor
  · -- Lower bound: lo + k * Δ ≤ x
    have h_floor_le : ↑(Nat.floor ((x - lo) / Δ)) * Δ ≤ x - lo := by
      have h_nonneg : 0 ≤ (x - lo) / Δ := div_nonneg (by linarith [hx.1]) (le_of_lt hΔ_pos)
      have h_le : (Nat.floor ((x - lo) / Δ) : ℝ) ≤ (x - lo) / Δ := Nat.floor_le h_nonneg
      calc ↑(Nat.floor ((x - lo) / Δ)) * Δ ≤ (x - lo) / Δ * Δ := by
             apply mul_le_mul_of_nonneg_right h_le (le_of_lt hΔ_pos)
           _ = x - lo := by field_simp
    have h_k_le_floor : k ≤ Nat.floor ((x - lo) / Δ) := Nat.min_le_left _ _
    calc lo + k * Δ ≤ lo + Nat.floor ((x - lo) / Δ) * Δ := by
           apply add_le_add_left
           apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_k_le_floor) (le_of_lt hΔ_pos)
         _ ≤ lo + (x - lo) := by linarith [h_floor_le]
         _ = x := by ring
  · -- Upper bound: x ≤ lo + (k + 1) * Δ
    by_cases h_at_end : x = hi
    · -- If x = hi, then k = n - 1 and (k + 1) * Δ = n * Δ = hi - lo
      have h_ne : hi - lo ≠ 0 := ne_of_gt (sub_pos.mpr hlohi)
      have h_k_eq : k = n - 1 := by
        simp only [hk_def, h_at_end]
        apply Nat.min_eq_right
        have h_ratio : (hi - lo) / Δ = n := by
          rw [hΔ_def]
          field_simp [h_ne]
        rw [h_ratio]
        rw [Nat.floor_natCast (R := ℝ)]
        omega
      rw [h_k_eq]
      have h_cast : (↑(n - 1) + 1 : ℝ) = n := by
        rw [Nat.cast_sub (Nat.one_le_of_lt hn)]
        ring
      rw [h_cast, h_at_end]
      have h_eq : hi = lo + (n : ℝ) * Δ := by
        calc hi = lo + (hi - lo) := by ring
             _ = lo + n * Δ := by rw [hΔ_def]; field_simp [h_ne]
      linarith [h_eq]
    · -- If x < hi, use floor property
      have h_x_lt_hi : x < hi := lt_of_le_of_ne hx.2 h_at_end
      -- When x < hi, floor((x-lo)/Δ) ≤ n - 1, so k = floor
      have h_floor_le_n_sub_1 : Nat.floor ((x - lo) / Δ) ≤ n - 1 := by
        have h_ratio_lt : (x - lo) / Δ < n := by
          rw [div_lt_iff₀ hΔ_pos, hΔ_def]
          field_simp
          linarith
        have h_nonneg : 0 ≤ (x - lo) / Δ := div_nonneg (by linarith [hx.1]) (le_of_lt hΔ_pos)
        have h_floor_lt : Nat.floor ((x - lo) / Δ) < n := (Nat.floor_lt h_nonneg).mpr h_ratio_lt
        omega
      have h_k_eq_floor : k = Nat.floor ((x - lo) / Δ) := by
        simp only [hk_def]
        exact Nat.min_eq_left h_floor_le_n_sub_1
      have h_lt_floor : (x - lo) / Δ < ↑(Nat.floor ((x - lo) / Δ)) + 1 := Nat.lt_floor_add_one _
      have h_lt : x < lo + (↑k + 1) * Δ := by
        calc x = lo + (x - lo) := by ring
             _ = lo + ((x - lo) / Δ) * Δ := by field_simp
             _ < lo + (↑(Nat.floor ((x - lo) / Δ)) + 1) * Δ := by
                 apply add_lt_add_left
                 apply mul_lt_mul_of_pos_right h_lt_floor hΔ_pos
             _ = lo + (↑k + 1) * Δ := by rw [h_k_eq_floor]
      linarith [h_lt]

/-- Definition 1.1.15 -/
theorem RiemannIntegrable.bounded {f: ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) : ∃ M, ∀ x ∈ I, |f x| ≤ M := by
  obtain ⟨hIcc, h_nonempty, R, hR⟩ := h
  -- Handle zero-length case separately
  by_cases hab : I.a = I.b
  · -- Zero-length case: I.toSet = {I.a}
    use |f I.a|
    intro x hx
    rw [hIcc] at hx
    simp [BoundedInterval.toSet, Set.mem_Icc] at hx
    have hxa : x = I.a := le_antisymm (by linarith [hx.1, hx.2, hab]) hx.1
    rw [hxa]
  · -- Positive-length case
    push_neg at hab
    have h_lt : I.a < I.b := by
      rw [hIcc] at h_nonempty
      simp only [BoundedInterval.toSet] at h_nonempty
      obtain ⟨x, hax, hxb⟩ := h_nonempty
      by_contra h_not_lt
      push_neg at h_not_lt
      have : I.b < I.a := lt_of_le_of_ne h_not_lt (Ne.symm hab)
      linarith
    -- Use ε-δ characterization with ε = 1
    rw [riemann_integral_eq_iff] at hR
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := hR 1 one_pos
    -- Choose n large enough that (b-a)/n ≤ δ
    have h_width_pos : 0 < I.b - I.a := sub_pos.mpr h_lt
    obtain ⟨N, hN⟩ := exists_nat_gt ((I.b - I.a) / δ)
    have hN_pos : 0 < N := by
      by_contra h_not_pos
      push_neg at h_not_pos
      interval_cases N
      simp at hN
      linarith [div_pos h_width_pos hδ_pos]
    have h_norm_le : (I.b - I.a) / N ≤ δ := by
      have h_ratio_pos : 0 < (I.b - I.a) / δ := div_pos h_width_pos hδ_pos
      have h_N_pos_real : 0 < (N : ℝ) := Nat.cast_pos.mpr hN_pos
      rw [div_le_iff₀ h_N_pos_real]
      have h1 : (I.b - I.a) / δ < N := hN
      have h2 : I.b - I.a < N * δ := by
        rwa [div_lt_iff₀ hδ_pos] at h1
      linarith
    -- Construct uniform partition
    let P := TaggedPartition.uniform I N hN_pos hIcc h_lt
    -- The partition has norm = (b-a)/N ≤ δ
    have h_P_norm : P.norm = (I.b - I.a) / N := TaggedPartition.uniform_norm I N hN_pos hIcc h_lt
    have h_P_norm_le : P.norm ≤ δ := by rw [h_P_norm]; exact h_norm_le
    -- For contradiction, assume f is unbounded
    by_contra h_unbounded
    push_neg at h_unbounded
    -- h_unbounded : ∀ M, ∃ x ∈ I.toSet, M < |f x|
    -- Let K = sum of |f| at partition left endpoints (a bound we'll use)
    let K := ∑ j : Fin N, |f (P.x_tag j)|
    -- Choose large enough M to get contradiction
    let idx0 : Fin N := ⟨0, hN_pos⟩
    let M := K + |f (P.x_tag idx0)| + 3 * N / (I.b - I.a) + |R| + 10
    obtain ⟨x₀, hx₀_in, hx₀_large⟩ := h_unbounded M
    -- Find which subinterval contains x₀
    have hx₀_in' : I.a ≤ x₀ ∧ x₀ ≤ I.b := by
      rw [hIcc] at hx₀_in
      simp [BoundedInterval.toSet, Set.mem_Icc] at hx₀_in
      exact hx₀_in
    let k := findSubintervalIndex I.a I.b N hN_pos x₀ hx₀_in'
    -- x₀ is in the k-th subinterval of the partition
    have h_x₀_in_k := findSubintervalIndex_spec I.a I.b N hN_pos h_lt x₀ hx₀_in'
    -- The uniform partition has x k.castSucc = a + k * Δ
    have h_P_x : ∀ i : Fin (N + 1), P.x i = I.a + (I.b - I.a) * i.val / N := fun i => rfl
    have h_Δ : (I.b - I.a) / N = P.delta ⟨0, hN_pos⟩ := (TaggedPartition.uniform_delta hN_pos hIcc h_lt ⟨0, hN_pos⟩).symm
    -- Show x₀ is in [P.x k.castSucc, P.x k.succ]
    have h_x₀_bracket : P.x k.castSucc ≤ x₀ ∧ x₀ ≤ P.x k.succ := by
      constructor
      · calc P.x k.castSucc = I.a + (I.b - I.a) * k.val / N := h_P_x k.castSucc
             _ = I.a + k.val * ((I.b - I.a) / N) := by ring
             _ ≤ x₀ := h_x₀_in_k.1
      · have h_succ : (k.succ.val : ℝ) = k.val + 1 := by simp [Fin.val_succ]
        calc x₀ ≤ I.a + (k.val + 1) * ((I.b - I.a) / N) := h_x₀_in_k.2
             _ = I.a + (I.b - I.a) * (k.val + 1) / N := by ring
             _ = I.a + (I.b - I.a) * k.succ.val / N := by rw [← h_succ]
             _ = P.x k.succ := (h_P_x k.succ).symm
    -- Construct P₂ by changing tag k to x₀
    let P₂ := P.changeTag k x₀ h_x₀_bracket
    -- P₂ has the same norm as P (same x values, so same deltas)
    have h_P₂_delta_eq : ∀ i, P₂.delta i = P.delta i := fun i => rfl
    have h_P₂_norm_le : P₂.norm ≤ δ := by
      have h_eq : P₂.norm = P.norm := by
        unfold TaggedPartition.norm
        have h_fun_eq : P₂.delta = P.delta := funext h_P₂_delta_eq
        rw [h_fun_eq]
      rw [h_eq]
      exact h_P_norm_le
    -- Get bounds on both Riemann sums
    have h_S₁ : |P.RiemannSum f - R| ≤ 1 := hδ_bound N P h_P_norm_le
    have h_S₂ : |P₂.RiemannSum f - R| ≤ 1 := hδ_bound N P₂ h_P₂_norm_le
    -- The difference of Riemann sums
    have h_diff := TaggedPartition.RiemannSum_changeTag_sub P f k x₀ h_x₀_bracket
    -- |S₂ - S₁| ≤ 2 by triangle inequality
    have h_diff_le_2 : |P₂.RiemannSum f - P.RiemannSum f| ≤ 2 := by
      have h_tri := abs_sub_le (P₂.RiemannSum f) R (P.RiemannSum f)
      -- h_tri : |P₂.RiemannSum f - P.RiemannSum f| ≤ |P₂.RiemannSum f - R| + |R - P.RiemannSum f|
      rw [abs_sub_comm R (P.RiemannSum f)] at h_tri
      calc |P₂.RiemannSum f - P.RiemannSum f|
           ≤ |P₂.RiemannSum f - R| + |P.RiemannSum f - R| := h_tri
         _ ≤ 1 + 1 := add_le_add h_S₂ h_S₁
         _ = 2 := by ring
    -- But |S₂ - S₁| = |f(x₀) - f(tag_k)| * delta_k
    rw [h_diff] at h_diff_le_2
    -- delta_k = (b - a) / N
    have h_delta_k : P.delta k = (I.b - I.a) / N := TaggedPartition.uniform_delta hN_pos hIcc h_lt k
    -- |f(x₀) - f(tag_k)| ≤ 2 / delta_k = 2N / (b - a)
    have h_Δ_pos : 0 < P.delta k := by
      rw [h_delta_k]
      exact div_pos h_width_pos (Nat.cast_pos.mpr hN_pos)
    have h_f_diff : |f x₀ - f (P.x_tag k)| ≤ 2 / P.delta k := by
      have h_eq := abs_mul (f x₀ - f (P.x_tag k)) (P.delta k)
      rw [abs_of_pos h_Δ_pos] at h_eq
      have h_le : |f x₀ - f (P.x_tag k)| * P.delta k ≤ 2 := by rw [← h_eq]; exact h_diff_le_2
      rwa [le_div_iff₀ h_Δ_pos]
    -- |f(x₀)| ≤ |f(tag_k)| + 2N / (b - a)
    have h_f_x₀_bound : |f x₀| ≤ |f (P.x_tag k)| + 2 * N / (I.b - I.a) := by
      have h1 : |f x₀| - |f (P.x_tag k)| ≤ |f x₀ - f (P.x_tag k)| := abs_sub_abs_le_abs_sub _ _
      have h2 : |f x₀ - f (P.x_tag k)| ≤ 2 / P.delta k := h_f_diff
      rw [h_delta_k] at h2
      have h3 : 2 / ((I.b - I.a) / N) = 2 * N / (I.b - I.a) := by field_simp
      rw [h3] at h2
      linarith
    -- But |f(tag_k)| ≤ K (sum includes this term)
    have h_tag_k_le_K : |f (P.x_tag k)| ≤ K := by
      apply Finset.single_le_sum (f := fun j => |f (P.x_tag j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ k)
    -- So |f(x₀)| ≤ K + 2N / (b - a)
    have h_f_x₀_final : |f x₀| ≤ K + 2 * N / (I.b - I.a) := by linarith
    -- But we chose |f(x₀)| > M = K + ... + 3N / (b - a) + ...
    have h_contradiction : M < |f x₀| := hx₀_large
    -- M > K + 2N / (b - a), so |f(x₀)| > K + 2N / (b - a)
    have h_M_lower : K + 2 * N / (I.b - I.a) < M := by
      -- Goal: K + 2*N/(b-a) < K + |f(tag0)| + 3*N/(b-a) + |R| + 10
      -- Simplifies to: 2*N/(b-a) < |f(tag0)| + 3*N/(b-a) + |R| + 10
      -- Which holds since 3*N/(b-a) > 2*N/(b-a) and other terms are nonnegative
      have h_N_div_pos : 0 < (N : ℝ) / (I.b - I.a) := div_pos (Nat.cast_pos.mpr hN_pos) h_width_pos
      have h_abs_nonneg : 0 ≤ |f (P.x_tag idx0)| := abs_nonneg _
      have h_R_nonneg : 0 ≤ |R| := abs_nonneg _
      have h_step1 : K + 2 * N / (I.b - I.a) < K + 3 * N / (I.b - I.a) := by
        have : 2 * (N : ℝ) / (I.b - I.a) < 3 * N / (I.b - I.a) := by
          apply div_lt_div_of_pos_right _ h_width_pos
          have h_N_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
          linarith
        linarith
      calc K + 2 * N / (I.b - I.a)
           < K + 3 * N / (I.b - I.a) := h_step1
         _ ≤ K + |f (P.x_tag idx0)| + 3 * N / (I.b - I.a) := by linarith
         _ ≤ K + |f (P.x_tag idx0)| + 3 * N / (I.b - I.a) + |R| := by linarith
         _ < K + |f (P.x_tag idx0)| + 3 * N / (I.b - I.a) + |R| + 10 := by linarith
    linarith

@[ext]
-- A function that is constant on each interval in a partition of I.
structure PiecewiseConstantFunction (I: BoundedInterval) where
  f : ℝ → ℝ
  T : Finset BoundedInterval
  c : T → ℝ
  disjoint: T.toSet.PairwiseDisjoint BoundedInterval.toSet
  cover : I.toSet = ⋃ J ∈ T, J.toSet
  const : ∀ J:T, ∀ x ∈ J.val, f x = c J

-- Two functions agree if they are equal on the interval I.
abbrev PiecewiseConstantFunction.agreesWith {I: BoundedInterval} (F: PiecewiseConstantFunction I) (f: ℝ → ℝ) : Prop := I.toSet.EqOn f F.f

-- A function is piecewise constant on I if it can be represented as a piecewise constant function.
def PiecewiseConstantOn (f: ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ F: PiecewiseConstantFunction I, F.agreesWith f

-- The integral of a piecewise constant function: sum of (constant value × interval length) over all intervals.
def PiecewiseConstantFunction.integral {I: BoundedInterval} (g: PiecewiseConstantFunction I) : ℝ :=
  ∑ J : g.T, g.c J * |J|ₗ

/-- Exercise 1.1.20 (Piecewise constant functions) -/
-- The integral is well-defined: different representations of the same piecewise constant function have the same integral.
theorem PiecewiseConstantFunction.integral_eq (f: ℝ → ℝ) {I: BoundedInterval} (F F': PiecewiseConstantFunction I) (hF: F.agreesWith f) (hF': F'.agreesWith f) : F.integral = F'.integral := by sorry

-- The integral of a piecewise constant function on I.
noncomputable def PiecewiseConstantOn.integral (f: ℝ → ℝ) {I: BoundedInterval} (h: PiecewiseConstantOn f I) : ℝ := h.choose.integral

/-- Exercise 1.1.20 (Piecewise constant functions) -/
-- The integral of a piecewise constant function equals the integral of any of its representations.
theorem PiecewiseConstantOn.integral_eq (f: ℝ → ℝ) {I: BoundedInterval} (h: PiecewiseConstantOn f I) (F: PiecewiseConstantFunction I) (hF: F.agreesWith f) : h.integral = F.integral := by sorry

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
-- A scalar multiple of a piecewise constant function is piecewise constant.
theorem PiecewiseConstantOn.smul {I: BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by sorry

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
-- The integral is linear: integral(c * f) = c * integral(f).
theorem PiecewiseConstantFunction.integral_smul {I:BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) : (h.smul c).integral = h.integral := by sorry

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
-- The sum of two piecewise constant functions is piecewise constant.
theorem PiecewiseConstantOn.add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I := by sorry

/-- Exercise 1.1.21 (a) (Linearity of the piecewise constant integral) -/
-- The integral is linear: integral(f + g) = integral(f) + integral(g).
theorem PiecewiseConstantFunction.integral_add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : (hf.add hg).integral = hf.integral + hg.integral := by sorry

/-- Exercise 1.1.21 (b) (Monotonicity of the piecewise constant integral) -/
-- The integral is monotone: if f ≤ g pointwise, then integral(f) ≤ integral(g).
theorem PiecewiseConstantFunction.integral_mono {I: BoundedInterval} {f g: ℝ → ℝ} (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x): hf.integral ≤ hg.integral := by sorry

/-- Exercise 1.1.21 (c) (Piecewise constant integral of indicator functions) -/
-- The indicator function of an elementary set is piecewise constant.
theorem PiecewiseConstantOn.indicator_of_elem (I: BoundedInterval) {E:Set ℝ} (hE: IsElementary (Real.equiv_EuclideanSpace' '' E) ) : PiecewiseConstantOn E.indicator' I := by sorry

/-- Exercise 1.1.21 (c) (Piecewise constant integral of indicator functions) -/
-- The integral of an indicator function of an elementary set equals its elementary measure.
theorem PiecewiseConstantFunction.integral_of_elem {I: BoundedInterval} {E:Set ℝ} (hE: IsElementary (Real.equiv_EuclideanSpace' '' E) ) (hsub: E ⊆ I.toSet) : (PiecewiseConstantOn.indicator_of_elem I hE).integral = hE.measure := by sorry

/-- Definition 1.1.6 (Darboux integral) -/
-- The lower Darboux integral: supremum of integrals of piecewise constant functions that underestimate f.
noncomputable def LowerDarbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := sSup { R | ∃ g: PiecewiseConstantFunction I, g.integral = R ∧ ∀ x ∈ I.toSet, g.f x ≤ f x }

/-- Definition 1.1.6 (Darboux integral) -/
-- The upper Darboux integral: infimum of integrals of piecewise constant functions that overestimate f.
noncomputable def UpperDarbouxIntegral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := sInf { R | ∃ h: PiecewiseConstantFunction I, h.integral = R ∧ ∀ x ∈ I.toSet, f x ≤ h.f x }

namespace PiecewiseConstantFunction
/-- Helper: Construct a constant piecewise constant function with a given value -/
def mkConst (I: BoundedInterval) (c: ℝ) : PiecewiseConstantFunction I where
  f := fun _ => c
  T := {I}
  c := fun _ => c
  disjoint := by simp [Set.pairwiseDisjoint_singleton]
  cover := by simp
  const := by intro J x hx; rfl

/-- Helper: The integral of a constant piecewise constant function -/
lemma integral_mkConst (I: BoundedInterval) (c: ℝ) :
    (PiecewiseConstantFunction.mkConst I c).integral = c * |I|ₗ := by
  unfold PiecewiseConstantFunction.integral PiecewiseConstantFunction.mkConst
  simp [Finset.sum_singleton]

/-- Helper: Construct the negation of a piecewise constant function -/
def neg {I: BoundedInterval} (g: PiecewiseConstantFunction I) : PiecewiseConstantFunction I where
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
lemma integral_neg {I: BoundedInterval} (g: PiecewiseConstantFunction I) :
    g.neg.integral = -g.integral := by
  unfold PiecewiseConstantFunction.integral PiecewiseConstantFunction.neg
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext J
  ring

/-- Helper: Convert a PiecewiseConstantFunction to PiecewiseConstantOn and relate integrals -/
lemma to_PiecewiseConstantOn {I: BoundedInterval} (g: PiecewiseConstantFunction I) :
    ∃ (h: PiecewiseConstantOn g.f I), h.integral = g.integral := by
  have hg_agrees : g.agreesWith g.f := fun x hx => rfl
  use ⟨g, hg_agrees⟩
  exact PiecewiseConstantOn.integral_eq g.f ⟨g, hg_agrees⟩ g hg_agrees

/-- Helper: Apply integral_mono between two PiecewiseConstantFunctions via PiecewiseConstantOn -/
lemma integral_mono' {I: BoundedInterval}
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

end PiecewiseConstantFunction


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
-- For any bounded function, the lower Darboux integral is at most the upper Darboux integral.
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
-- A function is Darboux integrable if it is bounded and its lower and upper Darboux integrals coincide.
noncomputable def DarbouxIntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop := (I = Icc I.a I.b) ∧ ∃ M, ∀ x ∈ I, |f x| ≤ M ∧ LowerDarbouxIntegral f I = UpperDarbouxIntegral f I

/-- We give the Darboux integral the "junk" value of the lower Darboux integral when the function is not integrable. -/
-- The Darboux integral: equals the common value if integrable, otherwise the lower Darboux integral.
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
-- For the negation of a function, the upper Darboux integral of -f equals minus the lower Darboux integral of f.
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
-- Riemann integrability is equivalent to Darboux integrability for bounded functions.
lemma RiemannIntegrableOn.iff_darbouxIntegrable {f:ℝ → ℝ} {I: BoundedInterval} (hbound: ∃ M, ∀ x ∈ I, |f x| ≤ M) : RiemannIntegrableOn f I ↔ DarbouxIntegrableOn f I := by sorry

/-- Exercise 1.1.22 -/
-- For Riemann integrable functions, the Riemann integral equals the Darboux integral.
lemma riemann_integral_eq_darboux_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: RiemannIntegrableOn f I) : riemannIntegral f I = darbouxIntegral f I := by sorry

/-- Exercise 1.1.23 -/
-- Any function continuous on a closed interval is Riemann integrable.
lemma RiemannIntegrableOn.continuous {f:ℝ → ℝ} {I: BoundedInterval} (hI: I = Icc I.a I.b) (hcont: ContinuousOn f I.toSet) : RiemannIntegrableOn f I := by sorry

-- A function that is continuous on each piece of a partition is Riemann integrable on the whole interval.
lemma RiemannIntegrableOn.piecewise_continuous {f:ℝ → ℝ} {I: BoundedInterval} (hI: I = Icc I.a I.b)
 (T: Finset BoundedInterval)  (hdisjoint: T.toSet.PairwiseDisjoint BoundedInterval.toSet)
 (hcover : I.toSet = ⋃ J ∈ T, J.toSet) (hcont: ∀ J ∈ T, ContinuousOn f J.toSet) : RiemannIntegrableOn f I := by sorry

/-- Exercise 1.1.24 (a) (Linearity of the piecewise constant integral) -/
-- A scalar multiple of a Riemann integrable function is Riemann integrable.
theorem RiemannIntegrableOn.smul {I: BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: RiemannIntegrableOn f I) : RiemannIntegrableOn (c • f) I := by sorry

/-- Exercise 1.1.24 (a) (Linearity of the piecewise constant integral) -/
-- The integral of a scalar multiple: integral(c * f) = c * integral(f).
theorem riemann_integral_smul {I:BoundedInterval} (c:ℝ) {f: ℝ → ℝ} (h: RiemannIntegrableOn f I) : riemannIntegral (c • f) = c • (riemannIntegral f) := by sorry

/-- Exercise 1.1.24 (a) (Linearity of the piecewise constant integral) -/
-- The sum of two Riemann integrable functions is Riemann integrable.
theorem RiemannIntegrableOn.add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) : RiemannIntegrableOn (f + g) I := by sorry

/-- Exercise 1.1.24 (a) (Linearity of the piecewise constant integral) -/
-- The integral of a sum: integral(f + g) = integral(f) + integral(g).
theorem riemann_integral_add {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) : riemannIntegral (f+g) = riemannIntegral f + riemannIntegral g := by sorry

/-- Exercise 1.1.24 (b) (Monotonicity of the piecewise constant integral) -/
-- The integral is monotone: if f ≤ g pointwise, then integral(f) ≤ integral(g).
theorem riemann_integral_mono {I: BoundedInterval} {f g: ℝ → ℝ} (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x): riemannIntegral f ≤ riemannIntegral g := by sorry

/-- Exercise 1.1.24 (c) (Indicator functions) -/
-- The indicator function of a Jordan measurable set is Riemann integrable.
theorem RiemannIntegrableOn.indicator_of_elem (I: BoundedInterval) {E:Set ℝ} (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E) ) : RiemannIntegrableOn E.indicator' I := by sorry

/-- Exercise 1.1.24 (c) (Piecewise constant integral of indicator functions) -/
-- The integral of an indicator function equals the measure of the set it indicates.
theorem riemann_integral_of_elem {I: BoundedInterval} {E:Set ℝ} (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E) ) (hsub: E ⊆ I.toSet) : riemannIntegral E.indicator' I = hE.measure := by sorry

/-- Exercise 1.1.24 (Uniqueness) -/
-- The Riemann integral is the unique integral satisfying linearity, monotonicity, and normalization on indicator functions.
theorem riemann_integral_unique {I: BoundedInterval} (integ: (ℝ → ℝ) → ℝ)
  (hsmul: ∀ (c:ℝ) (f: ℝ → ℝ) (hf: RiemannIntegrableOn f I), integ (c • f) = c • (integ f))
  (hadd: ∀ (f g: ℝ → ℝ) (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I), integ (f + g) = integ f + integ g)
  (hmono: ∀ (f g: ℝ → ℝ) (hf: RiemannIntegrableOn f I) (hg: RiemannIntegrableOn g I) (hmono: ∀ x ∈ I.toSet, f x ≤ g x), integ f ≤ integ g)
  (hindicator: ∀ (E:Set ℝ) (hE: JordanMeasurable (Real.equiv_EuclideanSpace' '' E) ) (hsub: E ⊆ I.toSet), integ E.indicator' = hE.measure) :
  ∀ f, RiemannIntegrableOn f I → integ f = riemannIntegral f I := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
-- The region under the graph of a Riemann integrable function is Jordan measurable.
theorem RiemannIntegrableOn.measurable_upper {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ 0 ≤ p 1 ∧ p 1 ≤ f (p 0) } := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
-- The region below the graph of a Riemann integrable function is Jordan measurable.
theorem RiemannIntegrableOn.measurable_lower {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ f (p 0) ≤ p 1 ∧ p 1 ≤ 0 } := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
-- A function is Riemann integrable iff the regions above and below its graph are both Jordan measurable.
theorem JordanMeasurable.iff_integrable {I: BoundedInterval} (hI: I = Icc I.a I.b)
  {f: ℝ → ℝ} (hf: ∃ M, ∀ x ∈ I.toSet, |f x| ≤ M) : RiemannIntegrableOn f I ↔
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ 0 ≤ p 1 ∧ p 1 ≤ f (p 0) } ∧
  JordanMeasurable { p:EuclideanSpace' 2 | p 0 ∈ I.toSet ∧ f (p 0) ≤ p 1 ∧ p 1 ≤ 0 }
  := by sorry

/-- Exercise 1.1.25 (Area interpretation of Riemann integral) -/
-- The Riemann integral equals the difference between the measures of the upper and lower regions.
theorem RiemannIntegrableOn.eq_measure {I: BoundedInterval}
  {f: ℝ → ℝ} (hfint: RiemannIntegrableOn f I) :
  riemannIntegral f I = hfint.measurable_upper.measure - hfint.measurable_lower.measure := by sorry

/- Exercise 1.1.26: Extend the definition of the Riemann and Darboux integrals to higher dimensions, in such a way that analogues of all the previous results hold; state and prove those analogues. -/
