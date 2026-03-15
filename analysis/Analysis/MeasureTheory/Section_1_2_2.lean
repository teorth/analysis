import Analysis.MeasureTheory.Section_1_2_1

/-!
# Introduction to Measure Theory, Section 1.2.2: Lebesgue measurability

A companion to (the introduction to) Section 1.2.2 of the book "An introduction to Measure Theory".

-/

/-- Lemma 1.2.13(i) (Every open set is Lebesgue measurable). -/
theorem IsOpen.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsOpen E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, choose U = E itself
  -- Since E is already open, U \ E = E \ E = ∅, and m*(∅) = 0 ≤ ε
  intro ε hε
  -- Witness: U = E
  use E
  constructor
  · -- E is open (given)
    exact hE
  constructor
  · -- E ⊆ E (reflexivity)
    rfl
  · -- Show m*(E \ E) ≤ ε
    have h_empty : E \ E = ∅ := Set.diff_self
    rw [h_empty]
    have h_zero : Lebesgue_outer_measure (∅ : Set (EuclideanSpace' d)) = 0 :=
      Lebesgue_outer_measure.of_empty d
    rw [h_zero]
    exact le_of_lt hε

/-- Helper: For a finset of pairwise almost disjoint dyadic boxes, the outer measure of their
    union equals the sum of their volumes. -/
private lemma Lebesgue_outer_measure.sum_of_almost_disjoint_finset {d : ℕ} (_hd_pos : 0 < d)
    {t : Finset ℕ} {Q : ℕ → Box d} (_hQ_dyadic : ∀ i, (Q i).IsDyadic)
    (hQ : Pairwise (Function.onFun AlmostDisjoint Q)) :
    Lebesgue_outer_measure (⋃ i ∈ t, (Q i).toSet) = ∑ i ∈ t, ((Q i).volume : EReal) := by
  -- Direct proof using elementary set theory (avoids flawed union_of_separated approach)
  -- Convert to Fin (t.card) indexed boxes via Finset.equivFin
  let equiv := t.equivFin
  let B' : Fin t.card → Box d := fun i => Q (equiv.symm i).val
  -- Show the biUnion equals the iUnion over Fin t.card
  have h_eq : (⋃ i ∈ t, (Q i).toSet) = ⋃ (i : Fin t.card), (B' i).toSet := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_iUnion, B']
    constructor
    · intro ⟨i, hi, hx⟩
      exact ⟨equiv ⟨i, hi⟩, by simp [hx]⟩
    · intro ⟨i, hx⟩
      exact ⟨(equiv.symm i).val, (equiv.symm i).property, hx⟩
  rw [h_eq]
  -- The finite union is elementary
  have hElem : IsElementary (⋃ (i : Fin t.card), (B' i).toSet) :=
    IsElementary.iUnion_boxes B'
  -- Almost-disjointness for Fin-indexed boxes
  have hB'_disj : Pairwise (Function.onFun AlmostDisjoint B') := by
    intro i j h_ne
    simp only [Function.onFun, B']
    apply hQ
    intro h_eq
    have heq : equiv.symm i = equiv.symm j := Subtype.ext h_eq
    exact h_ne (equiv.symm.injective heq)
  -- Apply IsElementary.almost_disjoint: measure = ∑ volumes
  have h_measure := IsElementary.almost_disjoint hElem B' rfl hB'_disj
  -- Convert measure to outer measure
  have h_outer := Lebesgue_outer_measure.elementary _ hElem
  -- Sum conversion: ∑ i : Fin t.card, (B' i).volume = ∑ i ∈ t, (Q i).volume
  have h_sum_eq : ∑ i : Fin t.card, (B' i).volume = ∑ i ∈ t, (Q i).volume := by
    conv_rhs => rw [← Finset.sum_attach]
    refine Finset.sum_equiv equiv.symm ?_ ?_
    · intro i; simp [Finset.mem_univ, Finset.mem_attach]
    · intro i _; simp only [B']
  rw [h_outer, h_measure, h_sum_eq]
  -- Now need: ↑(∑ i ∈ t, (Q i).volume) = ∑ i ∈ t, ↑(Q i).volume
  exact EReal.coe_finset_sum (fun i _ => Box.volume_nonneg _)


/-- Helper: Bounded closed sets are measurable (Lemma 1.2.13(ii) for bounded case).
    For bounded closed E (compact by Heine-Borel), show that for any ε > 0,
    there exists open U ⊇ E with m*(U \ E) ≤ ε. -/
private lemma IsClosed.measurable_of_bounded {d:ℕ} {E: Set (EuclideanSpace' d)}
    (hE: IsClosed E) (hE_bounded : Bornology.IsBounded E) : LebesgueMeasurable E := by
  intro ε hε
  -- Empty case
  by_cases hE_empty : E = ∅
  · use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp [Lebesgue_outer_measure.of_empty]; exact le_of_lt hε
  -- Non-empty bounded closed E is compact
  have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  -- Get open U with m*(U) ≤ m*(E) + ε/2
  have hε_half_pos : (0 : EReal) < ε / 2 := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top =>
      show (0 : EReal) < ⊤ / 2
      -- ⊤ / 2 = ⊤ in EReal since 2 > 0 and 2 ≠ ⊤
      have : (⊤ : EReal) / 2 = ⊤ := by
        have h2_pos : (0 : EReal) < 2 := by norm_num
        have h2_ne_top : (2 : EReal) ≠ ⊤ := by
          intro h
          have : (2 : EReal) = (2 : ℝ) := rfl
          rw [this] at h
          exact EReal.coe_ne_top 2 h
        exact EReal.top_div_of_pos_ne_top h2_pos h2_ne_top
      rw [this]
      exact EReal.zero_lt_top
    | coe r =>
      have hr_pos : 0 < r := EReal.coe_pos.mp hε
      rw [show (2 : EReal) = (2 : ℝ) from rfl, ← EReal.coe_div r 2]
      exact EReal.coe_pos.mpr (half_pos hr_pos)
  obtain ⟨U, hU_open, hE_sub_U, hU_meas⟩ := Lebesgue_outer_measure.exists_open_superset_measure_le E (ε/2) hε_half_pos
  use U
  refine ⟨hU_open, hE_sub_U, ?_⟩
  -- Key: show m*(U \ E) ≤ ε
  -- U \ E is open
  have h_diff_open : IsOpen (U \ E) := hU_open.sdiff hE
  -- Handle d = 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 = Fin 0 → ℝ is a subsingleton
    -- Since E is nonempty and E ⊆ U, and U is nonempty (contains E), we have E = U
    -- Therefore U \ E = ∅, so m*(U \ E) = 0 ≤ ε
    subst hd
    have : Subsingleton (EuclideanSpace' 0) := by
      unfold EuclideanSpace'
      infer_instance
    have hU_nonempty : U.Nonempty := hE_nonempty.mono hE_sub_U
    have hEU_eq : E = U := by
      apply Set.Subset.antisymm hE_sub_U
      intro x hx
      obtain ⟨y, hy⟩ := hE_nonempty
      have hxy : x = y := Subsingleton.elim x y
      rw [hxy]
      exact hy
    rw [hEU_eq, Set.diff_self, Lebesgue_outer_measure.of_empty]
    exact le_of_lt hε
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- If U \ E is empty, trivial
  by_cases h_diff_empty : U \ E = ∅
  · rw [h_diff_empty, Lebesgue_outer_measure.of_empty]; exact le_of_lt hε
  -- Main argument: U \ E is nonempty open, decompose into cubes
  have h_diff_nonempty : (U \ E).Nonempty := Set.nonempty_iff_ne_empty.mpr h_diff_empty
  obtain ⟨Q, hQ_union, hQ_dyadic, hQ_pairwise⟩ := h_diff_open.eq_union_boxes hd_pos (U \ E) h_diff_nonempty
  rw [hQ_union]
  -- m*(⋃ Q_n) = ∑ |Q_n|
  have h_measure_eq : Lebesgue_outer_measure (⋃ n, (Q n).toSet) = ∑' n, (Q n).volume.toEReal := by
    have h1 := Lebesgue_outer_measure.union_of_almost_disjoint hQ_pairwise
    simp_rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _),
             IsElementary.measure_of_box] at h1
    exact h1
  rw [h_measure_eq]
  -- Use compactness: E is compact (closed + bounded)
  -- EuclideanSpace ℝ (Fin d) is finite-dimensional, hence ProperSpace
  -- By Heine-Borel: closed + bounded = compact in proper spaces
  have hE_compact : IsCompact E := Metric.isCompact_of_isClosed_isBounded hE hE_bounded
  calc ∑' n, (Q n).volume.toEReal
      = Lebesgue_outer_measure (⋃ n, (Q n).toSet) := h_measure_eq.symm
    _ = Lebesgue_outer_measure (U \ E) := by rw [← hQ_union]
    _ ≤ ε / 2 := by
        -- Key: E is compact, so m*(E) is finite (not ⊥ or ⊤)
        have hE_finite : Lebesgue_outer_measure E ≠ ⊤ :=
          Lebesgue_outer_measure.finite_of_compact hE_compact
        have hE_ne_bot : Lebesgue_outer_measure E ≠ ⊥ := by
          have h_nonneg : 0 ≤ Lebesgue_outer_measure E := Lebesgue_outer_measure.nonneg E
          intro h_eq
          rw [h_eq] at h_nonneg
          -- 0 ≤ ⊥ is false in EReal
          exact not_le.mpr EReal.bot_lt_zero h_nonneg

        -- For each finite N, show ∑_{i < N} vol(Q_i) ≤ ε/2
        have h_finite_sum_bound : ∀ (t : Finset ℕ),
            ∑ i ∈ t, ((Q i).volume : EReal) ≤ ε / 2 := by
          intro t
          -- Handle empty finset case
          by_cases ht_empty : t = ∅
          · rw [ht_empty]
            simp
            exact le_of_lt hε_half_pos
          -- Now t is nonempty
          -- Let F_t = ⋃_{i ∈ t} Q_i
          let F_t := ⋃ i ∈ t, (Q i).toSet
          -- F_t is compact (finite union of compact boxes)
          have hF_compact : IsCompact F_t := by
            -- Each box is compact (product of compact intervals)
            have hQ_compact : ∀ i ∈ t, IsCompact ((Q i).toSet) := by
              intro i _
              exact Box.isCompact (Q i) (Box.IsDyadic.all_sides_Icc (hQ_dyadic i))
            -- Finite union of compact sets is compact
            exact Finset.isCompact_biUnion t hQ_compact
          -- E ∩ F_t = ∅ (since F_t ⊆ U\E)
          have hE_F_disj : E ∩ F_t = ∅ := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, F_t]
            intro hxE
            simp only [Set.mem_iUnion, not_exists]
            intro i hi
            -- x ∈ E and x ∈ Q_i, but Q_i ⊆ U\E
            have hQ_sub : (Q i).toSet ⊆ U \ E := by
              have : (Q i).toSet ⊆ ⋃ n, (Q n).toSet := by
                intro y hy
                exact Set.mem_iUnion_of_mem i hy
              rw [← hQ_union] at this
              exact this
            intro hxi
            exact (hQ_sub hxi).2 hxE
          -- By compactness: set_dist E F_t > 0 (t is nonempty, so F_t is nonempty)
          have h_sep : set_dist E F_t > 0 :=
            dist_of_disj_compact_pos E F_t hE_compact hF_compact hE_F_disj
          -- By separation: m*(E ∪ F_t) = m*(E) + m*(F_t)
          have h_add : Lebesgue_outer_measure (E ∪ F_t) =
                       Lebesgue_outer_measure E + Lebesgue_outer_measure F_t :=
            Lebesgue_outer_measure.union_of_separated hd_pos h_sep
          -- E ∪ F_t ⊆ U
          have h_sub : E ∪ F_t ⊆ U := by
            intro x hx
            cases hx with
            | inl hxE => exact hE_sub_U hxE
            | inr hxF =>
              -- F_t ⊆ ⋃ n, Q_n = U\E ⊆ U
              have : F_t ⊆ ⋃ n, (Q n).toSet := by
                intro y hy
                simp [F_t] at hy
                obtain ⟨i, hi, hyi⟩ := hy
                exact Set.mem_iUnion_of_mem i hyi
              have hF_sub : (⋃ n, (Q n).toSet) ⊆ U := by
                rw [← hQ_union]
                exact Set.diff_subset
              exact hF_sub (this hxF)
          -- So m*(E ∪ F_t) ≤ m*(U) ≤ m*(E) + ε/2
          have h_bound : Lebesgue_outer_measure (E ∪ F_t) ≤ Lebesgue_outer_measure E + ε / 2 := by
            calc Lebesgue_outer_measure (E ∪ F_t)
                ≤ Lebesgue_outer_measure U := Lebesgue_outer_measure.mono h_sub
              _ ≤ Lebesgue_outer_measure E + ε / 2 := hU_meas
          -- Therefore m*(E) + m*(F_t) ≤ m*(E) + ε/2, so m*(F_t) ≤ ε/2
          rw [h_add] at h_bound
          -- Cancellation: m*(E) + m*(F_t) ≤ m*(E) + ε/2 implies m*(F_t) ≤ ε/2
          have h_F_bound : Lebesgue_outer_measure F_t ≤ ε / 2 := by
            -- Use EReal.sub_le_of_le_add': if a ≤ b + c then a - b ≤ c
            have h1 : Lebesgue_outer_measure E + Lebesgue_outer_measure F_t - Lebesgue_outer_measure E ≤ ε / 2 :=
              EReal.sub_le_of_le_add' h_bound
            -- Since m*(E) is finite (not ⊥ or ⊤), we have (m*(E) + m*(F_t)) - m*(E) = m*(F_t)
            -- Case analysis on m*(E) being a real number
            have h_cancel : Lebesgue_outer_measure E + Lebesgue_outer_measure F_t - Lebesgue_outer_measure E = Lebesgue_outer_measure F_t := by
              cases h : Lebesgue_outer_measure E with
              | bot => exact absurd h hE_ne_bot
              | top => exact absurd h hE_finite
              | coe r =>
                -- m*(E) = r (a real number), so the goal is already r + m*(F_t) - r = m*(F_t)
                exact EReal.add_sub_cancel_left
            rw [h_cancel] at h1
            exact h1
          -- Finally: m*(F_t) = ∑_{i ∈ t} vol(Q_i) by almost disjoint union
          calc ∑ i ∈ t, ((Q i).volume : EReal)
              = Lebesgue_outer_measure F_t := by
                symm
                exact Lebesgue_outer_measure.sum_of_almost_disjoint_finset hd_pos hQ_dyadic hQ_pairwise
            _ ≤ ε / 2 := h_F_bound

        -- Now: ∑' n, vol(Q_n) ≤ ε/2 by supremum of finite sums
        have hvol_nonneg : ∀ n, 0 ≤ (Q n).volume := fun n => Box.volume_nonneg _
        have h_range_bound : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((Q i).volume : EReal) ≤ ε / 2 :=
          fun N => h_finite_sum_bound (Finset.range N)
        have h_tsum_bound : ∑' n, ((Q n).volume : EReal) ≤ ε / 2 :=
          EReal.tsum_le_of_sum_range_le hvol_nonneg h_range_bound
        -- Convert back using h_measure_eq
        calc Lebesgue_outer_measure (U \ E)
            = Lebesgue_outer_measure (⋃ n, (Q n).toSet) := by rw [hQ_union]
          _ = ∑' n, ((Q n).volume : EReal) := h_measure_eq
          _ ≤ ε / 2 := h_tsum_bound
    _ ≤ ε := by
        cases ε with
        | bot => exact absurd hε (not_lt.mpr bot_le)
        | top => simp
        | coe r =>
          have hr_pos : 0 < r := EReal.coe_pos.mp hε
          rw [show (2 : EReal) = (2 : ℝ) from rfl, ← EReal.coe_div r 2]
          exact EReal.coe_le_coe_iff.mpr (half_le_self (le_of_lt hr_pos))

/-- Lemma 1.2.13(ii) (Every closed set is Lebesgue measurable). -/
theorem IsClosed.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsClosed E) : LebesgueMeasurable E := by
  -- Write E = ⋃_{n=0}^∞ (E ∩ closedBall 0 n)
  have h_union : E = ⋃ n : ℕ, E ∩ Metric.closedBall 0 n := (Metric.iUnion_inter_closedBall_nat E 0).symm
  rw [h_union]
  -- Each E ∩ closedBall 0 n is closed (intersection of closed sets) and bounded
  have h_closed : ∀ n : ℕ, IsClosed (E ∩ Metric.closedBall 0 n) :=
    fun n => hE.inter Metric.isClosed_closedBall
  have h_bounded : ∀ n : ℕ, Bornology.IsBounded (E ∩ Metric.closedBall 0 n) :=
    fun n => Metric.isBounded_closedBall.subset Set.inter_subset_right
  -- Apply IsClosed.measurable_of_bounded to each piece
  have h_meas : ∀ n : ℕ, LebesgueMeasurable (E ∩ Metric.closedBall 0 n) :=
    fun n => IsClosed.measurable_of_bounded (h_closed n) (h_bounded n)
  -- Inline countable union proof (Lemma 1.2.13(vi) is defined later in this file)
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with (E ∩ closedBall 0 n) ⊆ U_n and m*(U_n \ (E ∩ closedBall 0 n)) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  choose U hU_open hE_sub hU_diff using fun n => h_meas n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · exact isOpen_iUnion hU_open
  constructor
  · apply Set.iUnion_mono; intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E ∩ closedBall 0 n)) ≤ ε
    have h_diff_subset : (⋃ (n : ℕ), U n) \ (⋃ (n : ℕ), E ∩ Metric.closedBall 0 ↑n) ⊆ ⋃ (n : ℕ), (U n \ (E ∩ Metric.closedBall 0 ↑n)) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek; exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ (n : ℕ), U n) \ (⋃ (n : ℕ), E ∩ Metric.closedBall 0 ↑n))
        ≤ Lebesgue_outer_measure (⋃ (n : ℕ), (U n \ (E ∩ Metric.closedBall 0 ↑n))) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' (n : ℕ), Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' (n : ℕ), ((ε' / 2^(n+1) : ℝ) : EReal) := by
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n))
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

abbrev IsNull {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := Lebesgue_outer_measure E = 0

/-- Lemma 1.2.13(iii) (Every null set is Lebesgue measurable).-/
theorem IsNull.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsNull E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, since m*(E) = 0, get a box cover with total volume < ε,
  -- then inflate boxes to open sets. The union is open and contains E.
  intro ε hε
  -- Handle dimension 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 is a single point.
    -- Since m*(E) = 0 and m*(univ) = 1 for nonempty sets in d=0, E must be empty.
    -- Use U = E = ∅, which is open, E ⊆ U, and U \ E = ∅ has measure 0.
    subst hd
    -- In d=0: m*(E) = if E.Nonempty then 1 else 0
    -- hE : IsNull E is an abbrev for Lebesgue_outer_measure E = 0
    have hE' : Lebesgue_outer_measure E = 0 := hE
    rw [Lebesgue_outer_measure_of_dim_zero] at hE'
    simp only [ite_eq_right_iff, one_ne_zero] at hE'
    -- hE' : E.Nonempty → False, i.e., E = ∅
    have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE'
    use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp only [Set.empty_diff]
      rw [Lebesgue_outer_measure.of_empty]
      exact le_of_lt hε
  -- Now d > 0
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- m*(E) = 0 implies m*(E) ≠ ⊤
  have h_finite : Lebesgue_outer_measure E ≠ ⊤ := by rw [hE]; exact EReal.zero_ne_top
  -- Convert EReal ε to a real number
  -- Since ε > 0, get a real ε' with 0 < ε' and ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- Get an ε'/2-close box cover
  have hε2_pos : 0 < ε' / 2 := by linarith
  obtain ⟨S, hS_cover, hS_vol⟩ := Lebesgue_outer_measure.exists_cover_close hd_pos E (ε' / 2) hε2_pos h_finite
  -- hS_vol : ∑' n, (S n).volume.toEReal ≤ m*(E) + ε'/2 = 0 + ε'/2 = ε'/2
  rw [hE] at hS_vol
  simp only [zero_add] at hS_vol
  -- Inflate each box to get an open set containing it
  -- Use δₙ = ε' / 2^(n+2) so that ∑ δₙ = ε'/2
  let δ : ℕ → ℝ := fun n => ε' / 2 / 2 ^ (n + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => by simp only [δ]; positivity
  -- Get inflated boxes using Box.inflate
  have h_inflate := fun n => Box.inflate (S n) (δ n) (hδ_pos n)
  choose U' hU'_subset hU'_open hU'_vol using h_inflate
  -- Define U as union of interiors of inflated boxes
  let U := ⋃ n, interior (U' n).toSet
  use U
  constructor
  · -- U is open (union of open sets)
    exact isOpen_iUnion (fun n => isOpen_interior)
  constructor
  · -- E ⊆ U
    calc E ⊆ ⋃ n, (S n).toSet := hS_cover
         _ ⊆ ⋃ n, interior (U' n).toSet := Set.iUnion_mono (fun n => hU'_subset n)
  · -- m*(U \ E) ≤ ε
    -- Key bounds: m*(U \ E) ≤ m*(U) ≤ ∑ |U' n|ᵥ ≤ ∑ (|S n|ᵥ + δ n) ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have h1 : Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure U :=
      Lebesgue_outer_measure.mono Set.diff_subset
    have h2 : Lebesgue_outer_measure U ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := by
      have : U = ⋃ n, interior (U' n).toSet := rfl
      rw [this]
      exact Lebesgue_outer_measure.union_le _
    -- Each interior has measure ≤ box volume
    have h3 : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ (U' n).volume.toEReal := by
      intro n
      calc Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ Lebesgue_outer_measure (U' n).toSet := Lebesgue_outer_measure.mono interior_subset
        _ = (IsElementary.box (U' n)).measure.toEReal := by
            rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
        _ = (U' n).volume.toEReal := by rw [IsElementary.measure_of_box]
    -- Each inflated box volume ≤ original + δ
    have h4 : ∀ n, (U' n).volume.toEReal ≤ ((S n).volume + δ n).toEReal := by
      intro n
      exact EReal.coe_le_coe_iff.mpr (hU'_vol n)
    -- The sum splits: ∑ (|S n|ᵥ + δ n) = ∑ |S n|ᵥ + ∑ δ n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have hδ_sum : ∑' n, (δ n : ℝ) = ε' / 2 := by
      simp only [δ, div_div]
      have h := tsum_geometric_two' (ε' / 2)
      convert h using 1
      congr 1
      ext n
      ring_nf
    -- Combine the bounds to show m*(U \ E) ≤ ε' ≤ ε
    -- Strategy:
    -- m*(U\E) ≤ m*(U) ≤ ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol(S_n) + δ_n)
    --         ≤ ∑ vol(S_n) + ∑ δ_n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    -- The key steps use h1, h2, h3, h4, hS_vol, hδ_sum, hε'_le
    have h_sum_le : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ε' := by
      -- Each interior measure ≤ vol(U' n) ≤ vol(S n) + δ n
      -- Sum: ∑ vol(S n) ≤ ε'/2, ∑ δ n = ε'/2, so total ≤ ε'
      -- First show δ is summable (geometric series)
      have hδ_summable : Summable δ := by
        simp only [δ, div_div]
        exact (summable_geometric_two' (ε' / 2)).congr (fun n => by ring_nf)
      -- Show volumes are summable (from the bound hS_vol)
      have hvol_nonneg : ∀ n, 0 ≤ (S n).volume := fun n => Box.volume_nonneg _
      have hvol_sum : Summable (fun n => (S n).volume) := by
        -- Key: use that the partial sums in EReal are bounded
        have h_partial_bound : ∀ t : Finset ℕ, (∑ n ∈ t, (S n).volume : EReal) ≤ ε' / 2 := by
          intro t
          calc (∑ n ∈ t, (S n).volume : EReal)
              ≤ ∑' n, ((S n).volume : EReal) := EReal.finset_sum_le_tsum hvol_nonneg t
            _ ≤ ε' / 2 := hS_vol
        -- In ℝ: partial sums bounded implies summable for nonneg sequences
        have h_partial_real : ∀ t : Finset ℕ, ∑ n ∈ t, (S n).volume ≤ ε' / 2 := by
          intro t
          have h := h_partial_bound t
          have h_coe : (∑ n ∈ t, (S n).volume : EReal) = ↑(∑ n ∈ t, (S n).volume) :=
            (EReal.coe_finset_sum (fun n _ => hvol_nonneg n)).symm
          rw [h_coe] at h; exact EReal.coe_le_coe_iff.mp h
        exact summable_of_sum_le hvol_nonneg h_partial_real
      have hsum_combined : Summable (fun n => (S n).volume + δ n) := hvol_sum.add hδ_summable
      -- Use transitivity through ε' bound:
      -- ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol S_n + δ_n) = ∑ vol S_n + ∑ δ_n ≤ ε'/2 + ε'/2 = ε'
      have h_interior_bound : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ((S n).volume + δ n : EReal) := by
        intro n
        calc Lebesgue_outer_measure (interior (U' n).toSet)
            ≤ (U' n).volume.toEReal := h3 n
          _ ≤ ((S n).volume + δ n).toEReal := h4 n
          _ = ((S n).volume + δ n : EReal) := rfl
      -- Sum bound: use EReal.tsum_le_coe_tsum_of_forall_le
      have hg_nonneg : ∀ n, 0 ≤ (S n).volume + δ n := fun n => by linarith [hvol_nonneg n, hδ_pos n]
      have h_tsum_bound : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ∑' n, ((S n).volume + δ n : EReal) :=
        EReal.tsum_le_coe_tsum_of_forall_le (fun n => Lebesgue_outer_measure.nonneg _)
          hg_nonneg hsum_combined h_interior_bound
      -- Key equality: tsums in EReal with coercion can be rewritten
      have h_tsum_eq : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) := by
        have h1 : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ∑' n, ↑((S n).volume + δ n) := by
          apply tsum_congr
          intro n; exact (EReal.coe_add _ _).symm
        have h2 : ∑' n, (↑((S n).volume + δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) :=
          (EReal.coe_tsum_of_nonneg hg_nonneg hsum_combined).symm
        rw [h1, h2]
      calc ∑' n, Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ ∑' n, (↑(S n).volume + ↑(δ n) : EReal) := h_tsum_bound
        _ = ↑(∑' n, ((S n).volume + δ n)) := h_tsum_eq
        _ = ↑(∑' n, (S n).volume + ∑' n, δ n) := by rw [hvol_sum.tsum_add hδ_summable]
        _ = ↑(∑' n, (S n).volume) + ↑(∑' n, δ n) := by rw [EReal.coe_add]
        _ ≤ ↑(ε' / 2) + ↑(ε' / 2) := by
            apply add_le_add
            · have := EReal.coe_tsum_of_nonneg hvol_nonneg hvol_sum
              rw [this]; exact hS_vol
            · rw [hδ_sum]
        _ = ε' := by rw [← EReal.coe_add]; norm_cast; ring
    calc Lebesgue_outer_measure (U \ E)
        ≤ Lebesgue_outer_measure U := h1
      _ ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := h2
      _ ≤ ε' := h_sum_le
      _ ≤ ε := hε'_le

/-- A subset of a null set is null. -/
lemma IsNull.subset {d:ℕ} {E F : Set (EuclideanSpace' d)} (hE : IsNull E) (hFE : F ⊆ E) : IsNull F := by
  have := Lebesgue_outer_measure.mono hFE
  rw [hE] at this
  exact le_antisymm this (Lebesgue_outer_measure.nonneg F)

/-- Lemma 1.2.13(iv) (Empty set is measurable).-/
theorem LebesgueMeasurable.empty {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) :=
-- use (i) directly
  IsOpen.measurable isOpen_empty

theorem LebesgueMeasurable.empty' {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) := by
-- use definition of Lebesgue measurability
  intro ε hε
  use ∅
  constructor
  · exact isOpen_empty
  constructor
  · exact Set.empty_subset ∅
  · have h_empty : ∅ \ ∅ = (∅ : Set (EuclideanSpace' d)) := Set.diff_self
    rw [h_empty]
    rw [Lebesgue_outer_measure.of_empty d]
    exact le_of_lt hε

/-- Lemma 1.2.13(vi) (Countable union of measurable sets is measurable).-/
theorem LebesgueMeasurable.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋃ n, E n) := by
  -- Use the ε/2^n trick: let ε > 0 be arbitrary
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with E_n ⊆ U_n and m*(U_n \ E_n) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  -- Apply measurability of each E_n with ε'/2^(n+1)
  choose U hU_open hE_sub hU_diff using fun n => hE n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · -- ⋃ n, U n is open (union of open sets)
    exact isOpen_iUnion hU_open
  constructor
  · -- ⋃ n, E n ⊆ ⋃ n, U n
    apply Set.iUnion_mono
    intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E n)) ≤ ε
    -- Key: (⋃ U_n) \ (⋃ E_n) ⊆ ⋃ (U_n \ E_n)
    have h_diff_subset : (⋃ n, U n) \ (⋃ n, E n) ⊆ ⋃ n, (U n \ E n) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek
        exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ n, U n) \ (⋃ n, E n))
        ≤ Lebesgue_outer_measure (⋃ n, (U n \ E n)) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (U n \ E n) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' n, ((ε' / 2^(n+1) : ℝ) : EReal) := by
          -- Use EReal.tsum_le_coe_tsum_of_forall_le
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ E n) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ E n) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ E n)
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          -- ∑ n, ε'/2^(n+1) = ε' (geometric series)
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

/-- Lemma 1.2.13(v) (Complement of a measurable set is measurable). -/
theorem LebesgueMeasurable.complement {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) : LebesgueMeasurable (Eᶜ) := by
  -- Strategy: For each n, find open Uₙ ⊇ E with m*(Uₙ \ E) ≤ 1/(n+1).
  -- Let Fₙ = Uₙᶜ (closed). Then Eᶜ ⊇ Fₙ and m*(Eᶜ \ Fₙ) = m*(Uₙ \ E) ≤ 1/(n+1).
  -- Let F = ⋃ Fₙ. Then m*(Eᶜ \ F) = 0 and Eᶜ = F ∪ (Eᶜ \ F).
  -- F is measurable (countable union of closed sets), Eᶜ \ F is null (hence measurable).

  -- Step 1: For each n, get open Uₙ with E ⊆ Uₙ and m*(Uₙ \ E) ≤ 1/(n+1)
  have h_eps_pos : ∀ n : ℕ, (0 : EReal) < 1 / (n + 1 : ℕ) := fun n => by
    have h1 : (0 : EReal) < 1 := EReal.coe_pos.mpr (by norm_num : (0 : ℝ) < 1)
    have h2 : (0 : EReal) < (n + 1 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      exact EReal.coe_pos.mpr (by linarith : (0 : ℝ) < n + 1)
    exact EReal.div_pos h1 h2 (EReal.coe_ne_top _)
  choose U hU_open hE_sub_U hU_diff using fun n => hE (1 / (n + 1 : ℕ)) (h_eps_pos n)

  -- Step 2: Define Fₙ = Uₙᶜ (closed sets)
  let F_n : ℕ → Set (EuclideanSpace' d) := fun n => (U n)ᶜ
  have hF_closed : ∀ n, IsClosed (F_n n) := fun n => (hU_open n).isClosed_compl

  -- Key set-theoretic fact: Eᶜ \ Fₙ = Uₙ \ E
  have h_diff_eq : ∀ n, Eᶜ \ F_n n = U n \ E := fun n => by
    simp only [F_n, Set.diff_compl]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
    tauto

  -- Step 3: Define F = ⋃ Fₙ (F-sigma set)
  let F := ⋃ n, F_n n

  -- Step 4: Show m*(Eᶜ \ F) = 0
  have h_diff_F : ∀ n, Eᶜ \ F ⊆ U n \ E := fun n => by
    have h1 : Eᶜ \ F ⊆ Eᶜ \ F_n n := Set.diff_subset_diff_right (Set.subset_iUnion F_n n)
    rw [h_diff_eq n] at h1
    exact h1

  have h_measure_bound : ∀ n, Lebesgue_outer_measure (Eᶜ \ F) ≤ 1 / (n + 1 : ℕ) := fun n =>
    calc Lebesgue_outer_measure (Eᶜ \ F)
        ≤ Lebesgue_outer_measure (U n \ E) := Lebesgue_outer_measure.mono (h_diff_F n)
      _ ≤ 1 / (n + 1 : ℕ) := hU_diff n

  have h_null : IsNull (Eᶜ \ F) := by
    apply le_antisymm
    · -- Show m*(Eᶜ \ F) ≤ 0 by showing it's ≤ 1/(n+1) for all n
      by_contra h_ne
      push_neg at h_ne
      have h_pos : 0 < Lebesgue_outer_measure (Eᶜ \ F) := h_ne
      -- Get a real ε with 0 < ε ≤ m*(Eᶜ \ F)
      obtain ⟨ε, hε_pos, hε_le⟩ : ∃ ε : ℝ, 0 < ε ∧ (ε : EReal) ≤ Lebesgue_outer_measure (Eᶜ \ F) := by
        cases hm : Lebesgue_outer_measure (Eᶜ \ F) with
        | bot => rw [hm] at h_pos; exact absurd h_pos (not_lt.mpr bot_le)
        | top => exact ⟨1, one_pos, le_top⟩
        | coe r =>
          rw [hm] at h_pos
          have hr : 0 < r := EReal.coe_pos.mp h_pos
          exact ⟨r, hr, le_refl _⟩
      -- Find N with 1/(N+1) < ε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      have hNp1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hN1 : 1 / ((N : ℝ) + 1) < ε := by
        have h1 : 1 / ε < (N : ℝ) + 1 := lt_of_lt_of_le hN (by norm_cast; exact Nat.le_succ N)
        rw [one_div_lt hNp1_pos hε_pos]; exact h1
      -- h_measure_bound N says m*(Eᶜ \ F) ≤ 1/(N+1)
      have h_bound : Lebesgue_outer_measure (Eᶜ \ F) ≤ 1 / (N + 1 : ℕ) := h_measure_bound N
      have h_eq : (1 : EReal) / (N + 1 : ℕ) = ↑(1 / ((N : ℝ) + 1)) := by
        rw [EReal.coe_div, EReal.coe_one]; norm_cast
      rw [h_eq] at h_bound
      -- ε ≤ m*(Eᶜ \ F) ≤ 1/(N+1) < ε, contradiction
      have h_final : (ε : EReal) < (ε : EReal) := calc
        (ε : EReal) ≤ Lebesgue_outer_measure (Eᶜ \ F) := hε_le
        _ ≤ ↑(1 / ((N : ℝ) + 1)) := h_bound
        _ < ε := EReal.coe_lt_coe_iff.mpr hN1
      exact lt_irrefl (ε : EReal) h_final
    · exact Lebesgue_outer_measure.nonneg _

  -- Step 5: Show Eᶜ = F ∪ (Eᶜ \ F)
  have h_decomp : Eᶜ = F ∪ (Eᶜ \ F) := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · intro hx
      by_cases hxF : x ∈ F
      · left; exact hxF
      · right; exact ⟨hx, hxF⟩
    · intro h
      cases h with
      | inl hxF =>
        simp only [F, Set.mem_iUnion] at hxF
        obtain ⟨n, hxFn⟩ := hxF
        simp only [F_n, Set.mem_compl_iff] at hxFn
        have hxE : x ∉ E := fun h => hxFn (hE_sub_U n h)
        exact hxE
      | inr hxEcF => exact hxEcF.1

  -- Step 6: Apply measurability results
  rw [h_decomp]
  have hF_meas : LebesgueMeasurable F := by
    have : F = ⋃ n, F_n n := rfl
    rw [this]
    exact LebesgueMeasurable.countable_union (fun n => (hF_closed n).measurable)
  have hN_meas : LebesgueMeasurable (Eᶜ \ F) := h_null.measurable
  -- Union of two measurable sets
  let S : ℕ → Set (EuclideanSpace' d) := fun n => if n = 0 then F else if n = 1 then Eᶜ \ F else ∅
  have hS_meas : ∀ n, LebesgueMeasurable (S n) := fun n => by
    simp only [S]
    split_ifs with h0 h1
    · exact hF_meas
    · exact hN_meas
    · exact LebesgueMeasurable.empty
  have h_eq : F ∪ (Eᶜ \ F) = ⋃ n, S n := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, S]
    constructor
    · intro h
      cases h with
      | inl hF => exact ⟨0, by simp [hF]⟩
      | inr hN => exact ⟨1, by simp [hN]⟩
    · intro ⟨n, hn⟩
      split_ifs at hn with h0 h1
      · left; exact hn
      · right; exact hn
      · exact absurd hn (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.countable_union hS_meas

theorem LebesgueMeasurable.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋃ i, E i) := by
  -- Extend E to ℕ-indexed family by padding with empty sets
  let E' : ℕ → Set (EuclideanSpace' d) := fun k => if h : k < n then E ⟨k, h⟩ else ∅
  have hE'_meas : ∀ k, LebesgueMeasurable (E' k) := fun k => by
    simp only [E']
    split_ifs with hk
    · exact hE ⟨k, hk⟩
    · exact LebesgueMeasurable.empty
  -- Show ⋃ i : Fin n, E i = ⋃ k : ℕ, E' k
  have h_eq : (⋃ i : Fin n, E i) = ⋃ k : ℕ, E' k := by
    ext x
    simp only [Set.mem_iUnion, E']
    constructor
    · intro ⟨i, hx⟩
      use i.val
      simp only [i.isLt, ↓reduceDIte, hx]
    · intro ⟨k, hx⟩
      split_ifs at hx with hk
      · exact ⟨⟨k, hk⟩, hx⟩
      · exact absurd hx (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.countable_union hE'_meas

theorem LebesgueMeasurable.union {d :ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∪ F) := by
  -- Express E ∪ F as union over Fin 2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have hS : ∀ i, LebesgueMeasurable (S i) := fun i => by fin_cases i <;> simp [S, hE, hF]
  have h_eq : E ∪ F = ⋃ i : Fin 2, S i := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, S]
    constructor
    · rintro (hx | hx)
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hx]⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
  rw [h_eq]
  exact LebesgueMeasurable.finite_union hS

/-- Lemma 1.2.13(vii) (Countable intersection of measurable sets is measurable). -/
theorem LebesgueMeasurable.countable_inter {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋂ n, E n) := by
  -- By de Morgan: ⋂ Eₙ = (⋃ Eₙᶜ)ᶜ
  have h_eq : (⋂ n, E n) = (⋃ n, (E n)ᶜ)ᶜ := by
    rw [Set.compl_iUnion]
    simp only [compl_compl]
  rw [h_eq]
  -- Each Eₙᶜ is measurable by (v)
  have hE_compl : ∀ n, LebesgueMeasurable ((E n)ᶜ) := fun n => (hE n).complement
  -- ⋃ Eₙᶜ is measurable by (vi)
  have h_union : LebesgueMeasurable (⋃ n, (E n)ᶜ) := LebesgueMeasurable.countable_union hE_compl
  -- (⋃ Eₙᶜ)ᶜ is measurable by (v) again
  exact h_union.complement

theorem LebesgueMeasurable.finite_inter {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋂ i, E i) := by
  -- Extend Fin n indexed family to ℕ indexed family with univ for k ≥ n
  let E' : ℕ → Set (EuclideanSpace' d) := fun k => if h : k < n then E ⟨k, h⟩ else Set.univ
  have hE'_meas : ∀ k, LebesgueMeasurable (E' k) := fun k => by
    simp only [E']
    split_ifs with hk
    · exact hE ⟨k, hk⟩
    · -- univ = ∅ᶜ, so measurable by complement of empty
      rw [← Set.compl_empty]
      exact LebesgueMeasurable.empty.complement
  have h_eq : (⋂ i : Fin n, E i) = ⋂ k : ℕ, E' k := by
    ext x
    simp only [Set.mem_iInter, E']
    constructor
    · intro hx k
      split_ifs with hk
      · exact hx ⟨k, hk⟩
      · exact Set.mem_univ x
    · intro hx ⟨i, hi⟩
      have := hx i
      simp only [hi, dite_true] at this
      exact this
  rw [h_eq]
  exact LebesgueMeasurable.countable_inter hE'_meas

theorem LebesgueMeasurable.inter {d :ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∩ F) := by
  -- Express E ∩ F as intersection over Fin 2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have hS : ∀ i, LebesgueMeasurable (S i) := fun i => by fin_cases i <;> simp [S, hE, hF]
  have h_eq : E ∩ F = ⋂ i : Fin 2, S i := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, S]
    constructor
    · intro ⟨hxE, hxF⟩ i
      fin_cases i <;> simp_all
    · intro hx
      exact ⟨hx 0, hx 1⟩
  rw [h_eq]
  exact LebesgueMeasurable.finite_inter hS

/-- Finite intersection indexed by a Finset is Lebesgue measurable. -/
lemma LebesgueMeasurable.finset_inter {d : ℕ} {α : Type*} [DecidableEq α]
    {E : α → Set (EuclideanSpace' d)} {S : Finset α}
    (hE : ∀ i ∈ S, LebesgueMeasurable (E i)) :
    LebesgueMeasurable (⋂ i ∈ S, E i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
    rw [← Set.compl_empty]
    exact LebesgueMeasurable.empty.complement
  | insert a S' ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hE
    have hE_a := hE.1
    have hE_rest := fun i hi => hE.2 i hi
    rw [show (⋂ i ∈ insert a S', E i) = E a ∩ (⋂ i ∈ S', E i) by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨h a (Finset.mem_insert_self a S'), fun i hi => h i (Finset.mem_insert_of_mem hi)⟩
      · intro ⟨ha', h⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact ha'
        · exact h i hi']
    exact LebesgueMeasurable.inter hE_a (ih hE_rest)

/-- Finite union indexed by a Finset is Lebesgue measurable. -/
lemma LebesgueMeasurable.finset_union {d : ℕ} {α : Type*} [DecidableEq α]
    {E : α → Set (EuclideanSpace' d)} {S : Finset α}
    (hE : ∀ i ∈ S, LebesgueMeasurable (E i)) :
    LebesgueMeasurable (⋃ i ∈ S, E i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact LebesgueMeasurable.empty
  | insert a S' ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hE
    have hE_a := hE.1
    have hE_rest := fun i hi => hE.2 i hi
    rw [show (⋃ i ∈ insert a S', E i) = E a ∪ (⋃ i ∈ S', E i) by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · intro ⟨i, hi, hx⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · left; exact hx
        · right; exact ⟨i, hi', hx⟩
      · intro h
        cases h with
        | inl h => exact ⟨a, Finset.mem_insert_self a S', h⟩
        | inr h => obtain ⟨i, hi, hx⟩ := h; exact ⟨i, Finset.mem_insert_of_mem hi, hx⟩]
    exact LebesgueMeasurable.union hE_a (ih hE_rest)

/-- If A = B outside a null set N (i.e., A ∩ Nᶜ = B ∩ Nᶜ), then A is measurable if B is. -/
lemma LebesgueMeasurable.of_ae_eq {d : ℕ} {A B N : Set (EuclideanSpace' d)}
    (hB : LebesgueMeasurable B) (hN : IsNull N) (h_eq : A ∩ Nᶜ = B ∩ Nᶜ) :
    LebesgueMeasurable A := by
  -- A = (B ∩ Nᶜ) ∪ (A ∩ N)
  have h_decomp : A = (B ∩ Nᶜ) ∪ (A ∩ N) := by
    ext x
    constructor
    · intro hx
      by_cases hxN : x ∈ N
      · right; exact ⟨hx, hxN⟩
      · left; rw [← h_eq]; exact ⟨hx, hxN⟩
    · intro hx
      cases hx with
      | inl h => rw [← h_eq] at h; exact h.1
      | inr h => exact h.1
  rw [h_decomp]
  apply LebesgueMeasurable.union
  · exact LebesgueMeasurable.inter hB (IsNull.measurable hN).complement
  · exact IsNull.measurable (IsNull.subset hN Set.inter_subset_right)

/-- Closed balls are Lebesgue measurable. -/
lemma LebesgueMeasurable.closedBall {d : ℕ} (c : EuclideanSpace' d) (r : ℝ) :
    LebesgueMeasurable (Metric.closedBall c r) :=
  Metric.isClosed_closedBall.measurable

/-- Exercise 1.2.7 (Criteria for measurability)-/
theorem LebesgueMeasurable.TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε)
    ].TFAE
  := by sorry

  /-- Exercise 1.2.8 -/
theorem Jordan_measurable.lebesgue {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : LebesgueMeasurable E := by
  sorry

open BoundedInterval

abbrev CantorInterval (n:ℕ) : Set ℝ := ⋃ a : Fin n → ({0, 2}:Set ℕ), (Icc (∑ i, (a i)/(3:ℝ)^(i.val+1)) (∑ i, a i/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^n)).toSet

abbrev CantorSet : Set ℝ := ⋂ n : ℕ, CantorInterval n

/-- Exercise 1.2.9 (Middle thirds Cantor set ) -/
theorem CantorSet.compact : IsCompact CantorSet := by
  sorry

theorem CantorSet.uncountable : Uncountable CantorSet := by
  sorry

theorem CantorSet.null : IsNull (Real.equiv_EuclideanSpace' '' CantorSet) := by sorry

/-- Exercise 1.2.10 ([0,1) is not the countable union of pairwise disjoint closed intervals)-/
example : ¬ ∃ (I: ℕ → BoundedInterval), (∀ n, IsClosed (I n).toSet) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (I n).toSet) ) ∧ (⋃ n, (I n).toSet = Set.Ico 0 1) := by
  sorry

/-- Exercise 1.2.10, challenge version -/
example : ¬ ∃ (E: ℕ → Set ℝ), (∀ n, IsClosed (E n)) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (E n)) ) ∧ (⋃ n, (E n) = Set.Ico 0 1) := by
  sorry

theorem Jordan_measurable.Lebesgue_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : Lebesgue_measure E = hE.measure := by
  sorry

/-- Lemma 1.2.15(a) (Empty set has zero Lebesgue measure). The proof is missing. -/
@[simp]
theorem Lebesgue_measure.empty {d:ℕ} : Lebesgue_measure (∅: Set (EuclideanSpace' d)) = 0 :=
  -- Direct application of Lebesgue_outer_measure.of_empty since Lebesgue_measure = Lebesgue_outer_measure
  Lebesgue_outer_measure.of_empty d

/-- Helper: Countable additivity for compact sets.
    When all E_n are compact and pairwise disjoint, m(⋃ E_n) = ∑' m(E_n).
    Key: compact disjoint sets have positive separation, so we can use Lemma 1.2.5. -/
private lemma Lebesgue_measure.countable_union_compact {d:ℕ} (hd : 0 < d)
    {E: ℕ → Set (EuclideanSpace' d)}
    (hcompact: ∀ n, IsCompact (E n))
    (hdisj: Set.univ.PairwiseDisjoint E) :
    Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: For each N, m(⋃_{n<N} E_n) = ∑_{n<N} m(E_n) by finite additivity + separation
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- For each N, by induction, m(⋃_{n≤N} E_n) = ∑_{n≤N} m(E_n)
    have h_finite_sum : ∀ N : ℕ, Lebesgue_measure (⋃ n ∈ Finset.range N, E n) =
        ∑ n ∈ Finset.range N, Lebesgue_measure (E n) := by
      intro N
      induction N with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        -- ⋃ n ∈ ∅, E n = ∅
        have : (⋃ n ∈ (∅ : Finset ℕ), E n) = ∅ := by simp
        rw [this, Lebesgue_measure.empty]
      | succ N ih =>
        -- ⋃_{n<N+1} E_n = (⋃_{n<N} E_n) ∪ E_N
        have h_union_eq : (⋃ n ∈ Finset.range (N + 1), E n) =
            (⋃ n ∈ Finset.range N, E n) ∪ E N := by
          ext x
          simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union]
          constructor
          · intro ⟨n, ⟨hn, hx⟩⟩
            by_cases hnN : n < N
            · left; exact ⟨n, ⟨hnN, hx⟩⟩
            · right
              have : n = N := Nat.eq_of_lt_succ_of_not_lt hn hnN
              rw [← this]; exact hx
          · intro h
            cases h with
            | inl hl =>
              obtain ⟨n, ⟨hn, hx⟩⟩ := hl
              exact ⟨n, ⟨Nat.lt_succ_of_lt hn, hx⟩⟩
            | inr hr => exact ⟨N, ⟨Nat.lt_succ_self N, hr⟩⟩
        rw [h_union_eq]
        -- The two parts are disjoint
        have h_disj_parts : (⋃ n ∈ Finset.range N, E n) ∩ E N = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_range, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro ⟨n, ⟨hn, hxn⟩⟩ hxN
          have hne : n ≠ N := Nat.ne_of_lt hn
          have hdisj_pair : Disjoint (E n) (E N) := hdisj (Set.mem_univ n) (Set.mem_univ N) hne
          exact Set.disjoint_iff.mp hdisj_pair ⟨hxn, hxN⟩
        -- The finite union is compact
        have hcompact_finite : IsCompact (⋃ n ∈ Finset.range N, E n) :=
          Finset.isCompact_biUnion _ (fun n _ => hcompact n)
        -- Use separation of compact disjoint sets
        by_cases h_empty_N : E N = ∅
        · -- If E_N is empty, the union doesn't change
          simp only [h_empty_N, Set.union_empty]
          rw [Finset.sum_range_succ, ih]
          simp [h_empty_N, Lebesgue_measure.empty]
        · by_cases h_empty_union : (⋃ n ∈ Finset.range N, E n) = ∅
          · simp only [h_empty_union, Set.empty_union, Finset.sum_range_succ]
            have h_sum_zero : ∑ n ∈ Finset.range N, Lebesgue_measure (E n) = 0 := by
              have h_all_empty : ∀ n ∈ Finset.range N, E n = ∅ := by
                intro n hn
                by_contra hne
                have hnonempty : (E n).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
                have hsub : (E n) ⊆ ⋃ n ∈ Finset.range N, E n := Set.subset_biUnion_of_mem hn
                rw [h_empty_union] at hsub
                obtain ⟨x, hx⟩ := hnonempty
                exact Set.notMem_empty x (hsub hx)
              apply Finset.sum_eq_zero
              intro n hn
              rw [h_all_empty n hn, Lebesgue_measure.empty]
            rw [h_sum_zero, zero_add]
          · -- Both parts are nonempty compact and disjoint
            have h_nonempty_N : (E N).Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty_N
            have h_nonempty_union : (⋃ n ∈ Finset.range N, E n).Nonempty :=
              Set.nonempty_iff_ne_empty.mpr h_empty_union
            have h_sep : set_dist (⋃ n ∈ Finset.range N, E n) (E N) > 0 :=
              dist_of_disj_compact_pos _ _ hcompact_finite (hcompact N) h_disj_parts
            have h_add := Lebesgue_outer_measure.union_of_separated hd h_sep
            -- h_add : Lebesgue_outer_measure (...) = Lebesgue_outer_measure (...) + Lebesgue_outer_measure (E N)
            -- Since Lebesgue_measure = Lebesgue_outer_measure, we can use this directly
            calc Lebesgue_measure ((⋃ n ∈ Finset.range N, E n) ∪ E N)
                = Lebesgue_outer_measure ((⋃ n ∈ Finset.range N, E n) ∪ E N) := rfl
              _ = Lebesgue_outer_measure (⋃ n ∈ Finset.range N, E n) + Lebesgue_outer_measure (E N) := h_add
              _ = Lebesgue_measure (⋃ n ∈ Finset.range N, E n) + Lebesgue_measure (E N) := rfl
              _ = ∑ n ∈ Finset.range N, Lebesgue_measure (E n) + Lebesgue_measure (E N) := by rw [ih]
              _ = ∑ n ∈ Finset.range (N + 1), Lebesgue_measure (E n) := by rw [Finset.sum_range_succ]
    -- Now: ∑' m(E_n) = sup_N ∑_{n < N} m(E_n) ≤ sup_N m(⋃_{n < N} E_n) ≤ m(⋃ E_n)
    have h_mono : ∀ N : ℕ, (⋃ n ∈ Finset.range N, E n) ⊆ (⋃ n, E n) := by
      intro N x hx
      simp only [Set.mem_iUnion, Finset.mem_range] at hx ⊢
      obtain ⟨n, ⟨_, hxn⟩⟩ := hx
      exact ⟨n, hxn⟩
    have h_sum_le : ∀ N : ℕ, ∑ n ∈ Finset.range N, Lebesgue_measure (E n) ≤
        Lebesgue_measure (⋃ n, E n) := by
      intro N
      rw [← h_finite_sum N]
      exact Lebesgue_outer_measure.mono (h_mono N)
    -- All measures are nonnegative (by definition of outer measure)
    have h_nn : ∀ n, 0 ≤ Lebesgue_measure (E n) := fun _ => Lebesgue_outer_measure.nonneg _
    exact EReal.tsum_le_of_sum_range_le_of_nonneg h_nn h_sum_le
  exact le_antisymm h_le h_ge

/-- Helper: Countable additivity for bounded sets.
    Following the textbook approach: Use ε/2ⁿ trick with inner regularity (Exercise 1.2.7).
    For bounded measurable E_n, find compact K_n ⊆ E_n with m(E_n) ≤ m(K_n) + ε/2^{n+1}.
    The K_n are pairwise disjoint (since K_n ⊆ E_n), so m(⋃ K_n) = ∑' m(K_n) by compact case,
    and m(⋃ E_n) ≥ m(⋃ K_n) = ∑' m(K_n) ≥ ∑' m(E_n) - ε. Let ε → 0. -/
private lemma Lebesgue_measure.countable_union_bounded {d:ℕ} (hd : 0 < d)
    {E: ℕ → Set (EuclideanSpace' d)}
    (hmes: ∀ n, LebesgueMeasurable (E n))
    (hbdd: ∀ n, Bornology.IsBounded (E n))
    (hdisj: Set.univ.PairwiseDisjoint E) :
    Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity (always holds)
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: Use ε/2ⁿ trick with compact approximation
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- Each bounded set has finite measure
    have h_finite : ∀ n, Lebesgue_measure (E n) ≠ ⊤ := by
      intro n
      have h_closure_compact : IsCompact (closure (E n)) :=
        Metric.isCompact_of_isClosed_isBounded isClosed_closure (hbdd n).closure
      have h_closure_finite : Lebesgue_measure (closure (E n)) ≠ ⊤ :=
        Lebesgue_outer_measure.finite_of_compact h_closure_compact
      have h_mono_closure : Lebesgue_measure (E n) ≤ Lebesgue_measure (closure (E n)) :=
        Lebesgue_outer_measure.mono subset_closure
      intro h_eq_top
      rw [h_eq_top] at h_mono_closure
      exact h_closure_finite (eq_top_iff.mpr h_mono_closure)
    -- Use ε-characterization: prove ∑' m(E_n) ≤ m(⋃ E_n) + ε for all ε > 0
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    -- Extract TFAE condition (4): inner approximation by closed sets
    have h_TFAE := fun n => LebesgueMeasurable.TFAE (E n)
    -- Condition (1) → Condition (4): For measurable E, closed F ⊆ E with m(E \ F) ≤ δ
    have h_inner : ∀ n, ∀ δ > (0 : EReal), ∃ F : Set (EuclideanSpace' d),
        IsClosed F ∧ F ⊆ E n ∧ Lebesgue_outer_measure (E n \ F) ≤ δ := by
      intro n δ hδ
      have h_tfae := h_TFAE n
      -- TFAE gives us: (1) ↔ (4)
      -- Condition (1) is hmes n : LebesgueMeasurable (E n)
      -- Condition (4) is ∀ ε > 0, ∃ F closed, F ⊆ E, m(E \ F) ≤ ε
      have h_14 : LebesgueMeasurable (E n) →
          (∀ ε > 0, ∃ F : Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E n ∧
            Lebesgue_outer_measure (E n \ F) ≤ ε) := by
        have := List.TFAE.out h_tfae 0 3
        exact this.mp
      exact h_14 (hmes n) δ hδ
    -- Choose ε_n = ε / 2^{n+1} for each n
    -- For each n, get compact K_n ⊆ E_n with m(E_n) ≤ m(K_n) + ε/2^{n+1}
    have h_eps_pos : ∀ n, (0 : EReal) < ε / 2^(n+1) := by
      intro n
      have h_pow_pos : (0 : ℝ) < 2^(n+1) := by positivity
      have h_eps_over_pow : (0 : ℝ) < ε / 2^(n+1) := by positivity
      -- ε/2^(n+1) > 0 by straightforward calculation
      calc (0 : EReal) < (ε / 2^(n+1) : ℝ) := EReal.coe_pos.mpr h_eps_over_pow
        _ = (ε : EReal) / (2^(n+1) : ℝ) := by rw [EReal.coe_div]
        _ = (ε : EReal) / (2 : EReal)^(n+1) := by simp only [EReal.coe_pow]; rfl
    choose F hF using fun n => h_inner n (ε / 2^(n+1)) (h_eps_pos n)
    -- F_n is closed (from h_inner), bounded (since F_n ⊆ E_n and E_n bounded), hence compact
    have hF_compact : ∀ n, IsCompact (F n) := by
      intro n
      have hF_closed : IsClosed (F n) := (hF n).1
      have hF_bdd : Bornology.IsBounded (F n) :=
        Bornology.IsBounded.subset (hbdd n) (hF n).2.1
      exact Metric.isCompact_of_isClosed_isBounded hF_closed hF_bdd
    -- F_n are pairwise disjoint (since F_n ⊆ E_n and E_n are pairwise disjoint)
    have hF_disj : Set.univ.PairwiseDisjoint F := by
      intro i _ j _ hij
      have hE_disj : Disjoint (E i) (E j) := hdisj (Set.mem_univ i) (Set.mem_univ j) hij
      exact Set.disjoint_of_subset_left (hF i).2.1 (Set.disjoint_of_subset_right (hF j).2.1 hE_disj)
    -- By the compact case: m(⋃ F_n) = ∑' m(F_n)
    have h_compact_case : Lebesgue_measure (⋃ n, F n) = ∑' n, Lebesgue_measure (F n) :=
      Lebesgue_measure.countable_union_compact hd hF_compact hF_disj
    -- Key inequality: m(E_n) ≤ m(F_n) + ε/2^{n+1}
    have h_approx : ∀ n, Lebesgue_measure (E n) ≤ Lebesgue_measure (F n) + ε / 2^(n+1) := by
      intro n
      -- E_n = F_n ∪ (E_n \ F_n), and F_n ⊆ E_n
      -- By monotonicity and subadditivity: m(E_n) ≤ m(F_n) + m(E_n \ F_n) ≤ m(F_n) + ε/2^{n+1}
      have h_partition : E n = F n ∪ (E n \ F n) := (Set.union_diff_cancel (hF n).2.1).symm
      -- Binary subadditivity: m(A ∪ B) ≤ m(A) + m(B)
      have h_binary_subadd : Lebesgue_measure (F n ∪ (E n \ F n)) ≤
          Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := by
        -- Use finite_union_le with Fin 2
        let S : Fin 2 → Set (EuclideanSpace' d) := ![F n, E n \ F n]
        have h_eq : F n ∪ (E n \ F n) = ⋃ i : Fin 2, S i := by
          ext x
          simp only [Set.mem_union, Set.mem_iUnion, S]
          constructor
          · intro h
            cases h with
            | inl hF => exact ⟨0, by simp [hF]⟩
            | inr hDiff => exact ⟨1, by simp [hDiff]⟩
          · intro ⟨i, hi⟩
            fin_cases i
            · left; exact hi
            · right; exact hi
        rw [h_eq]
        calc Lebesgue_measure (⋃ i : Fin 2, S i)
            ≤ ∑ i : Fin 2, Lebesgue_outer_measure (S i) := Lebesgue_outer_measure.finite_union_le S
          _ = Lebesgue_outer_measure (S 0) + Lebesgue_outer_measure (S 1) := Fin.sum_univ_two _
          _ = Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := by simp only [S]; rfl
      calc Lebesgue_measure (E n) = Lebesgue_measure (F n ∪ (E n \ F n)) := by
            conv_lhs => rw [h_partition]
        _ ≤ Lebesgue_measure (F n) + Lebesgue_measure (E n \ F n) := h_binary_subadd
        _ ≤ Lebesgue_measure (F n) + ε / 2^(n+1) := by
          apply add_le_add_left
          exact (hF n).2.2
    -- Sum the approximations: ∑' m(E_n) ≤ ∑' m(F_n) + ∑' (ε/2^{n+1}) = ∑' m(F_n) + ε
    have h_sum_eps : ∑' n, (ε / (2 : EReal)^(n+1)) = ε := by
      -- ∑_{n=0}^∞ ε/2^{n+1} = ε · ∑_{n=0}^∞ 1/2^{n+1} = ε · 1 = ε
      -- First show (2 : EReal)^k = ((2^k : ℝ) : EReal) by induction
      have h2_eq : ∀ k : ℕ, (2 : EReal) ^ k = ((2 ^ k : ℝ) : EReal) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => simp only [pow_succ]; rw [ih]; push_cast; rfl
      -- Show EReal division equals Real division coerced
      have h_eq : ∀ n, (ε : EReal) / (2 : EReal) ^ (n + 1) = ((ε / (2 : ℝ)^(n+1)) : ℝ) := fun n => by
        rw [h2_eq (n + 1), ← EReal.coe_div]
      -- Summability and non-negativity for Real series
      have h_nn : ∀ n, 0 ≤ ε / (2 : ℝ)^(n+1) := fun n => by positivity
      have h_sum : Summable (fun n => ε / (2 : ℝ)^(n+1)) := by
        have h_eq_fn : (fun n => ε / (2 : ℝ)^(n+1)) = (fun n => ε/2 * (1/2 : ℝ)^n) := by
          ext n
          have h2 : (2 : ℝ) ^ (n+1) = 2 * 2^n := by ring
          field_simp [h2]; ring_nf; simp [← mul_pow]
        rw [h_eq_fn]
        exact summable_geometric_two.mul_left (ε/2)
      simp_rw [h_eq, ← EReal.coe_tsum_of_nonneg h_nn h_sum, tsum_geometric_eps ε hε]
    -- ∑' m(E_n) ≤ ∑' m(F_n) + ε
    have h_tsum_approx : ∑' n, Lebesgue_measure (E n) ≤ ∑' n, Lebesgue_measure (F n) + ε := by
      -- Lift to ENNReal where tsum_le_tsum and tsum_add work cleanly
      let mE_enn : ℕ → ENNReal := fun n => (Lebesgue_measure (E n)).toENNReal
      let mF_enn : ℕ → ENNReal := fun n => (Lebesgue_measure (F n)).toENNReal
      let eps_enn : ℕ → ENNReal := fun n => ((ε : EReal) / 2 ^ (n + 1)).toENNReal
      have h_mE_nn : ∀ n, 0 ≤ Lebesgue_measure (E n) := fun n => Lebesgue_outer_measure.nonneg (E n)
      have h_mF_nn : ∀ n, 0 ≤ Lebesgue_measure (F n) := fun n => Lebesgue_outer_measure.nonneg (F n)
      have h_eps_nn : ∀ n, (0 : EReal) ≤ (ε : EReal) / 2 ^ (n + 1) := fun n => le_of_lt (h_eps_pos n)
      -- Coerce back: x = x.toENNReal for non-negative EReal
      have h_mE_coe : ∀ n, Lebesgue_measure (E n) = (mE_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_mE_nn n)).symm
      have h_mF_coe : ∀ n, Lebesgue_measure (F n) = (mF_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_mF_nn n)).symm
      have h_eps_coe : ∀ n, (ε : EReal) / 2 ^ (n + 1) = (eps_enn n : EReal) := fun n =>
        (EReal.coe_toENNReal (h_eps_nn n)).symm
      -- In ENNReal: h_approx gives mE_enn n ≤ mF_enn n + eps_enn n
      have h_approx_enn : ∀ n, mE_enn n ≤ mF_enn n + eps_enn n := by
        intro n
        have h := h_approx n
        rw [h_mE_coe, h_mF_coe, h_eps_coe] at h
        rw [← EReal.coe_ennreal_add] at h
        exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h
      -- ENNReal tsum_le_tsum: ∑' mE_enn ≤ ∑' (mF_enn + eps_enn)
      have h_tsum_le : ∑' n, mE_enn n ≤ ∑' n, (mF_enn n + eps_enn n) :=
        ENNReal.tsum_le_tsum h_approx_enn
      -- ENNReal tsum_add: ∑' (mF_enn + eps_enn) = ∑' mF_enn + ∑' eps_enn
      have h_tsum_add : ∑' n, (mF_enn n + eps_enn n) = ∑' n, mF_enn n + ∑' n, eps_enn n :=
        ENNReal.tsum_add
      -- Coerce back to EReal
      simp_rw [h_mE_coe, h_mF_coe]
      -- Use continuous coercion to lift tsum results
      have h_cont : Continuous (fun x : ENNReal => (x : EReal)) := continuous_coe_ennreal_ereal
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := rfl
        map_add' := EReal.coe_ennreal_add
      }
      have h_tsum_mE : ∑' n, (mE_enn n : EReal) = φ (∑' n, mE_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      have h_tsum_mF : ∑' n, (mF_enn n : EReal) = φ (∑' n, mF_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      have h_tsum_eps : ∑' n, (eps_enn n : EReal) = φ (∑' n, eps_enn n) :=
        (Summable.map_tsum ENNReal.summable φ h_cont).symm
      rw [h_tsum_mE, h_tsum_mF]
      -- Show φ (∑' mE_enn) ≤ φ (∑' mF_enn) + ε
      calc φ (∑' n, mE_enn n)
          ≤ φ (∑' n, (mF_enn n + eps_enn n)) := by
            apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_tsum_le
        _ = φ (∑' n, mF_enn n + ∑' n, eps_enn n) := by rw [h_tsum_add]
        _ = φ (∑' n, mF_enn n) + φ (∑' n, eps_enn n) := φ.map_add _ _
        _ = φ (∑' n, mF_enn n) + ∑' n, (eps_enn n : EReal) := by rw [← h_tsum_eps]
        _ = φ (∑' n, mF_enn n) + ∑' n, (ε : EReal) / 2 ^ (n + 1) := by simp_rw [← h_eps_coe]
        _ = φ (∑' n, mF_enn n) + ε := by rw [h_sum_eps]
    -- m(⋃ F_n) ≤ m(⋃ E_n) by monotonicity (since F_n ⊆ E_n)
    have h_union_mono : Lebesgue_measure (⋃ n, F n) ≤ Lebesgue_measure (⋃ n, E n) := by
      apply Lebesgue_outer_measure.mono
      apply Set.iUnion_mono
      intro n
      exact (hF n).2.1
    -- Combine: ∑' m(E_n) ≤ ∑' m(F_n) + ε = m(⋃ F_n) + ε ≤ m(⋃ E_n) + ε
    calc ∑' n, Lebesgue_measure (E n)
        ≤ ∑' n, Lebesgue_measure (F n) + ε := h_tsum_approx
      _ = Lebesgue_measure (⋃ n, F n) + ε := by rw [h_compact_case]
      _ ≤ Lebesgue_measure (⋃ n, E n) + ε := add_le_add_right h_union_mono ε
  exact le_antisymm h_le h_ge

/-- Lemma 1.2.15(b) (Countable additivity).
    Strategy: m(⋃ E_n) = ∑' m(E_n) for pairwise disjoint measurable sets.
    - Direction ≤: Countable subadditivity (Lebesgue_outer_measure.union_le)
    - Direction ≥: Decompose ℝᵈ into annuli Aₘ, express each E_n = ⋃_m (E_n ∩ Aₘ),
      apply bounded case to the doubly-indexed family (E_n ∩ Aₘ). -/
theorem Lebesgue_measure.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Direction ≤: Countable subadditivity
  have h_le : Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_measure (E n) :=
    Lebesgue_outer_measure.union_le E
  -- Direction ≥: Use annuli decomposition for general case
  have h_ge : ∑' n, Lebesgue_measure (E n) ≤ Lebesgue_measure (⋃ n, E n) := by
    -- Handle d = 0 case separately (trivial)
    by_cases hd : d = 0
    · -- In dimension 0, the space is a singleton (Subsingleton), so any pairwise disjoint
      -- family has at most one nonempty set. The sum equals the measure of the union.
      subst hd
      haveI : Subsingleton (EuclideanSpace' 0) := inferInstance
      -- Each E n is either ∅ or univ (the singleton). For disjoint sets, at most one is nonempty.
      by_cases h_empty : ∀ n, E n = ∅
      · -- All sets are empty: both sides are 0
        simp_rw [h_empty, Set.iUnion_empty]
        simp only [Lebesgue_measure.empty, tsum_zero, le_refl]
      · -- At least one E n is nonempty; by disjointness in a subsingleton, exactly one
        push_neg at h_empty
        obtain ⟨n₀, hn₀⟩ := h_empty
        -- In a Subsingleton, a nonempty set equals univ
        have hE_univ : E n₀ = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact Subsingleton.mem_iff_nonempty.mpr hn₀
        -- All other E m must be empty (disjoint from E n₀ = univ)
        have hE_empty : ∀ m, m ≠ n₀ → E m = ∅ := by
          intro m hm
          have hdisj' : Disjoint (E n₀) (E m) := hdisj (Set.mem_univ n₀) (Set.mem_univ m) hm.symm
          rw [hE_univ, Set.disjoint_iff] at hdisj'
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          have : x ∈ Set.univ ∩ E m := ⟨Set.mem_univ x, hx⟩
          exact Set.notMem_empty x (hdisj' this)
        -- The union equals E n₀
        have h_union : (⋃ n, E n) = E n₀ := by
          ext x
          simp only [Set.mem_iUnion]
          constructor
          · intro ⟨n, hxn⟩
            by_cases hn : n = n₀
            · exact hn ▸ hxn
            · rw [hE_empty n hn] at hxn
              exact (Set.notMem_empty x hxn).elim
          · intro hx
            exact ⟨n₀, hx⟩
        -- The sum has only one nonzero term
        have h_sum : ∑' n, Lebesgue_measure (E n) = Lebesgue_measure (E n₀) := by
          apply tsum_eq_single n₀
          intro m hm
          rw [hE_empty m hm, Lebesgue_measure.empty]
        rw [h_sum, h_union]
    · -- For d ≥ 1, use the annuli decomposition from the textbook
      push_neg at hd
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      -- Define annuli: A_m = { x : m ≤ |x| < m+1 } for m ≥ 0
      -- Then ℝᵈ = ⋃_m A_m (disjoint union) and each A_m is bounded
      let A : ℕ → Set (EuclideanSpace' d) := fun m =>
        { x | (m : ℝ) ≤ ‖x‖ ∧ ‖x‖ < m + 1 }
      -- Each annulus is bounded
      have hA_bdd : ∀ m, Bornology.IsBounded (A m) := by
        intro m
        rw [Metric.isBounded_iff_subset_closedBall 0]
        use m + 1
        intro x hx
        simp only [Metric.mem_closedBall, dist_zero_right, A, Set.mem_setOf_eq] at hx ⊢
        exact le_of_lt hx.2
      -- The annuli cover all of ℝᵈ
      have hA_cover : ∀ x : EuclideanSpace' d, ∃ m, x ∈ A m := by
        intro x
        use ⌊‖x‖⌋₊
        simp only [A, Set.mem_setOf_eq]
        constructor
        · exact Nat.floor_le (norm_nonneg x)
        · exact Nat.lt_floor_add_one ‖x‖
      -- The annuli are pairwise disjoint
      have hA_disj : Set.univ.PairwiseDisjoint A := by
        intro i _ j _ hij
        simp only [Function.onFun, Set.disjoint_iff]
        intro x ⟨hi, hj⟩
        simp only [A, Set.mem_setOf_eq, Set.mem_empty_iff_false] at hi hj ⊢
        by_cases h : i < j
        · have h1 : (j : ℝ) ≤ ‖x‖ := hj.1
          have h2 : ‖x‖ < i + 1 := hi.2
          have h3 : (j : ℝ) < i + 1 := lt_of_le_of_lt h1 h2
          have h4 : j < i + 1 := by exact_mod_cast h3
          omega
        · push_neg at h
          have hji : j < i := lt_of_le_of_ne h (Ne.symm hij)
          have h1 : (i : ℝ) ≤ ‖x‖ := hi.1
          have h2 : ‖x‖ < j + 1 := hj.2
          have h3 : (i : ℝ) < j + 1 := lt_of_le_of_lt h1 h2
          have h4 : i < j + 1 := by exact_mod_cast h3
          omega
      -- Define the doubly-indexed family E'(n,m) = E_n ∩ A_m
      let E' : ℕ × ℕ → Set (EuclideanSpace' d) := fun ⟨n, m⟩ => E n ∩ A m
      -- E' is measurable (intersection of measurable and Borel sets)
      have hE'_mes : ∀ p, LebesgueMeasurable (E' p) := by
        intro ⟨n, m⟩
        -- E n is measurable, A m is Borel (hence measurable)
        have hA_meas : LebesgueMeasurable (A m) := by
          -- A m = { x | m ≤ ‖x‖ } ∩ { x | ‖x‖ < m + 1 }
          -- { x | m ≤ ‖x‖ } is closed, { x | ‖x‖ < m + 1 } is open
          have h1 : IsClosed { x : EuclideanSpace' d | (m : ℝ) ≤ ‖x‖ } :=
            isClosed_le continuous_const continuous_norm
          have h2 : IsOpen { x : EuclideanSpace' d | ‖x‖ < (m : ℝ) + 1 } :=
            isOpen_lt continuous_norm continuous_const
          have heq : A m = { x | (m : ℝ) ≤ ‖x‖ } ∩ { x | ‖x‖ < (m : ℝ) + 1 } := by
            ext x; simp only [A, Set.mem_setOf_eq, Set.mem_inter_iff]
          rw [heq]
          exact LebesgueMeasurable.inter h1.measurable h2.measurable
        exact LebesgueMeasurable.inter (hmes n) hA_meas
      -- E' is bounded (subset of bounded A_m)
      have hE'_bdd : ∀ p, Bornology.IsBounded (E' p) := by
        intro ⟨n, m⟩
        exact Bornology.IsBounded.subset (hA_bdd m) Set.inter_subset_right
      -- E' is pairwise disjoint
      have hE'_disj : Set.univ.PairwiseDisjoint E' := by
        intro ⟨n₁, m₁⟩ _ ⟨n₂, m₂⟩ _ hne
        simp only [E', Function.onFun]
        by_cases hn : n₁ = n₂
        · -- Same n, different m: disjoint by annuli
          subst hn
          have hm : m₁ ≠ m₂ := by
            intro heq
            exact hne (Prod.ext rfl heq)
          have hA_disj' : Disjoint (A m₁) (A m₂) :=
            hA_disj (Set.mem_univ m₁) (Set.mem_univ m₂) hm
          exact Set.disjoint_of_subset_left Set.inter_subset_right
            (Set.disjoint_of_subset_right Set.inter_subset_right hA_disj')
        · -- Different n: disjoint by original family
          have hE_disj' : Disjoint (E n₁) (E n₂) :=
            hdisj (Set.mem_univ n₁) (Set.mem_univ n₂) hn
          exact Set.disjoint_of_subset_left Set.inter_subset_left
            (Set.disjoint_of_subset_right Set.inter_subset_left hE_disj')
      -- ⋃_n E_n = ⋃_p E' p (reindex the union)
      have h_union_eq : (⋃ n, E n) = ⋃ p, E' p := by
        ext x
        simp only [Set.mem_iUnion, E']
        constructor
        · intro ⟨n, hx⟩
          obtain ⟨m, hm⟩ := hA_cover x
          exact ⟨⟨n, m⟩, ⟨hx, hm⟩⟩
        · intro ⟨⟨n, m⟩, hx⟩
          exact ⟨n, hx.1⟩
      -- Apply countable_union_bounded to E' (reindexed as ℕ via equivalence ℕ × ℕ ≃ ℕ)
      -- Step 1: Reindex E' to E'' : ℕ → Set using Nat.pairEquiv
      let e := Nat.pairEquiv.symm  -- e : ℕ ≃ ℕ × ℕ
      let E'' : ℕ → Set (EuclideanSpace' d) := fun k => E' (e k)
      -- Step 2: E'' inherits measurability, boundedness, and disjointness
      have hE''_mes : ∀ k, LebesgueMeasurable (E'' k) := fun k => hE'_mes (e k)
      have hE''_bdd : ∀ k, Bornology.IsBounded (E'' k) := fun k => hE'_bdd (e k)
      have hE''_disj : Set.univ.PairwiseDisjoint E'' := by
        intro i _ j _ hij
        simp only [E'', Function.onFun]
        have hne : e i ≠ e j := by
          intro heq
          apply hij
          exact e.injective heq
        exact hE'_disj (Set.mem_univ (e i)) (Set.mem_univ (e j)) hne
      -- Step 3: The unions are equal
      have h_union_E'' : (⋃ p, E' p) = ⋃ k, E'' k := by
        ext x
        simp only [Set.mem_iUnion, E'']
        constructor
        · intro ⟨p, hp⟩
          use e.symm p
          simp [hp]
        · intro ⟨k, hk⟩
          use e k
      -- Step 4: Apply countable_union_bounded to E''
      have h_E''_eq : Lebesgue_measure (⋃ k, E'' k) = ∑' k, Lebesgue_measure (E'' k) :=
        Lebesgue_measure.countable_union_bounded hd_pos hE''_mes hE''_bdd hE''_disj
      -- Step 5: Relate sums: ∑' k, m(E'' k) = ∑' p, m(E' p) by reindexing
      have h_tsum_reindex : ∑' k, Lebesgue_measure (E'' k) = ∑' p, Lebesgue_measure (E' p) := by
        rw [show (∑' p, Lebesgue_measure (E' p)) = ∑' k, Lebesgue_measure (E' (e k)) from
          (Equiv.tsum_eq e (fun p => Lebesgue_measure (E' p))).symm]
      -- Step 6: Relate ∑' n, m(E n) to ∑' p, m(E' p)
      -- Each E n = ⋃ k, (E n ∩ A k) is a disjoint union of bounded measurable sets
      -- So m(E n) = ∑' k, m(E n ∩ A k) by countable_union_bounded
      have h_En_decomp : ∀ n, Lebesgue_measure (E n) = ∑' k, Lebesgue_measure (E n ∩ A k) := by
        intro n
        -- Define the family for fixed n
        let F : ℕ → Set (EuclideanSpace' d) := fun k => E n ∩ A k
        have hF_eq : E n = ⋃ k, F k := by
          ext x
          simp only [F, Set.mem_iUnion, Set.mem_inter_iff]
          constructor
          · intro hx
            obtain ⟨k, hk⟩ := hA_cover x
            exact ⟨k, hx, hk⟩
          · intro ⟨k, hx, _⟩
            exact hx
        have hF_mes : ∀ k, LebesgueMeasurable (F k) := fun k => hE'_mes (n, k)
        have hF_bdd : ∀ k, Bornology.IsBounded (F k) := fun k => hE'_bdd (n, k)
        have hF_disj : Set.univ.PairwiseDisjoint F := by
          intro k₁ _ k₂ _ hk
          simp only [F, Function.onFun]
          have hA_disj' : Disjoint (A k₁) (A k₂) :=
            hA_disj (Set.mem_univ k₁) (Set.mem_univ k₂) hk
          exact Set.disjoint_of_subset_right Set.inter_subset_right
            (Set.disjoint_of_subset_left Set.inter_subset_right hA_disj')
        calc Lebesgue_measure (E n)
            = Lebesgue_measure (⋃ k, F k) := by rw [hF_eq]
          _ = ∑' k, Lebesgue_measure (F k) :=
              Lebesgue_measure.countable_union_bounded hd_pos hF_mes hF_bdd hF_disj
          _ = ∑' k, Lebesgue_measure (E n ∩ A k) := rfl
      -- Step 7: Now relate the double sum to the product sum
      -- ∑' n, m(E n) = ∑' n, ∑' k, m(E n ∩ A k) = ∑' (n,k), m(E n ∩ A k) = ∑' p, m(E' p)
      have h_sum_eq : ∑' n, Lebesgue_measure (E n) = ∑' p, Lebesgue_measure (E' p) := by
        simp_rw [h_En_decomp]
        -- Need: ∑' n, ∑' k, m(E n ∩ A k) = ∑' p, m(E' p)
        -- Simplify the inner sums to use E'
        have h_eq : ∀ n k, Lebesgue_measure (E n ∩ A k) = Lebesgue_measure (E' (n, k)) := by
          intro n k; simp only [E']
        simp_rw [h_eq]
        -- Now need: ∑' n, ∑' k, m(E' (n, k)) = ∑' p, m(E' p)
        -- Lift to ENNReal where tsum_prod' works unconditionally
        -- Define ENNReal version: f_enn p = m(E' p).toENNReal
        let f_enn : ℕ × ℕ → ENNReal := fun p => (Lebesgue_measure (E' p)).toENNReal
        -- Lebesgue measure is non-negative, so toENNReal is well-defined
        have hf_nn : ∀ p, 0 ≤ Lebesgue_measure (E' p) := fun p => Lebesgue_outer_measure.nonneg (E' p)
        -- ENNReal.tsum_prod' gives: ∑' p, f_enn p = ∑' n, ∑' k, f_enn (n, k)
        have h_enn_prod : ∑' n, ∑' k, f_enn (n, k) = ∑' p, f_enn p := ENNReal.tsum_prod'.symm
        -- Coerce back to EReal: For non-negative EReal, x = (x.toENNReal : EReal)
        have h_coe : ∀ p, Lebesgue_measure (E' p) = (f_enn p : EReal) := by
          intro p
          simp only [f_enn]
          exact (EReal.coe_toENNReal (hf_nn p)).symm
        simp_rw [h_coe]
        -- Now need: ∑' n, ∑' k, (f_enn (n, k) : EReal) = ∑' p, (f_enn p : EReal)
        -- Use continuous coercion from ENNReal to EReal
        have h_cont : Continuous (fun x : ENNReal => (x : EReal)) := continuous_coe_ennreal_ereal
        -- Define coercion as AddMonoidHom
        let φ : ENNReal →+ EReal := {
          toFun := (↑·)
          map_zero' := rfl
          map_add' := EReal.coe_ennreal_add
        }
        -- Map tsum through coercion using Summable.map_tsum
        -- For ENNReal, Summable always holds
        have h_map_outer : ∑' p, (f_enn p : EReal) = φ (∑' p, f_enn p) :=
          (Summable.map_tsum ENNReal.summable φ h_cont).symm
        have h_map_inner : ∀ n, ∑' k, (f_enn (n, k) : EReal) = φ (∑' k, f_enn (n, k)) := by
          intro n
          exact (Summable.map_tsum ENNReal.summable φ h_cont).symm
        have h_map_double : ∑' n, φ (∑' k, f_enn (n, k)) = φ (∑' n, ∑' k, f_enn (n, k)) :=
          (Summable.map_tsum ENNReal.summable φ h_cont).symm
        simp_rw [h_map_inner]
        rw [h_map_double, h_map_outer, h_enn_prod]
      -- Final step: combine everything
      calc ∑' n, Lebesgue_measure (E n)
          = ∑' p, Lebesgue_measure (E' p) := h_sum_eq
        _ = ∑' k, Lebesgue_measure (E'' k) := h_tsum_reindex.symm
        _ = Lebesgue_measure (⋃ k, E'' k) := h_E''_eq.symm
        _ = Lebesgue_measure (⋃ p, E' p) := by rw [← h_union_E'']
        _ = Lebesgue_measure (⋃ n, E n) := by rw [← h_union_eq]
        _ ≤ Lebesgue_measure (⋃ n, E n) := le_refl _
  exact le_antisymm h_le h_ge

theorem Lebesgue_measure.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  -- Strategy: Extend E to ℕ-indexed family by padding with empty sets, then use countable_union
  -- Define E' : ℕ → Set by E'(k) = E(k) if k < n, else ∅
  let E' : ℕ → Set (EuclideanSpace' d) := fun k =>
    if h : k < n then E ⟨k, h⟩ else ∅

  -- The union over Fin n equals the union over ℕ with E'
  have h_union : (⋃ i : Fin n, E i) = (⋃ k, E' k) := by
    ext x
    simp only [Set.mem_iUnion, E']
    constructor
    · intro ⟨i, hi⟩
      use i.val
      simp [hi]
    · intro ⟨k, hx⟩
      by_cases hk : k < n
      · use ⟨k, hk⟩
        simpa [dif_pos hk] using hx
      · simp [dif_neg hk] at hx

  -- E' is measurable (E(k) is measurable, ∅ is measurable)
  have hmes' : ∀ k, LebesgueMeasurable (E' k) := by
    intro k
    simp only [E']
    by_cases hk : k < n
    · simp [dif_pos hk]
      exact hmes ⟨k, hk⟩
    · simp [dif_neg hk]
      exact LebesgueMeasurable.empty

  -- E' is pairwise disjoint
  have hdisj' : Set.univ.PairwiseDisjoint E' := by
    intro i _ j _ hij
    simp only [E', Function.onFun]
    by_cases hi : i < n <;> by_cases hj : j < n
    · simp only [dif_pos hi, dif_pos hj]
      have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
        intro heq
        apply hij
        exact congrArg Fin.val heq
      exact hdisj (Set.mem_univ _) (Set.mem_univ _) hne
    · simp only [dif_pos hi, dif_neg hj]
      exact disjoint_bot_right
    · simp only [dif_neg hi, dif_pos hj]
      exact disjoint_bot_left
    · simp only [dif_neg hi, dif_neg hj]
      exact disjoint_bot_left

  -- Apply countable_union
  rw [h_union, Lebesgue_measure.countable_union hmes' hdisj']

  -- The tsum over ℕ equals the tsum over Fin n (since E' k = ∅ for k ≥ n)
  have h_empty : ∀ k ≥ n, E' k = ∅ := fun k hk => dif_neg (not_lt.mpr hk)
  have h_measure_empty : ∀ k ≥ n, Lebesgue_measure (E' k) = 0 := by
    intro k hk
    rw [h_empty k hk, Lebesgue_measure.empty]

  -- Convert tsum over ℕ to tsum over Fin n
  -- Key: E' k = E ⟨k, h⟩ for k < n, and E' k = ∅ for k ≥ n

  -- Direct approach: show term-by-term equality using the embedding
  have h_eq_terms : ∀ i : Fin n, Lebesgue_measure (E' i.val) = Lebesgue_measure (E i) := by
    intro i
    simp only [E', dif_pos i.isLt]

  -- The tsum over ℕ equals the tsum over Fin n via reindexing
  -- Show that the support of E' is contained in {k : k < n}
  have h_support : Function.support (fun k => Lebesgue_measure (E' k)) ⊆ Set.Iio n := by
    intro k hk
    simp only [Set.mem_Iio]
    contrapose! hk
    simp only [Function.mem_support, not_not]
    exact h_measure_empty k hk
  -- Reindex from ℕ to Set.Iio n
  rw [← tsum_subtype_eq_of_support_subset h_support]
  -- Define equivalence between ↑(Set.Iio n) and Fin n
  let e : ↑(Set.Iio n) ≃ Fin n := {
    toFun := fun ⟨k, hk⟩ => ⟨k, Set.mem_Iio.mp hk⟩
    invFun := fun i => ⟨i.val, Set.mem_Iio.mpr i.isLt⟩
    left_inv := fun ⟨k, hk⟩ => rfl
    right_inv := fun i => rfl
  }
  -- Use the equivalence to reindex the tsum
  rw [← Equiv.tsum_eq e]
  congr 1
  ext ⟨k, hk⟩
  simp only [e, Equiv.coe_fn_mk]
  exact h_eq_terms ⟨k, Set.mem_Iio.mp hk⟩

theorem Lebesgue_measure.union {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hdisj: E ∩ F = ∅) : Lebesgue_measure (E ∪ F) = Lebesgue_measure E + Lebesgue_measure F := by
  -- Apply finite_union with n=2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have h_union : E ∪ F = ⋃ n, S n := by
    ext x
    simp only [S, Set.mem_union, Set.mem_iUnion]
    constructor
    · intro h
      cases h with
      | inl hl => exact ⟨0, hl⟩
      | inr hr => exact ⟨1, hr⟩
    · intro ⟨n, hn⟩
      fin_cases n
      · left; exact hn
      · right; exact hn
  have hmes : ∀ n, LebesgueMeasurable (S n) := by intro n; fin_cases n <;> simp [S, hE, hF]
  have hdisj' : Set.univ.PairwiseDisjoint S := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp only [S, Function.onFun]
      exact Set.disjoint_iff_inter_eq_empty.mpr hdisj
    · simp only [S, Function.onFun]
      exact Set.disjoint_iff_inter_eq_empty.mpr (Set.inter_comm F E ▸ hdisj)
    · exact (hij rfl).elim
  rw [h_union, Lebesgue_measure.finite_union hmes hdisj']
  rw [tsum_fintype]
  simp only [S, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Exercise 1.2.11(a) (Upward monotone convergence)-/
theorem Lebesgue_measure.upward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E n ⊆ E (n + 1)) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋃ n, E n))) := by
  sorry

/-- Exercise 1.2.11(b) (Downward monotone convergence)-/
theorem Lebesgue_measure.downward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n) (hfin: ∃ n, Lebesgue_measure (E n) < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by
  sorry

/-- Exercise 1.2.11 (c) (counterexample)-/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by sorry

/-- Exercise 1.2.12 -/
example {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E F: Set (EuclideanSpace' d)}
(hsub: E ⊆ F) (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : m E ≤ m F := by
  sorry

/-- Exercise 1.2.12 -/
example {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)):  m (⋃ n, E n) ≤ ∑' n, m (E n) := by
  sorry

/-- Exercise 1.2.13(i) -/
example {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} {E₀: Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x))) : LebesgueMeasurable E₀ := by sorry

/-- Exercise 1.2.13(ii) -/
example {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} {E₀ F: Set (EuclideanSpace' d)}
  (hE: ∀ n, LebesgueMeasurable (E n))
  (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)))
  (hsub: ∀ n, E n ⊆ F) (hFmes: LebesgueMeasurable F) (hfin: Lebesgue_measure F < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by sorry

/-- Exercise 1.2.13(iii) -/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (E₀ F: Set (EuclideanSpace' d))
  (hE: ∀ n, LebesgueMeasurable (E n))
  (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)))
  (hsub: ∀ n, E n ⊆ F) (hFmes: LebesgueMeasurable F), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by sorry

/-- Exercise 1.2.14 -/
example {d:ℕ} (E: Set (EuclideanSpace' d)) : ∃ (F: Set (EuclideanSpace' d)), E ⊆ F ∧ LebesgueMeasurable F ∧ Lebesgue_measure F = Lebesgue_outer_measure E := by sorry

/-- Exercise 1.2.15 (Inner regularity)-/
theorem Lebesgue_measure.eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): Lebesgue_measure E = sSup { M | ∃ K, K ⊆ E ∧ IsCompact K ∧ M = Lebesgue_measure K} := by
  sorry

/-- Exercise 1.2.16 (Criteria for measurability)-/
theorem LebesgueMeasurable.finite_TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_measure U < ⊤ ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Bornology.IsBounded U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_measure E' < ⊤ ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Bornology.IsBounded E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), IsElementary E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ (n:ℤ) (F: Finset (Box d)), (∀ B ∈ F, B.IsDyadicAtScale n) ∧ Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) ≤ ε)
    ].TFAE
  := by sorry

/-- Exercise 1.2.17 (Caratheodory criterion one direction)-/
theorem LebesgueMeasurable.caratheodory {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∀ A: Set (EuclideanSpace' d), IsElementary A → Lebesgue_outer_measure A = Lebesgue_outer_measure (A ∩ E) + Lebesgue_outer_measure (A \ E)),
      (∀ (B:Box d),  Lebesgue_outer_measure B.toSet = Lebesgue_outer_measure (B.toSet ∩ E) + Lebesgue_outer_measure (B.toSet \ E))
    ].TFAE
  := by sorry

theorem Bornology.IsBounded.inElementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ (A: Set (EuclideanSpace' d)), IsElementary A ∧ E ⊆ A := by sorry

noncomputable def inner_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ℝ := (Lebesgue_measure hE.inElementary.choose).toReal - (Lebesgue_measure (hE.inElementary.choose \ E)).toReal

/-- Exercise 1.2.18(i) (Inner measure)-/
theorem inner_measure.eq {d:ℕ} {E A: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  (hA: IsElementary A) (hsub: E ⊆ A) : inner_measure hE = Lebesgue_measure A - Lebesgue_outer_measure (A \ E) := by
  sorry

/-- Exercise 1.2.18(ii) (Inner measure)-/
theorem inner_measure.le {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  : inner_measure hE ≤ Lebesgue_outer_measure E := by
  sorry

/-- Exercise 1.2.18(ii) (Inner measure)-/
theorem inner_measure.eq_iff {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  : inner_measure hE = Lebesgue_outer_measure E ↔ LebesgueMeasurable E := by
  sorry

def IsFσ  {X:Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T

/-- Exercise 1.2.19 -/
theorem LebesgueMeasurable.TFAE' {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∃ F, ∃ N, IsGδ F ∧ IsNull N ∧ E = F \ N),
      (∃ F, ∃ N, IsFσ F ∧ IsNull N ∧ E = F ∪ N)
    ].TFAE
  := by sorry

open Pointwise

/-- Exercise 1.2.20 (Translation invariance) -/
theorem LebesgueMeasurable.translate {d:ℕ} (E: Set (EuclideanSpace' d)) (x: EuclideanSpace' d) :
    LebesgueMeasurable E ↔ LebesgueMeasurable (E + {x}) := by
  sorry

theorem Lebesgue_measure.translate {d:ℕ} {E: Set (EuclideanSpace' d)} (x: EuclideanSpace' d)
   (hE: LebesgueMeasurable E): Lebesgue_measure (E + {x}) = Lebesgue_measure E := by
  sorry

/-- Exercise 1.2.21 (Change of variables) -/
lemma LebesgueMeasurable.linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): LebesgueMeasurable (T '' E) := by
  sorry

/-- Exercise 1.2.21 (Change of variables) -/
lemma Lebesgue_measure.linear {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A]
 {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): Lebesgue_measure (A.linear_equiv '' E) = |A.det| * Lebesgue_measure E := by
  sorry

/-- Exercise 1.2.22 -/
theorem Lebesgue_outer_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ Lebesgue_outer_measure E₁ * Lebesgue_outer_measure E₂ := by sorry

/-- Exercise 1.2.22 -/
theorem LebesgueMeasurable.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: LebesgueMeasurable E₁) (hE₂: LebesgueMeasurable E₂) : LebesgueMeasurable (EuclideanSpace'.prod E₁ E₂) := by sorry

/-- Exercise 1.2.22 -/
theorem Lebesgue_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: LebesgueMeasurable E₁) (hE₂: LebesgueMeasurable E₂)
  : Lebesgue_measure (EuclideanSpace'.prod E₁ E₂) = Lebesgue_measure E₁ * Lebesgue_measure E₂ := by sorry

/-- Exercise 1.2.23 (Uniqueness of Lebesgue measure) -/
theorem Lebesgue_measure.unique {d:ℕ} (m: Set (EuclideanSpace' d) → EReal)
  (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E)
  (h_add: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n))
  (hnorm: m (Box.unit_cube d) = 1)
  : ∀ E, LebesgueMeasurable E → m E = Lebesgue_measure E := by sorry

/-- Exercise 1.2.24(i) (Lebesgue measure as the completion of elementary measure)-/
instance IsElementary.ae_equiv {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A):
Setoid (Set A) := {
   r E F := IsNull (Subtype.val '' (_root_.symmDiff E F))
   iseqv := by sorry
}

def IsElementary.ae_subsets {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) := Quotient hA.ae_equiv

def IsElementary.ae_quot {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: Set A): hA.ae_subsets := Quotient.mk' (s := hA.ae_equiv) E

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
noncomputable def IsElementary.dist {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : hA.ae_subsets → hA.ae_subsets → ℝ := Quotient.lift₂ (fun E F ↦ (Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff E F))).toReal) (by sorry)

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
noncomputable instance IsElementary.metric {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : MetricSpace hA.ae_subsets := {
    dist := hA.dist
    dist_self := by sorry
    eq_of_dist_eq_zero := by sorry
    dist_comm := by sorry
    dist_triangle := by sorry
  }

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
instance IsElementary.complete {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : CompleteSpace hA.ae_subsets := by
  sorry

noncomputable def IsElementary.ae_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, IsElementary (Subtype.val '' F) ∧ hA.ae_quot F = E }

noncomputable def IsElementary.ae_measurable {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, LebesgueMeasurable (Subtype.val '' F) ∧ hA.ae_quot F = E }

/-- Exercise 1.2.24(iii) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.measurable_eq_closure_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : closure hA.ae_elem = hA.ae_measurable := by
  sorry

/-- Exercise 1.2.24(c) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.measurable_complete {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : closure hA.ae_elem = hA.ae_measurable := by
  sorry

noncomputable def IsElementary.ae_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_measurable) : ℝ := (Lebesgue_measure (Subtype.val '' E.property.choose)).toReal

noncomputable def IsElementary.ae_elem_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_elem) : ℝ := E.property.choose_spec.1.measure

/-- Exercise 1.2.24(iv) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.ae_measure_eq_completion {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (m: hA.ae_subsets → ℝ) :
ContinuousOn m hA.ae_measurable ∧ (∀ (E:hA.ae_elem), m E.val = hA.ae_elem_measure E)
↔ (∀ (E:hA.ae_measurable), m E.val = hA.ae_measure E) := by sorry

noncomputable abbrev IsCurve {d:ℕ} (C: Set (EuclideanSpace' d)) : Prop := ∃ (a b:ℝ) (γ: ℝ → EuclideanSpace' d), C = γ '' (Set.Icc a b) ∧ ContDiffOn ℝ 1 γ (Set.Icc a b)

/-- Exercise 1.2.25(i) -/
theorem IsCurve.null {d:ℕ} (hd: d ≥ 2) {C: Set (EuclideanSpace' d)} (hC: IsCurve C) : IsNull C := by sorry

example : ∃ (d:ℕ) (C: Set (EuclideanSpace' d)) (hC: IsCurve C), ¬ IsNull Cx := by
  sorry

/-- Exercise 1.2.25 -/
example {d:ℕ} (hd: d ≥ 2) : ¬ ∃ C: ℕ → Set (EuclideanSpace' d), (∀ n, IsCurve (C n)) ∧ (⋃ n, C n = (Box.unit_cube d).toSet) := by
  sorry
