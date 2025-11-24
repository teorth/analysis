import Analysis.MeasureTheory.Section_1_2

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Exercise 1.2.3(i) (Empty set) -/
theorem Lebesgue_outer_measure.of_empty (d:ℕ) : Lebesgue_outer_measure (∅: Set (EuclideanSpace' d)) = 0 := by
  sorry

/-- Exercise 1.2.3(ii) (Monotonicity) -/
theorem Lebesgue_outer_measure.mono {d: ℕ} {E F : Set (EuclideanSpace' d)} (h : E ⊆ F) :
    Lebesgue_outer_measure E ≤ Lebesgue_outer_measure F := by
  sorry

/-- Exercise 1.2.3(iii) (Countable subadditivity) -/
theorem Lebesgue_outer_measure.union_le {d: ℕ} (E : ℕ → Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure (⋃ i, E i) ≤ ∑' i, Lebesgue_outer_measure (E i) := by
  sorry

/-- Finite subadditivity -/
theorem Lebesgue_outer_measure.finite_union_le {d n:ℕ} (E: Fin n → Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure (⋃ i, E i) ≤ ∑ i, Lebesgue_outer_measure (E i) := by
  -- Extend E to ℕ → Set by using empty set for indices ≥ n, then use countable subadditivity
  let E' : ℕ → Set (EuclideanSpace' d) := fun k =>
    if h : k < n then E ⟨k, h⟩ else ∅
  -- The union over Fin n equals the union over all k with E' k
  have h_union : (⋃ i, E i) = (⋃ k, E' k) := by
    ext x
    simp [E']
    constructor
    · intro ⟨i, hi⟩
      use i.val
      simp [hi]
    · intro ⟨k, hx⟩
      by_cases hk : k < n
      · use ⟨k, hk⟩
        simpa [dif_pos hk] using hx
      · simp [dif_neg hk] at hx
  rw [h_union]
  -- Apply countable subadditivity
  calc Lebesgue_outer_measure (⋃ k, E' k)
      ≤ ∑' k, Lebesgue_outer_measure (E' k) := union_le E'
    _ = ∑ i : Fin n, Lebesgue_outer_measure (E i) := by
        -- The sum over ℕ equals the sum over Fin n because E' k = ∅ for k ≥ n
        -- First, establish that E' k = ∅ for k ≥ n, so its outer measure is 0
        have h_empty : ∀ k ≥ n, E' k = ∅ := fun k hk => dif_neg (not_lt.mpr hk)
        have h_measure_empty : ∀ k ≥ n, Lebesgue_outer_measure (E' k) = 0 := by
          intro k hk
          rw [h_empty k hk, of_empty]

        -- Convert the tsum to a sum over Fin n
        -- The key lemma we need is: tsum equals finite sum when function has finite support
        -- In our case, E' k is non-empty only for k < n

        -- Define an explicit bijection and use it
        have : ∑' k, Lebesgue_outer_measure (E' k) = ∑ i : Fin n, Lebesgue_outer_measure (E' i.val) := by
          -- Use tsum_eq_sum with finite support
          let s : Finset ℕ := Finset.range n
          have h_support : ∀ k ∉ s, Lebesgue_outer_measure (E' k) = 0 := by
            intro k hk
            have : ¬ k < n := by simpa [s, Finset.mem_range] using hk
            exact h_measure_empty k (le_of_not_gt this)
          rw [tsum_eq_sum h_support]
          -- Now show the sums are equal by reindexing
          refine Finset.sum_bij (fun (k : ℕ) (hk : k ∈ s) => ⟨k, ?_⟩) ?_ ?_ ?_ ?_
          · simpa [s, Finset.mem_range] using hk
          · intros; simp
          · intros k₁ k₂ hk₁ hk₂ heq; simp at heq; exact heq
          · intro i _
            use i.val
            refine ⟨?_, ?_⟩
            · simp [s, Finset.mem_range, i.isLt]
            · simp
          · intro i _; simp

        rw [this]
        congr 1
        ext i
        simp [E', dif_pos i.isLt]


noncomputable def set_dist {X:Type*} [PseudoMetricSpace X] (A B: Set X) : ℝ :=
  sInf ((fun p: X × X ↦ dist p.1 p.2) '' (A ×ˢ B))

-- ========================================================================
-- Start of Helpers for lemma 1.2.5: Lebesgue_outer_measure.union_of_separated
-- ========================================================================
/-- For EReal, adding a positive real value to a value that is neither ⊥ nor ⊤ gives a strictly greater result. -/
lemma EReal.lt_add_of_pos_coe {x : EReal} {ε : ℝ} (hε : 0 < ε) (h_ne_bot : x ≠ ⊥) (h_ne_top : x ≠ ⊤) :
    x < x + ↑ε := by
  have h_eps : (0 : EReal) < (ε : EReal) := EReal.coe_pos.mpr hε
  have : 0 + x < ↑ε + x := EReal.add_lt_add_of_lt_of_le h_eps (le_refl x) h_ne_bot h_ne_top
  simpa [add_comm] using this

/-- The square root function is subadditive: √(x + y) ≤ √x + √y for non-negative reals.
    This follows from the fact that (√x + √y)² = x + y + 2√(xy) ≥ x + y. -/
lemma Real.sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  by_cases hxy : x + y = 0
  · simp [hxy]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · rw [Real.sqrt_le_left (by positivity)]
    have : x + y ≤ (√x + √y) ^ 2 := by
      calc x + y
          = (√x) ^ 2 + (√y) ^ 2 := by
              rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
        _ ≤ (√x) ^ 2 + (√y) ^ 2 + 2 * √x * √y := by
              apply le_add_of_nonneg_right
              apply mul_nonneg; apply mul_nonneg
              · norm_num
              · exact Real.sqrt_nonneg _
              · exact Real.sqrt_nonneg _
        _ = (√x + √y) ^ 2 := by ring
    exact this

/-- The square root function is subadditive over finite sums: √(∑ᵢ xᵢ) ≤ ∑ᵢ √xᵢ
    for non-negative terms. This is a consequence of the concavity of sqrt. -/
lemma Real.sqrt_sum_le_sum_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    √(∑ i, f i) ≤ ∑ i, √(f i) := by
  -- Proof by induction on the Finset
  let s := (Finset.univ : Finset ι)
  show √(∑ i ∈ s, f i) ≤ ∑ i ∈ s, √(f i)
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      simp [Finset.sum_insert hi]
      calc √(f i + ∑ x ∈ s, f x)
          ≤ √(f i) + √(∑ x ∈ s, f x) := by
              apply Real.sqrt_add_le_add_sqrt (hf i)
              apply Finset.sum_nonneg
              intro j _; exact hf j
        _ ≤ √(f i) + ∑ x ∈ s, √(f x) := by
              apply add_le_add_left
              exact ih

namespace Box

/-- The diameter of a box is the supremum of Euclidean distances between points in the box -/
noncomputable def diameter {d:ℕ} (B: Box d) : ℝ :=
  sSup { r | ∃ x ∈ B.toSet, ∃ y ∈ B.toSet, r = √(∑ i, (x i - y i)^2) }

/-- Diameter is always nonnegative -/
lemma diameter_nonneg {d:ℕ} (B: Box d) : 0 ≤ B.diameter := by
  unfold diameter
  by_cases h : B.toSet.Nonempty
  · obtain ⟨x, hx⟩ := h
    apply le_csSup
    · -- The set is bounded above
      use (∑ i : Fin d, |B.side i|ₗ)
      intro r ⟨y, hy, z, hz, hr⟩
      -- dist y z is bounded by sum of side lengths
      rw [hr]
      -- y, z ∈ B.toSet means ∀ i, y i ∈ B.side i and z i ∈ B.side i
      have hy_coord : ∀ i, y i ∈ (B.side i).toSet := by
        intro i; exact hy i (Set.mem_univ i)
      have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
        intro i; exact hz i (Set.mem_univ i)
      -- For each coordinate, the difference is bounded by the side length
      have coord_bound : ∀ i, |(y - z) i| ≤ |B.side i|ₗ := by
        intro i
        have hy_i := hy_coord i
        have hz_i := hz_coord i
        -- All interval types have the same bound: |y i - z i| ≤ max (b - a) 0
        -- This is because both y i and z i are in [a,b] (or (a,b) with open endpoints)
        cases h_side : B.side i with
        | Ioo a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Icc a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Ioc a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Ico a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
      -- Now prove that √(∑ (y i - z i)²) ≤ ∑ |B.side i|ₗ
      -- We use: √(∑ xᵢ²) ≤ ∑ √(xᵢ²) = ∑ |xᵢ| (subadditivity of sqrt)
      have sqrt_sum_le : (∑ i, (y i - z i) ^ 2).sqrt ≤ ∑ i, |(y i - z i)| := by
        -- ℓ² ≤ ℓ¹ norm: √(∑ xᵢ²) ≤ ∑ |xᵢ|
        calc (∑ i, (y i - z i) ^ 2).sqrt
            = (∑ i, |(y i - z i)| ^ 2).sqrt := by
                congr 1; congr 1; ext i; rw [sq_abs]
          _ ≤ ∑ i, (|(y i - z i)| ^ 2).sqrt := by
                -- Apply sqrt subadditivity lemma
                apply Real.sqrt_sum_le_sum_sqrt
                intro i; exact sq_nonneg _
          _ = ∑ i, |(y i - z i)| := by
                congr 1; ext i
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
      calc √(∑ i, (y i - z i) ^ 2)
          ≤ ∑ i, |(y i - z i)| := sqrt_sum_le
        _ = ∑ i, |(y - z) i| := by rfl
        _ ≤ ∑ i, |B.side i|ₗ := by
            apply Finset.sum_le_sum
            intro i _
            exact coord_bound i
    · -- 0 is in the set (distance from any point to itself)
      use x, hx, x, hx
      simp
  · -- Empty box has diameter 0
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    simp [sSup]

/-- Empty box has diameter 0 -/
lemma diameter_of_empty {d:ℕ} (B: Box d) (h: B.toSet = ∅) :
    B.diameter = 0 := by
  unfold diameter
  simp [h, sSup]

/-- Any two points in a box have Euclidean distance at most the diameter -/
lemma dist_le_diameter {d:ℕ} (B: Box d) {x y: EuclideanSpace' d}
    (hx: x ∈ B.toSet) (hy: y ∈ B.toSet) :
    √(∑ i, (x i - y i)^2) ≤ B.diameter := by
  unfold diameter
  apply le_csSup
  · -- The set is bounded above
    use (∑ i : Fin d, |B.side i|ₗ)
    intro r ⟨z, hz, w, hw, hr⟩
    -- dist z w is bounded by sum of side lengths
    rw [hr]
    -- z, w ∈ B.toSet means ∀ i, z i ∈ B.side i and w i ∈ B.side i
    have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
      intro i; exact hz i (Set.mem_univ i)
    have hw_coord : ∀ i, w i ∈ (B.side i).toSet := by
      intro i; exact hw i (Set.mem_univ i)
    -- For each coordinate, the difference is bounded by the side length
    have coord_bound : ∀ i, |(z - w) i| ≤ |B.side i|ₗ := by
      intro i
      have hz_i := hz_coord i
      have hw_i := hw_coord i
      -- All interval types have the same bound: |z i - w i| ≤ max (b - a) 0
      cases h_side : B.side i with
      | Ioo a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Icc a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Ioc a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Ico a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
    -- Now prove that √(∑ (z i - w i)²) ≤ ∑ |B.side i|ₗ
    have sqrt_sum_le : (∑ i, (z i - w i) ^ 2).sqrt ≤ ∑ i, |(z i - w i)| := by
      -- ℓ² ≤ ℓ¹ norm: √(∑ xᵢ²) ≤ ∑ |xᵢ|
      calc (∑ i, (z i - w i) ^ 2).sqrt
          = (∑ i, |(z i - w i)| ^ 2).sqrt := by
              congr 1; congr 1; ext i; rw [sq_abs]
        _ ≤ ∑ i, (|(z i - w i)| ^ 2).sqrt := by
              apply Real.sqrt_sum_le_sum_sqrt
              intro i; exact sq_nonneg _
        _ = ∑ i, |(z i - w i)| := by
              congr 1; ext i
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
    calc √(∑ i, (z i - w i) ^ 2)
        ≤ ∑ i, |(z i - w i)| := sqrt_sum_le
      _ = ∑ i, |(z - w) i| := by rfl
      _ ≤ ∑ i, |B.side i|ₗ := by
          apply Finset.sum_le_sum
          intro i _
          exact coord_bound i
  · -- √(∑ (x i - y i)²) is in the set
    exact ⟨x, hx, y, hy, rfl⟩

/-- Diameter is bounded by √d times the maximum side length -/
lemma diameter_bound_by_sides {d:ℕ} (B: Box d) :
    B.diameter ≤ Real.sqrt d * (⨆ i, |B.side i|ₗ) := by
  unfold diameter
  by_cases h : B.toSet.Nonempty
  · apply csSup_le
    · obtain ⟨x, hx⟩ := h
      exact ⟨√(∑ i, (x i - x i)^2), x, hx, x, hx, rfl⟩
    · intro r ⟨x, hx, y, hy, hr⟩
      -- √(∑ i, (x i - y i)²) ≤ √(d * max²) = √d * max
      rw [hr]
      let max_side := ⨆ i, |B.side i|ₗ
      -- Each coordinate difference is bounded by the maximum side length
      have coord_bound : ∀ i, |(x - y) i| ≤ max_side := by
        intro i
        have hx_i : x i ∈ (B.side i).toSet := hx i (Set.mem_univ i)
        have hy_i : y i ∈ (B.side i).toSet := hy i (Set.mem_univ i)
        -- |x i - y i| ≤ |B.side i|ₗ ≤ max_side
        have bound_by_side : |(x - y) i| ≤ |B.side i|ₗ := by
          cases h_side : B.side i with
          | Ioo a b =>
              simp [BoundedInterval.toSet, h_side] at hx_i hy_i
              simp [BoundedInterval.length]
              left
              rw [abs_sub_le_iff]
              constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2]
          | Icc a b =>
              simp [BoundedInterval.toSet, h_side] at hx_i hy_i
              simp [BoundedInterval.length]
              left
              rw [abs_sub_le_iff]
              constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2]
          | Ioc a b =>
              simp [BoundedInterval.toSet, h_side] at hx_i hy_i
              simp [BoundedInterval.length]
              left
              rw [abs_sub_le_iff]
              constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2]
          | Ico a b =>
              simp [BoundedInterval.toSet, h_side] at hx_i hy_i
              simp [BoundedInterval.length]
              left
              rw [abs_sub_le_iff]
              constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2]
        calc |(x - y) i|
            ≤ |B.side i|ₗ := bound_by_side
          _ ≤ max_side := by
              show |B.side i|ₗ ≤ ⨆ j, |B.side j|ₗ
              apply le_ciSup _ i
              -- The set is bounded above
              refine ⟨∑ j : Fin d, |B.side j|ₗ, ?_⟩
              intro r ⟨j, hj⟩
              simp only at hj
              rw [← hj]
              -- |B.side j|ₗ ≤ sum of all sides
              have single_le : ∀ j : Fin d, |B.side j|ₗ ≤ ∑ k : Fin d, |B.side k|ₗ := by
                intro j'
                calc |B.side j'|ₗ
                    = ∑ k ∈ ({j'} : Finset (Fin d)), |B.side k|ₗ := by simp
                  _ ≤ ∑ k ∈ Finset.univ, |B.side k|ₗ := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg
                      · intro x _; simp
                      · intro k _ _; simp [BoundedInterval.length]
                  _ = ∑ k : Fin d, |B.side k|ₗ := rfl
              exact single_le j
      -- Now: (x i - y i)² ≤ max_side² for each i
      have sq_bound : ∀ i, (x i - y i)^2 ≤ max_side^2 := by
        intro i
        have := coord_bound i
        calc (x i - y i)^2
            ≤ |(x i - y i)|^2 := by rw [← sq_abs]
          _ = |(x - y) i|^2 := by rfl
          _ ≤ max_side^2 := by
              apply sq_le_sq'
              · linarith [abs_nonneg ((x - y) i)]
              · exact this
      -- Sum: ∑ i, (x i - y i)² ≤ d * max_side²
      have sum_bound : ∑ i, (x i - y i)^2 ≤ d * max_side^2 := by
        calc ∑ i, (x i - y i)^2
            ≤ ∑ i : Fin d, max_side^2 := by
                apply Finset.sum_le_sum
                intro i _
                exact sq_bound i
          _ = Finset.card (Finset.univ : Finset (Fin d)) * max_side^2 := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ = d * max_side^2 := by
                rw [Finset.card_fin]
      -- Apply sqrt to both sides
      calc √(∑ i, (x i - y i)^2)
          ≤ √(d * max_side^2) := by
              apply Real.sqrt_le_sqrt
              exact sum_bound
        _ = √d * √(max_side^2) := by
              rw [Real.sqrt_mul (Nat.cast_nonneg d)]
        _ = √d * max_side := by
              rw [Real.sqrt_sq (by
                -- max_side ≥ 0
                apply Real.iSup_nonneg
                intro i
                -- BoundedInterval.length is max (b - a) 0, which is always ≥ 0
                simp [BoundedInterval.length])]
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    simp [sSup]
    apply mul_nonneg
    · exact Real.sqrt_nonneg _
    · apply Real.iSup_nonneg
      intro i
      -- BoundedInterval.length is max (b - a) 0, which is always ≥ 0
      simp [BoundedInterval.length]


/-- If a box intersects two sets, any two points (one from each set)
    in the box have distance at most the diameter -/
lemma diameter_ge_dist_of_intersects {d:ℕ} (B: Box d) (E F : Set (EuclideanSpace' d))
    (hE : (B.toSet ∩ E).Nonempty) (hF : (B.toSet ∩ F).Nonempty) :
    set_dist E F ≤ B.diameter := by
  obtain ⟨x, hx_box, hx_E⟩ := hE
  obtain ⟨y, hy_box, hy_F⟩ := hF
  -- set_dist E F ≤ dist x y (by definition of set_dist as infimum)
  have h_dist : set_dist E F ≤ dist x y := by
    unfold set_dist
    apply csInf_le
    · -- Bounded below by 0
      use 0
      intro r ⟨p, hp, hr⟩
      rw [← hr]
      exact dist_nonneg
    · -- The distance from x to y is in the set
      simp only [Set.mem_image]
      use (x, y)
      exact ⟨Set.mem_prod.mpr ⟨hx_E, hy_F⟩, rfl⟩
  -- dist x y ≤ B.diameter (by dist_le_diameter)
  have h_le_diam : √(∑ i, (x i - y i)^2) ≤ B.diameter :=
    dist_le_diameter B hx_box hy_box
  -- Note: For EuclideanSpace' d, dist x y = √(∑ i, (x i - y i)^2)
  have h_eq : dist x y = √(∑ i, (x i - y i)^2) := by
    simp only [EuclideanSpace.dist_eq]
    congr 1
    congr 1
    ext i
    rw [Real.dist_eq, sq_abs]
  -- Combine
  calc set_dist E F
      ≤ dist x y := h_dist
    _ = √(∑ i, (x i - y i)^2) := h_eq
    _ ≤ B.diameter := h_le_diam

/-- If B.diameter < set_dist E F, then B cannot intersect both E and F.
    This is the core geometric fact needed for finite additivity of separated sets. -/
lemma not_intersects_both_of_diameter_lt {d:ℕ} (B: Box d) (E F : Set (EuclideanSpace' d))
    (h : B.diameter < set_dist E F) :
    ¬((B.toSet ∩ E).Nonempty ∧ (B.toSet ∩ F).Nonempty) := by
  intro ⟨hE, hF⟩
  -- If B intersects both, then set_dist E F ≤ B.diameter
  have := diameter_ge_dist_of_intersects B E F hE hF
  -- But we assumed B.diameter < set_dist E F
  linarith

/-- Subdivide a box by bisecting each coordinate axis, producing 2^d sub-boxes.
    Each sub-box is formed by taking one half-interval from each coordinate. -/
def subdivide {d:ℕ} (B: Box d) : Finset (Box d) :=
  sorry

/-- The volume of a subdivided box equals the sum of its sub-box volumes -/
lemma volume_subdivide {d:ℕ} (B: Box d) :
    ∑ B' ∈ B.subdivide, |B'|ᵥ = |B|ᵥ := by
  sorry

/-- Each sub-box of a subdivision has diameter at most the original diameter divided by √2.
    This follows because each side is halved, reducing the diagonal by a factor related to √2. -/
lemma subdivide_diameter_bound {d:ℕ} (B: Box d) :
    ∀ B' ∈ B.subdivide, B'.diameter ≤ B.diameter / Real.sqrt 2 := by
  sorry

/-- The union of all sub-boxes equals the original box -/
lemma subdivide_covers {d:ℕ} (B: Box d) :
    (⋃ B' ∈ B.subdivide, B'.toSet) = B.toSet := by
  sorry

end Box

namespace Lebesgue_outer_measure
/-- For any set with finite outer measure, we can find a cover whose volume is within ε of the outer measure.
    This follows from the definition of outer measure as an infimum. -/
lemma exists_cover_close {d:ℕ} (hd: 0 < d)
    (E: Set (EuclideanSpace' d)) (ε: ℝ) (hε: 0 < ε)
    (h_finite: Lebesgue_outer_measure E ≠ ⊤) :
    ∃ (S: ℕ → Box d), E ⊆ ⋃ n, (S n).toSet ∧
      ∑' n, (S n).volume.toEReal ≤ Lebesgue_outer_measure E + ε := by
  -- Use the ℕ-indexed characterization of outer measure
  rw [Lebesgue_outer_measure_eq_nat_indexed hd] at h_finite ⊢

  -- Key fact: inf + ε is not a lower bound (since ε > 0)
  -- Therefore, there exists some cover with volume < inf + ε, which implies ≤ inf + ε

  have h_not_lb : ¬ IsGLB (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) ''
      { S | E ⊆ ⋃ n, (S n).toSet }) (sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) ''
      { S | E ⊆ ⋃ n, (S n).toSet }) + (ε : EReal)) := by
    intro h_glb
    -- If inf + ε were the GLB, then inf ≤ inf + ε ≤ inf (since inf is also a lower bound)
    -- This would imply ε ≤ 0, contradiction
    let img_set := ((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }
    let inf_val := sInf img_set
    -- sInf img_set is the GLB of img_set
    have h_inf_glb : IsGLB img_set inf_val := isGLB_sInf img_set
    -- From h_glb, we have that inf_val + ε is also a GLB
    -- But GLB is unique, so if both are GLBs, they must be equal
    -- However, inf_val < inf_val + ε (since ε > 0 and inf_val ≠ ⊥ and inf_val ≠ ⊤)
    -- inf_val is an infimum of box volumes (sums of volumes), which are non-negative, so inf_val ≠ ⊥
    have h_ne_bot : inf_val ≠ ⊥ := by
      intro h_eq
      -- If inf_val = ⊥, then ⊥ is the GLB of img_set
      have h_glb_bot : IsGLB img_set ⊥ := by rwa [← h_eq]
      -- But 0 is a lower bound of img_set (since all box volumes are non-negative)
      have h_zero_lb : (0 : EReal) ∈ lowerBounds img_set := by
        intro v hv
        obtain ⟨S, _, rfl⟩ := hv
        -- v = ∑' n, (S n).volume.toEReal, and each term is ≥ 0
        apply tsum_nonneg
        intro n
        exact EReal.coe_nonneg.mpr (by
          unfold Box.volume
          apply Finset.prod_nonneg
          intro i _
          unfold BoundedInterval.length
          exact le_max_right _ _)
      -- Since ⊥ is the GLB, we have 0 ≤ ⊥ (as 0 is a lower bound)
      have : (0 : EReal) ≤ ⊥ := h_glb_bot.2 h_zero_lb
      -- But 0 > ⊥ in EReal
      exact not_le.mpr EReal.bot_lt_zero this
    have h_lt : inf_val < inf_val + (ε : EReal) := EReal.lt_add_of_pos_coe hε h_ne_bot h_finite
    -- GLB is unique: if both x and y are GLBs of the same set, then x = y
    have h_eq : inf_val = inf_val + (ε : EReal) := h_inf_glb.unique h_glb
    -- But inf_val < inf_val + ε, contradicting h_eq
    rw [← h_eq] at h_lt
    simp at h_lt

  -- Since sInf is the infimum and sInf + ε is not a lower bound,
  -- there must exist some cover with volume ≤ sInf + ε
  let img_set := ((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }
  let inf_val := sInf img_set
  -- From h_not_lb, inf_val + ε is not a GLB, which means it's not a lower bound
  -- (since if it were a lower bound ≥ inf_val, it would have to equal inf_val to be a GLB)
  -- So there exists some element in img_set that is < inf_val + ε
  have h_exists_lt : ∃ v ∈ img_set, v < inf_val + (ε : EReal) := by
    -- If no such element existed, then inf_val + ε would be a lower bound
    by_contra h_not_exists
    push_neg at h_not_exists
    -- h_not_exists says: ∀ v ∈ img_set, inf_val + ε ≤ v
    -- This means inf_val + ε is a lower bound
    have h_is_lb : inf_val + (ε : EReal) ∈ lowerBounds img_set := by
      intro v hv
      exact h_not_exists v hv
    -- And since inf_val is the GLB (greatest lower bound), we have inf_val + ε ≤ inf_val
    have h_inf_glb : IsGLB img_set inf_val := isGLB_sInf img_set
    have h_le : inf_val + (ε : EReal) ≤ inf_val := h_inf_glb.2 h_is_lb
    -- But we also have inf_val < inf_val + ε (since ε > 0, inf_val ≠ ⊥, and inf_val ≠ ⊤)
    -- inf_val is an infimum of box volumes, which are non-negative, so inf_val ≠ ⊥
    have h_ne_bot : inf_val ≠ ⊥ := by
      intro h_eq
      have h_glb_bot : IsGLB img_set ⊥ := by rwa [← h_eq]
      have h_zero_lb : (0 : EReal) ∈ lowerBounds img_set := by
        intro v hv
        obtain ⟨S, _, rfl⟩ := hv
        apply tsum_nonneg
        intro n
        exact EReal.coe_nonneg.mpr (by
          unfold Box.volume
          apply Finset.prod_nonneg
          intro i _
          unfold BoundedInterval.length
          exact le_max_right _ _)
      have : (0 : EReal) ≤ ⊥ := h_glb_bot.2 h_zero_lb
      exact not_le.mpr EReal.bot_lt_zero this
    have h_lt : inf_val < inf_val + (ε : EReal) := EReal.lt_add_of_pos_coe hε h_ne_bot h_finite
    -- Contradiction: h_le says inf_val + ε ≤ inf_val, but h_lt says inf_val < inf_val + ε
    have : inf_val < inf_val := calc inf_val
        < inf_val + ↑ε := h_lt
      _ ≤ inf_val := h_le
    exact lt_irrefl _ this
  -- Extract the witness from the image set
  obtain ⟨v, ⟨S, hS_cover, rfl⟩, hv_lt⟩ := h_exists_lt
  -- S is our witness cover
  exact ⟨S, hS_cover, le_of_lt hv_lt⟩

/-- Refine a cover so that all boxes have diameter less than a given threshold.
    This is done by repeatedly subdividing boxes that are too large. -/
def refine_cover_to_diameter {d:ℕ} (S: ℕ → Box d) (r: ℝ) (hr: 0 < r) : ℕ → Box d :=
  sorry

/-- The refined cover still covers the same region -/
lemma refine_cover_preserves_union {d:ℕ} (S: ℕ → Box d) (r: ℝ) (hr: 0 < r) :
    (⋃ n, (S n).toSet) ⊆ (⋃ n, (refine_cover_to_diameter S r hr n).toSet) := by
  sorry

/-- The refined cover has total volume no greater than the original cover -/
lemma refine_cover_volume_bound {d:ℕ} (S: ℕ → Box d) (r: ℝ) (hr: 0 < r) :
    ∑' n, (refine_cover_to_diameter S r hr n).volume.toEReal ≤ ∑' n, (S n).volume.toEReal := by
  sorry

/-- All boxes in the refined cover have diameter less than r -/
lemma refine_cover_diameter_bound {d:ℕ} (S: ℕ → Box d) (r: ℝ) (hr: 0 < r) :
    ∀ n, (refine_cover_to_diameter S r hr n).diameter < r := by
  sorry

/-- The set of indices of boxes that intersect a given set E -/
def intersecting_indices {d:ℕ} (S: ℕ → Box d) (E: Set (EuclideanSpace' d)) : Set ℕ :=
  { n | ((S n).toSet ∩ E).Nonempty }

/-- If all boxes have diameter less than dist(E,F), then the sets of indices intersecting
    E and F are disjoint. This follows from Box.not_intersects_both_of_diameter_lt. -/
lemma partition_disjoint {d:ℕ} {E F: Set (EuclideanSpace' d)} (S: ℕ → Box d)
    (h_sep: 0 < set_dist E F) (h_diam: ∀ n, (S n).diameter < set_dist E F) :
    Disjoint (intersecting_indices S E) (intersecting_indices S F) := by
  rw [Set.disjoint_iff]
  intro n ⟨hE, hF⟩
  -- Box n intersects both E and F
  unfold intersecting_indices at hE hF
  simp at hE hF
  -- But diameter of box n < dist(E,F)
  have h_diam_n := h_diam n
  -- This contradicts Box.not_intersects_both_of_diameter_lt
  have := Box.not_intersects_both_of_diameter_lt (S n) E F h_diam_n
  exact this ⟨hE, hF⟩

end Lebesgue_outer_measure

-- ========================================================================
-- End of Helpers
-- ========================================================================

/-- Lemma 1.2.5 (Finite additivity for separated sets).
    If E and F are separated (dist(E,F) > 0), then m*(E ∪ F) = m*(E) + m*(F).

    Proof strategy (from textbook):
    1. Direction ≤: Use subadditivity
    2. Direction ≥: Show m*(E ∪ F) ≥ m*(E) + m*(F)
       - If m*(E ∪ F) = ⊤, trivial
       - If m*(E ∪ F) < ⊤:
         * Get epsilon-close cover of E ∪ F
         * Refine cover so all boxes have diameter < dist(E,F)
         * Partition boxes into E-intersecting and F-intersecting (disjoint by geometric separation)
         * Sum volumes separately: m*(E) + m*(F) ≤ sum of refined cover ≤ m*(E ∪ F) + ε
         * Take ε → 0 to conclude
-/
theorem Lebesgue_outer_measure.union_of_separated {d:ℕ} (hd: 0 < d) {E F : Set (EuclideanSpace' d)}
    (hsep: set_dist E F > 0) :
    Lebesgue_outer_measure (E ∪ F) = Lebesgue_outer_measure E + Lebesgue_outer_measure F := by

  -- Direction 1: m*(E ∪ F) ≤ m*(E) + m*(F) [EASY - subadditivity]
  have h_le : Lebesgue_outer_measure (E ∪ F) ≤ Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
    -- Use finite subadditivity for two sets
    have : Lebesgue_outer_measure (E ∪ F) ≤ Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
      -- Convert to countable union: E ∪ F = E_0 ∪ E_1 where E_0 = E, E_1 = F
      have h_union : E ∪ F = (fun i : Fin 2 => if i = 0 then E else F) 0 ∪ (fun i : Fin 2 => if i = 0 then E else F) 1 := by
        ext x; simp
      sorry
    exact this

  -- Direction 2: m*(E ∪ F) ≥ m*(E) + m*(F) [MAIN WORK]
  have h_ge : Lebesgue_outer_measure E + Lebesgue_outer_measure F ≤ Lebesgue_outer_measure (E ∪ F) := by
    -- Case 1: If m*(E ∪ F) = ⊤, then the inequality holds trivially
    by_cases h_inf : Lebesgue_outer_measure (E ∪ F) = ⊤
    · simp [h_inf]

    -- Case 2: m*(E ∪ F) < ⊤
    · -- For any ε > 0, we'll show m*(E) + m*(F) ≤ m*(E ∪ F) + ε
      -- Taking ε → 0 gives the result

      -- Proof: Show that for all ε > 0, m*(E) + m*(F) ≤ m*(E ∪ F) + ε
      -- This implies m*(E) + m*(F) ≤ m*(E ∪ F)
      have h_eps : ∀ (ε : ℝ), 0 < ε → Lebesgue_outer_measure E + Lebesgue_outer_measure F ≤
          Lebesgue_outer_measure (E ∪ F) + (ε : EReal) := by
        intro ε hε_real

        -- Get epsilon-close cover of E ∪ F
        have ⟨S, hS_cover, hS_vol⟩ := exists_cover_close hd (E ∪ F) ε hε_real h_inf

        -- Choose r with 0 < r < dist(E,F)
        have hr : ∃ r, 0 < r ∧ r < set_dist E F := by
          use set_dist E F / 2
          constructor
          · linarith
          · linarith
        obtain ⟨r, hr_pos, hr_lt⟩ := hr

        -- Refine cover to have all diameters < r < dist(E,F)
        let S' := Lebesgue_outer_measure.refine_cover_to_diameter S r hr_pos

        -- Key properties of refined cover:
        have hS'_diam : ∀ n, (S' n).diameter < set_dist E F := by
          intro n
          calc (S' n).diameter
              < r := Lebesgue_outer_measure.refine_cover_diameter_bound S r hr_pos n
            _ < set_dist E F := hr_lt

        have hS'_cover : E ∪ F ⊆ ⋃ n, (S' n).toSet := by
          calc E ∪ F
              ⊆ ⋃ n, (S n).toSet := hS_cover
            _ ⊆ ⋃ n, (S' n).toSet := Lebesgue_outer_measure.refine_cover_preserves_union S r hr_pos

        have hS'_vol : ∑' n, (S' n).volume.toEReal ≤ ∑' n, (S n).volume.toEReal := by
          exact Lebesgue_outer_measure.refine_cover_volume_bound S r hr_pos

        -- Partition indices into E-intersecting and F-intersecting
        let I_E := Lebesgue_outer_measure.intersecting_indices S' E
        let I_F := Lebesgue_outer_measure.intersecting_indices S' F

        -- These index sets are disjoint (key geometric fact!)
        have h_disj : Disjoint I_E I_F := Lebesgue_outer_measure.partition_disjoint S' hsep hS'_diam

        -- Cover E with boxes indexed by I_E
        have hE_cover : E ⊆ ⋃ n ∈ I_E, (S' n).toSet := by
          sorry

        -- Cover F with boxes indexed by I_F
        have hF_cover : F ⊆ ⋃ n ∈ I_F, (S' n).toSet := by
          sorry

        -- By definition of outer measure:
        -- m*(E) ≤ sum over I_E and m*(F) ≤ sum over I_F
        have hE_bound : Lebesgue_outer_measure E ≤ ∑' (n : I_E), (S' n).volume.toEReal := by
          sorry

        have hF_bound : Lebesgue_outer_measure F ≤ ∑' (n : I_F), (S' n).volume.toEReal := by
          sorry

        -- Sum the bounds
        calc Lebesgue_outer_measure E + Lebesgue_outer_measure F
            ≤ (∑' (n : I_E), (S' n).volume.toEReal) + (∑' (n : I_F), (S' n).volume.toEReal) := by
                sorry  -- EReal addition
          _ ≤ ∑' n, (S' n).volume.toEReal := by
                -- Since I_E and I_F are disjoint subsets of ℕ
                sorry
          _ ≤ ∑' n, (S n).volume.toEReal := hS'_vol
          _ ≤ Lebesgue_outer_measure (E ∪ F) + (ε : EReal) := hS_vol

      -- From h_eps, conclude the inequality holds
      -- If for all ε > 0, a ≤ b + ε, then a ≤ b
      sorry

  -- Combine both directions
  exact le_antisymm h_le h_ge

example : set_dist (Ico 0 1).toSet (Icc 1 2).toSet = 0 := by sorry

/-- Exercise 1.2.4 -/
theorem dist_of_disj_compact_pos {d:ℕ} (E F: Set (EuclideanSpace' d)) (hE: IsCompact E) (hF: IsCompact F) (hdisj: E ∩ F = ∅) :
    set_dist E F > 0 := by
  sorry

/-- Lemma 1.2.6 (Outer measure of elementary sets).  Proof has not been formalized yet. -/
theorem Lebesgue_outer_measure.elementary {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsElementary E) :
    Lebesgue_outer_measure E = hE.measure := by
  sorry

/-- Cantor's theorem -/
theorem EuclideanSpace'.uncountable (d:ℕ) : Uncountable (EuclideanSpace' d) := by sorry

/-- No uncountable subadditivity-/
example {d:ℕ} : ∃ (S:Type) (E: S → Set (EuclideanSpace' d)), ¬ Lebesgue_outer_measure (⋃ i, E i) ≤ ∑' i, Lebesgue_outer_measure (E i) := by sorry

/-- Remark 1.2.8 -/
example : ∃ (E: Set (EuclideanSpace' 1)), Bornology.IsBounded E ∧
    IsOpen E ∧ ¬ JordanMeasurable E := by sorry

/-- Remark 1.2.8 -/
example : ∃ (E: Set (EuclideanSpace' 1)), Bornology.IsBounded E ∧
    IsCompact E ∧ ¬ JordanMeasurable E := by sorry

def AlmostDisjoint {d:ℕ} (B B': Box d) : Prop := interior B.toSet ∩ interior B'.toSet = ∅

theorem IsElementary.almost_disjoint {d k:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) (B: Fin k → Box d) (hEB: E = ⋃ i, (B i).toSet) (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) : hE.measure = ∑ i, |B i|ᵥ := by
  sorry

/-- Lemma 1.2.9 (Outer measure of countable unions of almost disjoint boxes).  Proof has not been formalized yet. -/
theorem Lebesgue_outer_measure.union_of_almost_disjoint {d:ℕ} {B : ℕ → Box d} (h : Pairwise (Function.onFun AlmostDisjoint B)) :
    Lebesgue_outer_measure (⋃ i, (B i).toSet) = ∑' i, Lebesgue_outer_measure (B i).toSet := by
  sorry

theorem Lebesgue_outer_measure.univ {d:ℕ} : Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) = ⊤ := by
  sorry

/-- Remark 1.2.10 -/
theorem Box.sum_volume_eq {d:ℕ} (B B': ℕ → Box d) (hdisj: Pairwise (Function.onFun AlmostDisjoint B)) (hdisj': Pairwise (Function.onFun AlmostDisjoint B)) (hcover: (⋃ n, (B n).toSet) = (⋃ n, (B' n).toSet)) :
    ∑' n, (B n).volume = ∑' n, (B' n).volume := by
  sorry

/-- Exercise 1.2.5 -/
example {d:ℕ} (E: Set (EuclideanSpace' d)) (B: ℕ → Box d) (hE: E = ⋃ n, (B n).toSet) (hdisj: Pairwise (Function.onFun AlmostDisjoint B)) : Lebesgue_outer_measure E = Jordan_inner_measure E := by
  sorry

def IsCube {d:ℕ} (B: Box d) : Prop := ∃ r, ∀ i, |B.side i|ₗ = r

noncomputable def DyadicCube {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : Box d := { side := fun i ↦ Icc (a i/2^n) ((a i + 1)/2^n) }

lemma DyadicCube.isCube {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : IsCube (DyadicCube n a) := by
  sorry

def Box.IsDyadicAtScale {d:ℕ} (B: Box d) (n:ℤ) : Prop := ∃ a: Fin d → ℤ, B = DyadicCube n a

def Box.IsDyadic {d:ℕ} (B: Box d) : Prop := ∃ n:ℕ, B.IsDyadicAtScale n

/-- Lemma 1.2.11.  Proof has not been formalized yet. -/
theorem IsOpen.eq_union_boxes {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsOpen E) : ∃ B: ℕ → Box d, (E = ⋃ n, (B n).toSet) ∧ (∀ n, (B n).IsDyadic) ∧ Pairwise (Function.onFun AlmostDisjoint B) := by
  sorry

theorem Lebesgue_outer_measure.of_open {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsOpen E) : Lebesgue_outer_measure E = Jordan_inner_measure E := by
  sorry

/-- Lemma 1.2.12 (Outer regularity).  Proof has not been formalized yet. -/
theorem Lebesgue_outer_measure.eq {d:ℕ} (E: Set (EuclideanSpace' d)) : Lebesgue_outer_measure E = sInf { M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by
  sorry

/-- Exercise 1.2.6 -/
example : ∃ (d:ℕ) (E: Set (EuclideanSpace' d)), Lebesgue_outer_measure E ≠ sSup { M | ∃ U, U ⊆ E ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by sorry
