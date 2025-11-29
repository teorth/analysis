import Analysis.MeasureTheory.Section_1_2
import Analysis.Misc.«Real-EReal-ENNReal»
import Analysis.Misc.Combinatorics

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

namespace BoundedInterval
/-- Extract the left and right endpoints of a BoundedInterval.
    Returns (a, b) where a is the left endpoint and b is the right endpoint. -/
def endpoints (I : BoundedInterval) : ℝ × ℝ :=
  match I with
  | Ioo a b => (a, b)
  | Icc a b => (a, b)
  | Ioc a b => (a, b)
  | Ico a b => (a, b)

/-- Compute the midpoint of a BoundedInterval. -/
noncomputable def midpoint (I : BoundedInterval) : ℝ :=
  let (a, b) := I.endpoints
  (a + b) / 2

/-- Bisect a BoundedInterval into left and right halves using closed intervals.
    Left half: [a, m], Right half: [m, b], where m is the midpoint.
    Using closed intervals ensures coverage (union equals original) while
    maintaining measure-theoretic properties (overlap has measure zero). -/
noncomputable def bisect (I : BoundedInterval) : BoundedInterval × BoundedInterval :=
  let (a, b) := I.endpoints
  let m := I.midpoint
  (Icc a m, Icc m b)


/-- The left half of bisection has half the original length -/
lemma bisect_fst_length (I : BoundedInterval) :
    |(I.bisect.fst)|ₗ = |I|ₗ / 2 := by
  unfold bisect midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    -- Goal: max ((a + b) / 2 - a) 0 = max (b - a) 0 / 2
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]

/-- The right half of bisection has half the original length -/
lemma bisect_snd_length (I : BoundedInterval) :
    |(I.bisect.snd)|ₗ = |I|ₗ / 2 := by
  unfold bisect midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    -- Goal: max (b - (a + b) / 2) 0 = max (b - a) 0 / 2
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]

/-- Bisecting preserves total length -/
lemma bisect_length_sum (I : BoundedInterval) :
    |(I.bisect.fst)|ₗ + |(I.bisect.snd)|ₗ = |I|ₗ := by
  rw [bisect_fst_length, bisect_snd_length]
  ring

/-- The left endpoint of bisect.fst is I.a -/
@[simp]
lemma bisect_fst_a (I : BoundedInterval) : (I.bisect.fst).a = I.a := by
  unfold bisect endpoints
  cases I <;> simp [BoundedInterval.a]

/-- The left endpoint of bisect.snd is I.midpoint -/
@[simp]
lemma bisect_snd_a (I : BoundedInterval) : (I.bisect.snd).a = I.midpoint := by
  unfold bisect endpoints
  cases I <;> simp [BoundedInterval.a, midpoint]

/-- The midpoint equals a + length/2 when a ≤ b (non-degenerate interval) -/
lemma midpoint_eq_a_add_half_length (I : BoundedInterval) (h : I.a ≤ I.b) :
    I.midpoint = I.a + |I|ₗ / 2 := by
  unfold midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring


/-- The midpoint is in the first half of bisection (as the right endpoint of Icc) -/
lemma midpoint_mem_bisect_fst (I : BoundedInterval) (h : I.toSet.Nonempty) :
    I.midpoint ∈ (I.bisect.fst).toSet := by
  obtain ⟨x, hx⟩ := h
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩

/-- The midpoint is in the second half of bisection (as the left endpoint of Icc) -/
lemma midpoint_mem_bisect_snd (I : BoundedInterval) (h : I.toSet.Nonempty) :
    I.midpoint ∈ (I.bisect.snd).toSet := by
  obtain ⟨x, hx⟩ := h
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩


/-- A point is in I.bisect.snd iff it's in I.toSet and at or above the midpoint -/
lemma mem_bisect_snd_iff (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) :
    x ∈ (I.bisect.snd).toSet ↔ x ≥ I.midpoint := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩

/-- A point is in I.bisect.fst iff it's in I.toSet and below the midpoint -/
lemma mem_bisect_fst_iff (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) :
    x ∈ (I.bisect.fst).toSet ↔ x ≤ I.midpoint := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩

/-- If two intervals have equal bisect.fst, then their endpoints match -/
lemma bisect_fst_eq_endpoints {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.fst) : I₁.a = I₂.a ∧ I₁.b = I₂.b := by
  -- bisect.fst = Icc I.a I.midpoint, so (bisect.fst).a = I.a
  have ha' : (I₁.bisect.fst).a = (I₂.bisect.fst).a := congrArg (·.a) h
  have hm' : (I₁.bisect.fst).b = (I₂.bisect.fst).b := congrArg (·.b) h
  simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at ha' hm'
  constructor
  · cases I₁ <;> cases I₂ <;> simp_all
  · cases I₁ <;> cases I₂ <;> simp only [BoundedInterval.b] at ha' hm' ⊢ <;> linarith

/-- If two intervals have equal bisect.snd, then their endpoints match -/
lemma bisect_snd_eq_endpoints {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.snd = I₂.bisect.snd) : I₁.a = I₂.a ∧ I₁.b = I₂.b := by
  -- bisect.snd = Icc midpoint b, so (bisect.snd).a = midpoint and (bisect.snd).b = b
  have hm' : (I₁.bisect.snd).a = (I₂.bisect.snd).a := congrArg (·.a) h
  have hb' : (I₁.bisect.snd).b = (I₂.bisect.snd).b := congrArg (·.b) h
  -- The .b of bisect.snd is just I.b, and .a is (I.a + I.b)/2
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  all_goals simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at hm' hb' ⊢
  -- Now hm' : (a₁ + b₁)/2 = (a₂ + b₂)/2 and hb' : b₁ = b₂
  all_goals constructor <;> linarith


/-- Cross-case: if bisect.fst = bisect.snd, the intervals have overlapping midpoint and endpoint -/
lemma bisect_fst_eq_snd_shift {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.snd) : I₁.a = (I₂.a + I₂.b) / 2 := by
  -- (bisect.fst).a = I.a, (bisect.snd).a = I.midpoint = (I.a + I.b)/2
  have ha' : (I₁.bisect.fst).a = (I₂.bisect.snd).a := congrArg (·.a) h
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  all_goals simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at ha' ⊢
  all_goals linarith

end BoundedInterval

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


/-- For any nonempty interval and target value less than the length,
    we can find two points in the interval with separation exceeding the target.
    This is the key density fact: achievable differences are dense in [0, length]. -/
lemma BoundedInterval.exists_points_with_diff {I : BoundedInterval}
    (h_nonempty : I.toSet.Nonempty) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht : t < |I|ₗ) :
    ∃ x ∈ I.toSet, ∃ y ∈ I.toSet, t < |x - y| := by
  -- Since t < |I|ₗ = max (b - a) 0 and t ≥ 0, we have b - a > t ≥ 0
  have h_len_pos : 0 < |I|ₗ := lt_of_le_of_lt ht_nonneg ht
  cases I with
  | Icc a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Closed: use endpoints a and b
    refine ⟨a, Set.left_mem_Icc.mpr (le_of_lt h_ab), b, Set.right_mem_Icc.mpr (le_of_lt h_ab), ?_⟩
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < b - a)]
    linarith
  | Ioo a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Open: use points close to endpoints
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a + δ / 2 ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hy_mem : b - δ / 2 ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    refine ⟨a + δ / 2, hx_mem, b - δ / 2, hy_mem, ?_⟩
    have h_diff : (b - δ / 2) - (a + δ / 2) = (b - a) - δ := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < (b - δ / 2) - (a + δ / 2)), h_diff]
    linarith
  | Ioc a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Left open, right closed: use point close to a and b
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a + δ / 2 ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩
    have hy_mem : b ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨h_ab, le_refl b⟩
    refine ⟨a + δ / 2, hx_mem, b, hy_mem, ?_⟩
    have h_diff : b - (a + δ / 2) = (b - a) - δ / 2 := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < b - (a + δ / 2)), h_diff]
    linarith
  | Ico a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Left closed, right open: use a and point close to b
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a ∈ Set.Ico a b := Set.mem_Ico.mpr ⟨le_refl a, h_ab⟩
    have hy_mem : b - δ / 2 ∈ Set.Ico a b := Set.mem_Ico.mpr ⟨by linarith, by linarith⟩
    refine ⟨a, hx_mem, b - δ / 2, hy_mem, ?_⟩
    have h_diff : (b - δ / 2) - a = (b - a) - δ / 2 := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < (b - δ / 2) - a), h_diff]
    linarith

/-- The diameter of a nonempty box equals the diagonal length √(∑ |side i|ₗ²).
    This is the key fact: the supremum of pairwise distances equals the diagonal.
    For closed intervals, the diagonal is achieved at corners.
    For open intervals, the diagonal is the limit (supremum) of achievable distances. -/
lemma diameter_eq_sqrt_sum_sq {d:ℕ} (B: Box d) (h: B.toSet.Nonempty) :
    B.diameter = √(∑ i, |B.side i|ₗ^2) := by
  unfold diameter
  -- Use csSup_eq_of_forall_le_of_forall_lt_exists_gt:
  -- if s.Nonempty ∧ (∀ a ∈ s, a ≤ b) ∧ (∀ c < b, ∃ a ∈ s, c < a), then sSup s = b
  let s := { r | ∃ x ∈ B.toSet, ∃ y ∈ B.toSet, r = √(∑ i, (x i - y i)^2) }
  let b := √(∑ i, |B.side i|ₗ^2)
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · -- s is nonempty
    obtain ⟨x, hx⟩ := h
    exact ⟨√(∑ i, (x i - x i)^2), x, hx, x, hx, rfl⟩
  · -- ∀ a ∈ s, a ≤ b (upper bound)
    intro r ⟨x, hx, y, hy, hr⟩
    rw [hr]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    -- |x i - y i|² ≤ |B.side i|ₗ²
    have hx_i : x i ∈ (B.side i).toSet := hx i (Set.mem_univ i)
    have hy_i : y i ∈ (B.side i).toSet := hy i (Set.mem_univ i)
    have coord_bound : |x i - y i| ≤ |B.side i|ₗ := by
      cases h_side : B.side i <;>
          simp [BoundedInterval.toSet, h_side] at hx_i hy_i <;>
          simp [BoundedInterval.length] <;>
          (left; rw [abs_sub_le_iff]; constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2])
    calc (x i - y i)^2 = |x i - y i|^2 := by rw [sq_abs]
      _ ≤ |B.side i|ₗ^2 := by
          apply sq_le_sq' <;> [linarith [abs_nonneg (x i - y i), coord_bound]; exact coord_bound]
  · -- ∀ c < b, ∃ a ∈ s, c < a (density: can get arbitrarily close to b)
    intro c hc
    -- Need to find x, y ∈ B with √(∑ (x i - y i)²) > c
    -- Strategy: for each coordinate, pick points near opposite ends of the interval
    -- The resulting distance will be close to √(∑ side²)
    -- Since c < √(∑ side²), we can find ε > 0 such that c < √(∑ side²) - ε
    -- Then pick x, y such that |x i - y i| ≥ |side i| - δ for small enough δ
    -- This gives √(∑ (x i - y i)²) ≥ √(∑ (side - δ)²) > c for small δ
    --
    -- For the formal proof, we use that intervals are nonempty (from h_nonempty)
    -- and that we can pick points with controlled distances from endpoints.
    by_cases h_zero : (∑ i, |B.side i|ₗ^2) = 0
    · -- All sides have length 0, so b = 0
      -- c < 0 is impossible since distances are ≥ 0
      simp only [h_zero, Real.sqrt_zero] at hc
      -- c < 0, but any distance is ≥ 0, so we need c < some distance ≥ 0
      -- Since c < 0, we have c < 0 ≤ any distance
      obtain ⟨x, hx⟩ := h
      use 0
      constructor
      · exact ⟨x, hx, x, hx, by simp⟩
      · linarith
    · -- Some side has positive length
      -- Use the characterization: √(∑ side²) > c means ∑ side² > c²
      have h_pos : 0 < ∑ i, |B.side i|ₗ^2 := by
        apply lt_of_le_of_ne
        · apply Finset.sum_nonneg; intro i _; exact sq_nonneg _
        · exact Ne.symm h_zero
      -- Get ε such that c + ε < √(∑ side²)
      have h_c_lt : c < √(∑ i, |B.side i|ₗ^2) := hc
      -- Since c < √(∑ side²), we have c² < ∑ side² (for c ≥ 0) or c < 0
      by_cases hc_nonneg : 0 ≤ c
      · -- c ≥ 0 case: we need to construct points with large distance
        -- Strategy: use exists_points_with_diff for positive-length coordinates
        -- Each interval is nonempty (from h: B.toSet.Nonempty)
        have h_interval_nonempty : ∀ i, (B.side i).toSet.Nonempty := by
          intro i; obtain ⟨x, hx⟩ := h
          exact ⟨x i, hx i (Set.mem_univ i)⟩
        -- We'll construct points coordinate-wise with ≥ for all and > for positive-length
        let ratio := c / √(∑ i, |B.side i|ₗ^2)
        have h_ratio_lt_one : ratio < 1 := by
          show c / √(∑ i, |B.side i|ₗ^2) < 1
          rw [div_lt_one (Real.sqrt_pos.mpr h_pos)]
          exact h_c_lt
        have h_ratio_nonneg : 0 ≤ ratio := by
          show 0 ≤ c / √(∑ i, |B.side i|ₗ^2)
          exact div_nonneg hc_nonneg (Real.sqrt_nonneg _)
        -- For positive-length coordinates: get strict inequality
        have h_exists_points : ∀ i, ∃ xi ∈ (B.side i).toSet, ∃ yi ∈ (B.side i).toSet,
            |B.side i|ₗ * ratio ≤ |xi - yi| ∧
            (0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |xi - yi|) := by
          intro i
          by_cases h_len_zero : |B.side i|ₗ = 0
          · -- Zero-length interval: xi = yi gives 0 ≤ 0
            obtain ⟨xi, hxi⟩ := h_interval_nonempty i
            refine ⟨xi, hxi, xi, hxi, ?_, ?_⟩
            · simp [h_len_zero]
            · simp [h_len_zero]
          · -- Positive-length interval: use exists_points_with_diff
            have h_len_pos : 0 < |B.side i|ₗ := by
              apply lt_of_le_of_ne; simp [BoundedInterval.length]; exact Ne.symm h_len_zero
            have h_target_lt : |B.side i|ₗ * ratio < |B.side i|ₗ := by
              calc |B.side i|ₗ * ratio < |B.side i|ₗ * 1 := by
                    apply mul_lt_mul_of_pos_left h_ratio_lt_one h_len_pos
                _ = |B.side i|ₗ := mul_one _
            obtain ⟨xi, hxi, yi, hyi, hlt⟩ := BoundedInterval.exists_points_with_diff
              (h_interval_nonempty i) (mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg)
              h_target_lt
            exact ⟨xi, hxi, yi, hyi, le_of_lt hlt, fun _ => hlt⟩
        -- Use Classical.choose to extract the points
        classical
        let x : Fin d → ℝ := fun i => (h_exists_points i).choose
        let y : Fin d → ℝ := fun i => (h_exists_points i).choose_spec.2.choose
        have hx_mem : ∀ i, x i ∈ (B.side i).toSet := fun i => (h_exists_points i).choose_spec.1
        have hy_mem : ∀ i, y i ∈ (B.side i).toSet := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.1
        have h_diff_le : ∀ i, |B.side i|ₗ * ratio ≤ |x i - y i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.1
        have h_diff_lt : ∀ i, 0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |x i - y i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.2
        -- x, y ∈ B.toSet
        have hx_box : x ∈ B.toSet := fun i _ => hx_mem i
        have hy_box : y ∈ B.toSet := fun i _ => hy_mem i
        -- The distance √(∑ (x_i - y_i)²) > c
        use √(∑ i, (x i - y i)^2)
        constructor
        · exact ⟨x, hx_box, y, hy_box, rfl⟩
        · -- Need: c < √(∑ (x_i - y_i)²)
          rw [← Real.sqrt_sq hc_nonneg]
          apply Real.sqrt_lt_sqrt (sq_nonneg c)
          -- Need: c² < ∑ (x_i - y_i)²
          -- c² = ∑ (side * ratio)² and we have ≤ for all, < for at least one positive side
          have h_target : c^2 = ∑ i, (|B.side i|ₗ * ratio)^2 := by
            have h_sum_nonneg : 0 ≤ ∑ i : Fin d, |B.side i|ₗ^2 :=
              Finset.sum_nonneg (fun i _ => sq_nonneg (|B.side i|ₗ))
            have h_sqrt_ne : √(∑ i, |B.side i|ₗ^2) ≠ 0 := Real.sqrt_ne_zero'.mpr h_pos
            calc c^2 = (√(∑ i, |B.side i|ₗ^2) * ratio)^2 := by
                  show c^2 = (√(∑ i, |B.side i|ₗ^2) * (c / √(∑ i, |B.side i|ₗ^2)))^2
                  field_simp
              _ = (∑ i, |B.side i|ₗ^2) * ratio^2 := by
                  rw [mul_pow, Real.sq_sqrt h_sum_nonneg]
              _ = ∑ i, |B.side i|ₗ^2 * ratio^2 := Finset.sum_mul _ _ _
              _ = ∑ i, (|B.side i|ₗ * ratio)^2 := by congr 1; ext i; ring
          rw [h_target]
          -- Since ∑ side² > 0, at least one side is positive
          have h_exists_pos : ∃ j, 0 < |B.side j|ₗ := by
            by_contra h_all_zero; push_neg at h_all_zero
            have h_sum_zero : (∑ i, |B.side i|ₗ^2) = 0 := by
              apply Finset.sum_eq_zero; intro i _
              have : |B.side i|ₗ ≤ 0 := h_all_zero i
              have h_nonneg : 0 ≤ |B.side i|ₗ := by simp [BoundedInterval.length]
              have : |B.side i|ₗ = 0 := le_antisymm this h_nonneg
              simp [this]
            exact h_zero h_sum_zero
          obtain ⟨j, hj_pos⟩ := h_exists_pos
          apply Finset.sum_lt_sum
          · intro i _
            have h_sq : (|B.side i|ₗ * ratio)^2 ≤ |x i - y i|^2 := by
              apply sq_le_sq' _ (h_diff_le i)
              calc -(|x i - y i|) ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
                _ ≤ |B.side i|ₗ * ratio := mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg
            calc (|B.side i|ₗ * ratio)^2 ≤ |x i - y i|^2 := h_sq
              _ = (x i - y i)^2 := by rw [sq_abs]
          · use j, Finset.mem_univ j
            have h_sq_lt : (|B.side j|ₗ * ratio)^2 < |x j - y j|^2 := by
              -- From h_diff_lt we know side * ratio < |x j - y j|, so |x j - y j| > 0
              have h_diff_pos : 0 < |x j - y j| :=
                lt_of_le_of_lt (mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg)
                  (h_diff_lt j hj_pos)
              apply sq_lt_sq' _ (h_diff_lt j hj_pos)
              calc -(|x j - y j|) < 0 := neg_neg_of_pos h_diff_pos
                _ ≤ |B.side j|ₗ * ratio := mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg
            calc (|B.side j|ₗ * ratio)^2 < |x j - y j|^2 := h_sq_lt
              _ = (x j - y j)^2 := by rw [sq_abs]
      · -- c < 0 case: any distance ≥ 0 > c
        push_neg at hc_nonneg
        obtain ⟨x, hx⟩ := h
        use 0
        constructor
        · exact ⟨x, hx, x, hx, by simp⟩
        · linarith

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

open Classical in
/-- Decidable equality for boxes, needed for Finset operations -/
noncomputable instance {d:ℕ} : DecidableEq (Box d) := instDecidableEqOfLawfulBEq

/-- Subdivide a box by bisecting each coordinate axis, producing 2^d sub-boxes.
    Each sub-box is formed by taking one half-interval from each coordinate.
    We use Finset.univ (all possible d-bit patterns) to enumerate all 2^d combinations. -/
noncomputable def subdivide {d:ℕ} (B: Box d) : Finset (Box d) :=
  -- For each choice ∈ Fin d → Bool (which half to take for each coordinate),
  -- construct a sub-box by taking the left half (if false) or right half (if true)
  Finset.univ.image fun (choice : Fin d → Bool) =>
    { side := fun i =>
        let (left, right) := (B.side i).bisect
        if choice i then right else left }

/-- The volume of a subdivided box equals the sum of its sub-box volumes -/
lemma volume_subdivide {d:ℕ} (B: Box d) :
    ∑ B' ∈ B.subdivide, |B'|ᵥ = |B|ᵥ := by
  unfold subdivide Box.volume
  -- Establish that each coordinate's length splits into two halves
  have h_sum : ∀ i, |(B.side i)|ₗ = |(B.side i).bisect.fst|ₗ + |(B.side i).bisect.snd|ₗ := by
    intro i; exact (BoundedInterval.bisect_length_sum (B.side i)).symm
  -- Rewrite RHS using the sum identity
  have h_rhs : ∏ i, |(B.side i)|ₗ = ∏ i, (|(B.side i).bisect.fst|ₗ + |(B.side i).bisect.snd|ₗ) := by
    apply Finset.prod_congr rfl; intro i _; exact h_sum i
  rw [h_rhs, Fin.prod_add_eq_sum_prod_choice d _ _]
  -- The mapping from choice to box
  let g : (Fin d → Bool) → Box d := fun c =>
    { side := fun i => let (l, r) := (B.side i).bisect; if c i then r else l }
  -- Key: volume of g c equals the product of half-lengths
  have h_vol_eq : ∀ c : Fin d → Bool, |g c|ᵥ =
      ∏ i, (if c i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ) := by
    intro c; unfold Box.volume; apply Finset.prod_congr rfl; intro i _
    simp only [g]; split_ifs <;> rfl
  -- Two choices give same product when they map to same box
  have h_prod_eq : ∀ c₁ c₂ : Fin d → Bool, g c₁ = g c₂ →
      (∏ i, (if c₁ i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)) =
      (∏ i, (if c₂ i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)) := by
    intro c₁ c₂ heq
    apply Finset.prod_congr rfl; intro i _
    have hside : (g c₁).side i = (g c₂).side i := congrArg (·.side i) heq
    simp only [g] at hside
    cases hc₁ : c₁ i <;> cases hc₂ : c₂ i <;> simp only [hc₁, hc₂, ↓reduceIte, Bool.false_eq_true] at hside ⊢
    -- true/false case: hside : bisect.snd = bisect.fst
    · rw [congrArg BoundedInterval.length hside]
    -- false/true case: hside : bisect.fst = bisect.snd
    · rw [congrArg BoundedInterval.length hside]
  -- Use sum_image' which handles non-injective maps
  let h_func : (Fin d → Bool) → ℝ := fun c =>
    ∏ i, (if c i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)
  have h_fiber : ∀ c ∈ Finset.univ, |g c|ᵥ = ∑ j ∈ Finset.univ with g j = g c, h_func j := by
    intro c _
    rw [h_vol_eq c]
    have h_fib_eq : ∀ j ∈ Finset.univ, g j = g c → h_func j = h_func c := by
      intro j _ hgj; exact h_prod_eq j c hgj
    -- Goal: h_func c = ∑ j with g j = g c, h_func j
    -- All elements in fiber have value h_func c, so sum = card * h_func c
    conv_rhs => rw [show ∑ j ∈ Finset.univ with g j = g c, h_func j =
        ∑ j ∈ Finset.univ.filter (fun j => g j = g c), h_func j from rfl]
    rw [Finset.sum_eq_card_nsmul (fun x hx => by
      rw [Finset.mem_filter] at hx; exact h_fib_eq x hx.1 hx.2)]
    rw [nsmul_eq_mul]
    -- Need: h_func c = card * h_func c. Holds when card = 1 OR h_func c = 0.
    by_cases h_card : (Finset.univ.filter (fun j => g j = g c)).card = 1
    · simp only [h_card, Nat.cast_one, one_mul]; rfl
    · -- Card ≠ 1, and card ≥ 1 (since c is in fiber), so card > 1
      have h_card_pos : 0 < (Finset.univ.filter (fun j => g j = g c)).card := by
        apply Finset.card_pos.mpr; use c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h_card_gt : 1 < (Finset.univ.filter (fun j => g j = g c)).card := by omega
      obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.mp h_card_gt
      rw [Finset.mem_filter] at hc₁ hc₂
      -- c₁ and c₂ differ at some coordinate
      have ⟨i, hi_ne⟩ : ∃ i, c₁ i ≠ c₂ i := by
        by_contra h; push_neg at h; exact hne (funext h)
      -- At that coordinate, g c₁ = g c₂ implies bisect.fst = bisect.snd
      have hside : (g c₁).side i = (g c₂).side i := congrArg (·.side i) (hc₁.2.trans hc₂.2.symm)
      simp only [g] at hside
      -- Extract bisect equality from hside by case analysis on c₁ i and c₂ i
      have h_bisect_eq : (B.side i).bisect.fst = (B.side i).bisect.snd := by
        cases hc₁i : c₁ i <;> cases hc₂i : c₂ i <;>
        simp only [hc₁i, hc₂i, Bool.false_eq_true, ↓reduceIte] at hside hi_ne
        · exact (hi_ne rfl).elim  -- false/false case: contradiction
        · exact hside             -- false/true case: hside : fst = snd
        · exact hside.symm        -- true/false case: hside : snd = fst
        · exact (hi_ne rfl).elim  -- true/true case: contradiction
      -- When fst = snd, the interval is degenerate (point), so length = 0
      have h_len_zero : |(B.side i).bisect.snd|ₗ = 0 := by
        rw [← h_bisect_eq]
        -- bisect.fst = bisect.snd means Icc a m = Icc m b, so a = m = b
        unfold BoundedInterval.bisect BoundedInterval.midpoint BoundedInterval.endpoints at h_bisect_eq
        cases hI : B.side i with
        | Ioo a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Icc a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Ioc a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Ico a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
      -- h_func c has a zero factor at coordinate i, so the product is 0
      have h_len_fst_zero : |(B.side i).bisect.fst|ₗ = 0 := by rw [h_bisect_eq]; exact h_len_zero
      have h_prod_zero : h_func c = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        cases hci : c i
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact h_len_fst_zero
        · simp only [↓reduceIte]; exact h_len_zero
      simp only [h_prod_zero, mul_zero]
      -- Goal: h_func c = 0, which is exactly h_prod_zero
      exact h_prod_zero
  rw [Finset.sum_image' h_func h_fiber]

/-- Each sub-box of a subdivision has diameter at most the original diameter divided by √2.
    This follows because each side is halved, reducing the diagonal by a factor related to √2.
    Note: The hypothesis that B is nonempty is necessary because bisection always creates closed
    intervals, which can turn degenerate open intervals (Ioo a a) into nonempty singletons. -/
lemma subdivide_diameter_bound {d:ℕ} (B: Box d) (hB : B.toSet.Nonempty) :
    ∀ B' ∈ B.subdivide, B'.diameter ≤ B.diameter / Real.sqrt 2 := by
  intro B' hB'
  -- Extract the choice function that defines B'
  unfold subdivide at hB'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨choice, rfl⟩ := hB'
  -- Abbreviate the sub-box for readability
  set B' : Box d := { side := fun i => if choice i then (B.side i).bisect.snd
      else (B.side i).bisect.fst } with hB'_def
  -- Key: B'.diameter ≤ B.diameter / 2 ≤ B.diameter / √2
  -- Since √2 < 2, we have B.diameter / 2 ≤ B.diameter / √2
  suffices h : B'.diameter ≤ B.diameter / 2 by
    calc B'.diameter
        ≤ B.diameter / 2 := h
      _ ≤ B.diameter / √2 := by
          apply div_le_div_of_nonneg_left (diameter_nonneg B)
          · exact Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
          · calc √2 ≤ √4 := Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 4)
              _ = 2 := by norm_num
  -- Now prove B'.diameter ≤ B.diameter / 2
  -- Key: |B'.side i|ₗ = |B.side i|ₗ / 2 for all i, so diagonal is halved
  -- From nonemptiness of B, each side interval is nonempty
  have h_side_nonempty : ∀ i, (B.side i).toSet.Nonempty := by
    intro i; obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i (Set.mem_univ i)⟩
  -- First show B' is nonempty (the midpoint of each side is in both halves)
  have hB'_nonempty : B'.toSet.Nonempty := by
    use fun i => (B.side i).midpoint
    intro i _
    simp only [hB'_def]
    split_ifs with h
    · exact BoundedInterval.midpoint_mem_bisect_snd (B.side i) (h_side_nonempty i)
    · exact BoundedInterval.midpoint_mem_bisect_fst (B.side i) (h_side_nonempty i)
  -- Each side of B' has half the length of B's side
  have h_side_half : ∀ i, |B'.side i|ₗ = |B.side i|ₗ / 2 := by
    intro i
    simp only [hB'_def]
    split_ifs with h
    · exact BoundedInterval.bisect_snd_length _
    · exact BoundedInterval.bisect_fst_length _
  -- Use diameter_eq_sqrt_sum_sq for both boxes
  rw [diameter_eq_sqrt_sum_sq B' hB'_nonempty, diameter_eq_sqrt_sum_sq B hB]
  -- √(∑ (side/2)²) = √(∑ side²) / 2
  have h_sum_eq : ∑ i, |B'.side i|ₗ^2 = (∑ i, |B.side i|ₗ^2) / 4 := by
    simp_rw [h_side_half, div_pow]
    rw [Finset.sum_div]
    ring_nf
  rw [h_sum_eq, Real.sqrt_div (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  norm_num

/-- Subdivide a box k times, producing a Finset of boxes.
    After k iterations, each original box becomes up to 2^(d*k) sub-boxes. -/
noncomputable def subdivide_iter {d:ℕ} (B: Box d) : ℕ → Finset (Box d)
  | 0 => {B}
  | k+1 => (subdivide_iter B k).biUnion Box.subdivide

lemma subdivide_iter_zero {d:ℕ} (B: Box d) : subdivide_iter B 0 = {B} := rfl

lemma subdivide_iter_succ {d:ℕ} (B: Box d) (k: ℕ) :
    subdivide_iter B (k+1) = (subdivide_iter B k).biUnion Box.subdivide := rfl

/-- All sides in subdivide (single level) are Icc intervals -/
lemma subdivide_side_is_Icc {d:ℕ} (B: Box d) (B' : Box d) (hB' : B' ∈ B.subdivide) (i : Fin d) :
    ∃ a b, B'.side i = Icc a b := by
  simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨c, rfl⟩ := hB'
  -- B' = { side := fun j => if c j then ... else ... }
  -- B'.side i = if c i then (B.side i).bisect.snd else (B.side i).bisect.fst
  simp only  -- This introduces the if-then-else in the goal
  split_ifs with hc
  · -- snd case: (B.side i).bisect.snd is Icc
    unfold BoundedInterval.bisect BoundedInterval.endpoints BoundedInterval.midpoint
    cases B.side i <;> exact ⟨_, _, rfl⟩
  · -- fst case: (B.side i).bisect.fst is Icc
    unfold BoundedInterval.bisect BoundedInterval.endpoints BoundedInterval.midpoint
    cases B.side i <;> exact ⟨_, _, rfl⟩

/-- All sides in subdivide_iter for k ≥ 1 are Icc intervals -/
lemma subdivide_iter_side_is_Icc {d:ℕ} (B: Box d) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B (k+1)) (i : Fin d) :
    ∃ a b, B'.side i = Icc a b := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_biUnion, Finset.mem_singleton] at hB'
    obtain ⟨B'', rfl, hB'_sub⟩ := hB'
    exact subdivide_side_is_Icc B'' B' hB'_sub i
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    exact subdivide_side_is_Icc B'' B' hB'_sub i

/-- All boxes in subdivide_iter have the same side lengths at each coordinate -/
lemma subdivide_iter_side_length {d:ℕ} (B : Box d) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B k) (i : Fin d) :
    |B'.side i|ₗ = |B.side i|ₗ / 2^k := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton] at hB'
    simp [hB']
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    have h1 := ih B'' hB''
    simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'_sub
    obtain ⟨c, rfl⟩ := hB'_sub
    simp only
    split_ifs with hc
    · rw [BoundedInterval.bisect_snd_length, h1]; ring
    · rw [BoundedInterval.bisect_fst_length, h1]; ring

/-- A nonempty box remains nonempty after subdivision -/
lemma subdivide_one_step_nonempty {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) :
    ∀ B' ∈ B.subdivide, B'.toSet.Nonempty := by
  intro B' hB'
  unfold subdivide at hB'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨choice, rfl⟩ := hB'
  -- The midpoint of B is in all sub-boxes
  use fun i => (B.side i).midpoint
  intro i _
  have h_side_nonempty : (B.side i).toSet.Nonempty := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i (Set.mem_univ i)⟩
  simp only
  split_ifs with h
  · exact BoundedInterval.midpoint_mem_bisect_snd (B.side i) h_side_nonempty
  · exact BoundedInterval.midpoint_mem_bisect_fst (B.side i) h_side_nonempty

/-- A nonempty box remains nonempty after k iterations of subdivision -/
lemma subdivide_iter_nonempty {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (k: ℕ) :
    ∀ B' ∈ subdivide_iter B k, B'.toSet.Nonempty := by
  induction k with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton]
    intro B' hB'; rw [hB']; exact hB
  | succ k ih =>
    intro B' hB'
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB''_mem, hB'_sub⟩ := hB'
    exact subdivide_one_step_nonempty B'' (ih B'' hB''_mem) B' hB'_sub

/-- Grid alignment: sides in subdivide_iter start at grid positions.
    Requires nonempty box to ensure sides have a ≤ b (backwards intervals break the formula). -/
lemma subdivide_iter_side_grid {d:ℕ} (B : Box d) (hB : B.toSet.Nonempty) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B k) (i : Fin d) :
    ∃ j : ℕ, j < 2^k ∧ (B'.side i).a = (B.side i).a + j * (|B.side i|ₗ / 2^k) := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton] at hB'
    use 0
    simp [hB']
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    obtain ⟨j'', hj''_bound, hj''_eq⟩ := ih B'' hB''
    simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'_sub
    obtain ⟨c, rfl⟩ := hB'_sub
    have h_len := subdivide_iter_side_length B k B'' hB'' i
    simp only
    split_ifs with hc
    · -- snd case: start at midpoint of B''
      use 2 * j'' + 1
      constructor
      · omega
      · -- (bisect.snd).a = midpoint = B''.a + |B''|ₗ/2
        rw [BoundedInterval.bisect_snd_a]
        have h_B''_len : |B''.side i|ₗ = |B.side i|ₗ / 2 ^ k := h_len
        by_cases h_nondeg : (B''.side i).a ≤ (B''.side i).b
        · -- Non-degenerate: use midpoint_eq_a_add_half_length
          rw [BoundedInterval.midpoint_eq_a_add_half_length _ h_nondeg, hj''_eq, h_B''_len]
          have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
          rw [h2k]
          have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
          field_simp [h2k_ne]
          ring
        · -- Degenerate case: impossible for nonempty boxes (all sides have a ≤ b)
          -- B'' is nonempty since B is nonempty
          have hB''_nonempty : B''.toSet.Nonempty := subdivide_iter_nonempty B hB k B'' hB''
          -- Therefore (B''.side i) is nonempty
          have h_side_nonempty : (B''.side i).toSet.Nonempty :=
            Box.side_nonempty_of_nonempty B'' hB''_nonempty i
          -- Nonempty intervals have a ≤ b
          have h_order : (B''.side i).a ≤ (B''.side i).b :=
            BoundedInterval.nonempty_implies_le _ h_side_nonempty
          -- Contradiction with ¬h_nondeg
          exact absurd h_order h_nondeg
    · -- fst case: start at B''.a (left endpoint preserved)
      use 2 * j''
      constructor
      · omega
      · rw [BoundedInterval.bisect_fst_a, hj''_eq]
        have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [h2k]
        have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
        field_simp [h2k_ne]
        ring

/-- Volume is preserved through iterative subdivision -/
lemma volume_subdivide_iter {d:ℕ} (B: Box d) (hB : B.toSet.Nonempty) (k: ℕ) :
    ∑ B' ∈ subdivide_iter B k, |B'|ᵥ = |B|ᵥ := by
  induction k with
  | zero => simp [subdivide_iter]
  | succ k ih =>
    simp only [subdivide_iter_succ]
    rw [Finset.sum_biUnion]
    · -- Each inner sum ∑ i ∈ x.subdivide, |i|ᵥ = |x|ᵥ by volume_subdivide
      calc ∑ x ∈ subdivide_iter B k, ∑ i ∈ x.subdivide, |i|ᵥ
          = ∑ x ∈ subdivide_iter B k, |x|ᵥ := by
            apply Finset.sum_congr rfl
            intro B' _
            exact volume_subdivide B'
        _ = |B|ᵥ := ih
    · -- Pairwise disjointness of subdivisions from different parent boxes
      intro B₁ hB₁ B₂ hB₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_iff_ne]
      intro s₁ hs₁ s₂ hs₂
      -- Extract choice functions from membership in subdivide
      simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hs₁ hs₂
      obtain ⟨c₁, rfl⟩ := hs₁
      obtain ⟨c₂, rfl⟩ := hs₂
      -- Suppose for contradiction that s₁ = s₂
      intro heq
      apply hne
      -- Show B₁ = B₂ using Box.ext
      ext i
      -- At coordinate i, the sides of s₁ and s₂ must be equal
      have h_side_eq : (if c₁ i then (B₁.side i).bisect.snd else (B₁.side i).bisect.fst) =
                       (if c₂ i then (B₂.side i).bisect.snd else (B₂.side i).bisect.fst) := by
        have := congrFun (congrArg Box.side heq) i
        simpa using this
      -- At level k ≥ 1, all sides are Icc. k = 0 case: subdivide_iter B 0 = {B}, so B₁ = B₂
      match k with
      | 0 =>
        -- subdivide_iter B 0 = {B}, so B₁ = B and B₂ = B
        have hB₁' : B₁ = B := by simpa [subdivide_iter] using hB₁
        have hB₂' : B₂ = B := by simpa [subdivide_iter] using hB₂
        simp [hB₁', hB₂']
      | k'+1 =>
      -- Get Icc structure for both sides
      obtain ⟨a₁, b₁, h_side₁⟩ := subdivide_iter_side_is_Icc B k' B₁ hB₁ i
      obtain ⟨a₂, b₂, h_side₂⟩ := subdivide_iter_side_is_Icc B k' B₂ hB₂ i
      -- Get grid positions for B₁.side i and B₂.side i
      obtain ⟨j₁, _, hj₁⟩ := subdivide_iter_side_grid B hB (k'+1) B₁ hB₁ i
      obtain ⟨j₂, _, hj₂⟩ := subdivide_iter_side_grid B hB (k'+1) B₂ hB₂ i
      -- Both have the same length
      have h_len₁ := subdivide_iter_side_length B (k'+1) B₁ hB₁ i
      have h_len₂ := subdivide_iter_side_length B (k'+1) B₂ hB₂ i
      have h_same_len : |B₁.side i|ₗ = |B₂.side i|ₗ := by rw [h_len₁, h_len₂]
      -- Case analysis on c₁ i and c₂ i
      cases hc₁ : c₁ i <;> cases hc₂ : c₂ i <;> simp only [hc₁, hc₂, ite_true] at h_side_eq
      · -- fst = fst case: endpoint equality implies parent equality
        obtain ⟨ha, hb⟩ := BoundedInterval.bisect_fst_eq_endpoints h_side_eq
        -- Both sides are Icc with same endpoints
        simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at ha hb ⊢
        simp [ha, hb]
      · -- fst = snd cross case: parity contradiction via grid positions
        -- Key insight: Grid positions are integers, but fst=snd requires half-integer offset
        -- For degenerate case (L=0): all intervals collapse, so B₁=B₂
        by_cases hL : |B.side i|ₗ = 0
        · -- Degenerate case: all sides at dimension i are singletons
          -- When length = 0 for nonempty box, a = b (singleton)
          -- All subdivisions have same singleton side
          have h1a : (B₁.side i).a = (B.side i).a := by rw [hj₁, hL]; simp
          have h2a : (B₂.side i).a = (B.side i).a := by rw [hj₂, hL]; simp
          have h1len : |B₁.side i|ₗ = 0 := by rw [h_len₁, hL]; simp
          have h2len : |B₂.side i|ₗ = 0 := by rw [h_len₂, hL]; simp
          -- For nonempty Icc intervals with length 0: a = b
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h1b : (B₁.side i).b = (B₁.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            -- For Icc a b, length 0 with a ≤ b means a = b
            unfold BoundedInterval.length at h1len
            simp only [max_eq_right_iff] at h1len
            linarith
          have h2b : (B₂.side i).b = (B₂.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h2len
            simp only [max_eq_right_iff] at h2len
            linarith
          -- Both Icc intervals have same a and b, so they're equal
          simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at h1a h2a h1b h2b ⊢
          simp [h1a, h2a, h1b, h2b]
        · -- Non-degenerate case: derive parity contradiction
          -- From h_side_eq: bisect.fst of B₁ = bisect.snd of B₂
          -- So (B₁.side i).a = (B₂.side i).midpoint = (B₂.side i).a + |B₂.side i|ₗ/2
          have h_fst_a := BoundedInterval.bisect_fst_a (B₁.side i)
          have h_snd_a := BoundedInterval.bisect_snd_a (B₂.side i)
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h_side2_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
          have h_order2 := BoundedInterval.nonempty_implies_le _ h_side2_nonempty
          have h_mid := BoundedInterval.midpoint_eq_a_add_half_length (B₂.side i) h_order2
          -- From h_side_eq, left endpoints are equal
          have h_a_eq : (B₁.side i).bisect.fst.a = (B₂.side i).bisect.snd.a := congrArg (·.a) h_side_eq
          rw [h_fst_a, h_snd_a, h_mid] at h_a_eq
          -- Now we have: B₁.side i.a = B₂.side i.a + |B₂.side i|ₗ/2
          -- Substitute grid formulas
          rw [hj₁, hj₂, h_len₂] at h_a_eq
          -- j₁ * step = j₂ * step + step/2 where step = |B.side i|ₗ / 2^(k'+2)
          have hstep_pos : (0:ℝ) < |B.side i|ₗ / 2 ^ (k' + 2) := by
            apply div_pos
            · exact lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
            · positivity
          -- This gives j₁ = j₂ + 1/2, impossible for natural numbers
          -- Cancel (B.side i).a from both sides
          have h_cancel : j₁ * (|B.side i|ₗ / 2^(k'+1)) =
                          j₂ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) / 2 := by
            have := h_a_eq; linarith
          -- Multiply both sides by 2^(k'+2) / L to get: 2*j₁ = 2*j₂ + 1
          have h2k1_ne : (2:ℝ) ^ (k' + 1) ≠ 0 := by positivity
          have hL_pos : (0:ℝ) < |B.side i|ₗ := lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
          have hL_ne : |B.side i|ₗ ≠ 0 := hL
          have h_step_ne : |B.side i|ₗ / 2^(k'+1) ≠ 0 := by positivity
          have h_parity : (2 * j₁ : ℝ) = 2 * j₂ + 1 := by
            -- From h_cancel: j₁ * step = j₂ * step + step/2
            -- Multiply both sides by 2, then cancel step
            have h2 : 2 * (j₁ * (|B.side i|ₗ / 2^(k'+1))) =
                      2 * j₂ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) := by linarith
            have h3 : (|B.side i|ₗ / 2^(k'+1)) * (2 * j₁) = (|B.side i|ₗ / 2^(k'+1)) * (2 * j₂ + 1) := by
              ring_nf at h2 ⊢; linarith
            exact mul_left_cancel₀ h_step_ne h3
          -- 2*j₁ is even, 2*j₂+1 is odd: contradiction via omega
          have h_eq_nat : 2 * j₁ = 2 * j₂ + 1 := by
            have := h_parity
            norm_cast at this
          omega
      · -- snd = fst cross case: symmetric to fst = snd
        by_cases hL : |B.side i|ₗ = 0
        · -- Degenerate case: identical to fst = snd case
          have h1a : (B₁.side i).a = (B.side i).a := by rw [hj₁, hL]; simp
          have h2a : (B₂.side i).a = (B.side i).a := by rw [hj₂, hL]; simp
          have h1len : |B₁.side i|ₗ = 0 := by rw [h_len₁, hL]; simp
          have h2len : |B₂.side i|ₗ = 0 := by rw [h_len₂, hL]; simp
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h1b : (B₁.side i).b = (B₁.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h1len
            simp only [max_eq_right_iff] at h1len
            linarith
          have h2b : (B₂.side i).b = (B₂.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h2len
            simp only [max_eq_right_iff] at h2len
            linarith
          simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at h1a h2a h1b h2b ⊢
          simp [h1a, h2a, h1b, h2b]
        · -- Non-degenerate case: derive parity contradiction (symmetric argument)
          -- From h_side_eq: bisect.snd of B₁ = bisect.fst of B₂
          -- So (B₁.side i).midpoint = (B₂.side i).a
          have h_snd_a := BoundedInterval.bisect_snd_a (B₁.side i)
          have h_fst_a := BoundedInterval.bisect_fst_a (B₂.side i)
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have h_side1_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
          have h_order1 := BoundedInterval.nonempty_implies_le _ h_side1_nonempty
          have h_mid := BoundedInterval.midpoint_eq_a_add_half_length (B₁.side i) h_order1
          -- From h_side_eq, left endpoints are equal
          have h_a_eq : (B₁.side i).bisect.snd.a = (B₂.side i).bisect.fst.a := congrArg (·.a) h_side_eq
          rw [h_snd_a, h_fst_a, h_mid] at h_a_eq
          -- Now we have: B₁.side i.a + |B₁.side i|ₗ/2 = B₂.side i.a
          -- Substitute grid formulas
          rw [hj₁, hj₂, h_len₁] at h_a_eq
          -- This gives j₁ + 1/2 = j₂, impossible for natural numbers
          -- Cancel (B.side i).a from both sides
          have h_cancel : j₁ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) / 2 =
                          j₂ * (|B.side i|ₗ / 2^(k'+1)) := by
            have := h_a_eq; linarith
          -- Multiply both sides by 2^(k'+2) / L to get: 2*j₁ + 1 = 2*j₂
          have h2k1_ne : (2:ℝ) ^ (k' + 1) ≠ 0 := by positivity
          have hL_pos : (0:ℝ) < |B.side i|ₗ := lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
          have hL_ne : |B.side i|ₗ ≠ 0 := hL
          have h_step_ne : |B.side i|ₗ / 2^(k'+1) ≠ 0 := by positivity
          have h_parity : (2 * j₁ + 1 : ℝ) = 2 * j₂ := by
            -- From h_cancel: j₁ * step + step/2 = j₂ * step
            -- Multiply both sides by 2, then cancel step
            have h2 : 2 * j₁ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) =
                      2 * j₂ * (|B.side i|ₗ / 2^(k'+1)) := by linarith
            have h3 : (|B.side i|ₗ / 2^(k'+1)) * (2 * j₁ + 1) = (|B.side i|ₗ / 2^(k'+1)) * (2 * j₂) := by
              ring_nf at h2 ⊢; linarith
            exact mul_left_cancel₀ h_step_ne h3
          -- 2*j₁+1 is odd, 2*j₂ is even: contradiction via omega
          have h_eq_nat : 2 * j₁ + 1 = 2 * j₂ := by
            have := h_parity
            norm_cast at this
          omega
      · -- snd = snd case: endpoint equality implies parent equality
        obtain ⟨ha, hb⟩ := BoundedInterval.bisect_snd_eq_endpoints h_side_eq
        -- Both sides are Icc with same endpoints
        simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at ha hb ⊢
        simp [ha, hb]

/-- Diameter bound after k iterations of subdivision.
    Each iteration reduces diameter by factor of √2. -/
lemma diameter_subdivide_iter {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (k: ℕ) :
    ∀ B' ∈ subdivide_iter B k, B'.diameter ≤ B.diameter / (Real.sqrt 2) ^ k := by
  induction k with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton, pow_zero, div_one]
    intro B' hB'; rw [hB']
  | succ k ih =>
    intro B' hB'
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB''_mem, hB'_sub⟩ := hB'
    -- B'' is in subdivide_iter B k, and B' is in B''.subdivide
    have hB''_diam := ih B'' hB''_mem
    -- Need: B'' is nonempty to apply subdivide_diameter_bound
    have hB''_nonempty : B''.toSet.Nonempty := subdivide_iter_nonempty B hB k B'' hB''_mem
    have hB'_diam := subdivide_diameter_bound B'' hB''_nonempty B' hB'_sub
    calc B'.diameter
        ≤ B''.diameter / Real.sqrt 2 := hB'_diam
      _ ≤ (B.diameter / (Real.sqrt 2) ^ k) / Real.sqrt 2 := by
          apply div_le_div_of_nonneg_right hB''_diam (Real.sqrt_nonneg 2)
      _ = B.diameter / ((Real.sqrt 2) ^ k * Real.sqrt 2) := by rw [div_div]
      _ = B.diameter / (Real.sqrt 2 * (Real.sqrt 2) ^ k) := by ring_nf
      _ = B.diameter / (Real.sqrt 2) ^ (k + 1) := by rw [pow_succ']

/-- Number of subdivisions needed to get diameter below threshold r.
    Each subdivision reduces diameter by factor of √2, so after k iterations:
    diameter ≤ original_diameter / (√2)^k
    We need (√2)^k > diameter/r, i.e., k > log(diameter/r) / log(√2) = 2·log₂(diameter/r). -/
noncomputable def iter_count {d:ℕ} (B: Box d) (r: ℝ) : ℕ :=
  if B.diameter ≤ 0 then 0
  else if B.diameter < r then 0
  else Nat.ceil (2 * Real.log (B.diameter / r) / Real.log 2) + 1

/-- After iter_count subdivisions, all sub-boxes have diameter < r -/
lemma diameter_lt_of_iter_count {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (r: ℝ) (hr: 0 < r) :
    ∀ B' ∈ subdivide_iter B (B.iter_count r), B'.diameter < r := by
  intro B' hB'
  by_cases h_diam_le : B.diameter ≤ 0
  · -- Degenerate case: diameter ≤ 0 means all sub-boxes also have diameter ≤ 0 < r
    simp only [iter_count, h_diam_le, ↓reduceIte, subdivide_iter] at hB'
    simp only [Finset.mem_singleton] at hB'
    rw [hB']
    calc B.diameter ≤ 0 := h_diam_le
      _ < r := hr
  · push_neg at h_diam_le
    by_cases h_small : B.diameter < r
    · -- Already small enough, no subdivisions needed
      simp only [iter_count, not_le.mpr h_diam_le, h_small, ↓reduceIte, subdivide_iter] at hB'
      simp only [Finset.mem_singleton] at hB'
      rw [hB']; exact h_small
    · -- Need subdivisions: B.diameter ≥ r, so we use the logarithmic formula
      push_neg at h_small
      have h_iter_bound := diameter_subdivide_iter B hB (B.iter_count r) B' hB'
      -- Show that B.diameter / (√2)^k < r for k = iter_count
      -- Key: iter_count = ⌈2 * log(B.diameter / r) / log 2⌉ + 1
      -- So k > 2 * log₂(B.diameter / r), meaning (√2)^k > B.diameter / r
      calc B'.diameter
          ≤ B.diameter / (Real.sqrt 2) ^ (B.iter_count r) := h_iter_bound
        _ < r := by
            -- Need: B.diameter / (√2)^k < r, i.e., (√2)^k > B.diameter / r
            have h_k_def : B.iter_count r = Nat.ceil (2 * Real.log (B.diameter / r) / Real.log 2) + 1 := by
              simp only [iter_count, not_le.mpr h_diam_le, not_lt.mpr h_small, ↓reduceIte]
            -- Prove (√2)^k > B.diameter / r using the logarithmic definition
            have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
            have hsqrt2_pow_pos : 0 < (Real.sqrt 2) ^ (B.iter_count r) := pow_pos hsqrt2_pos _
            have hDr_pos : 0 < B.diameter / r := div_pos h_diam_le hr
            have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            rw [div_lt_iff₀ hsqrt2_pow_pos]
            -- Goal: B.diameter < r * (√2)^k
            set L := 2 * Real.log (B.diameter / r) / Real.log 2 with hL_def
            -- k > L because k = ⌈L⌉ + 1 > L
            have hk_gt : ((B.iter_count r) : ℝ) > L := by
              have h_ceil_ge : (Nat.ceil L : ℝ) ≥ L := Nat.le_ceil L
              have hk_eq : ((B.iter_count r) : ℝ) = (Nat.ceil L : ℝ) + 1 := by
                simp only [h_k_def]; norm_cast
              linarith
            -- k/2 > log₂(B.diameter/r)
            have hL_eq : L = 2 * (Real.log (B.diameter / r) / Real.log 2) := by ring
            have hk_half_gt : ((B.iter_count r) : ℝ) / 2 > Real.log (B.diameter / r) / Real.log 2 := by
              have : ((B.iter_count r) : ℝ) > 2 * (Real.log (B.diameter / r) / Real.log 2) := by
                rw [← hL_eq]; exact hk_gt
              linarith
            -- (√2)^k = 2^(k/2)
            have hsqrt_pow : (Real.sqrt 2) ^ (B.iter_count r) =
                             (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) := by
              have h1 : Real.sqrt 2 = (2 : ℝ) ^ ((1:ℝ) / 2) := Real.sqrt_eq_rpow 2
              conv_lhs => rw [h1]
              rw [← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ)/2)) (B.iter_count r)]
              rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
              congr 1; ring
            -- 2^(k/2) > B.diameter/r
            have h2pow_gt : (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) > B.diameter / r := by
              rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
              have hsimp : Real.log (B.diameter / r) / Real.log 2 * Real.log 2 =
                          Real.log (B.diameter / r) := by field_simp
              have h_exp_ineq : Real.log 2 * (((B.iter_count r) : ℝ) / 2) >
                               Real.log (B.diameter / r) := by
                calc Real.log 2 * (((B.iter_count r) : ℝ) / 2)
                    = ((B.iter_count r) : ℝ) / 2 * Real.log 2 := by ring
                  _ > Real.log (B.diameter / r) / Real.log 2 * Real.log 2 := by
                       apply mul_lt_mul_of_pos_right hk_half_gt hlog2_pos
                  _ = Real.log (B.diameter / r) := hsimp
              calc Real.exp (Real.log 2 * (((B.iter_count r) : ℝ) / 2))
                  > Real.exp (Real.log (B.diameter / r)) := Real.exp_strictMono h_exp_ineq
                _ = B.diameter / r := Real.exp_log hDr_pos
            -- Combine
            rw [hsqrt_pow]
            calc B.diameter = (B.diameter / r) * r := by field_simp
              _ < (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) * r := by
                  apply mul_lt_mul_of_pos_right h2pow_gt hr
              _ = r * (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) := by ring

/-- Subdivided boxes cover the original box: any point in B.toSet is contained in
    some box in subdivide_iter B k. -/
lemma subdivide_iter_covers {d:ℕ} (B : Box d) (k : ℕ) (x : EuclideanSpace' d)
    (hx : x ∈ B.toSet) : ∃ B' ∈ subdivide_iter B k, x ∈ B'.toSet := by
  induction k with
  | zero =>
    refine ⟨B, ?_, hx⟩
    simp only [subdivide_iter_zero, Finset.mem_singleton]
  | succ k ih =>
    obtain ⟨B'', hB''_mem, hx_B''⟩ := ih
    -- B'' is subdivided, x is in B''.toSet, need to find B' ∈ B''.subdivide with x ∈ B'
    -- Define choice function: c i = true iff x i is in right half
    let c : Fin d → Bool := fun i => decide (x i ≥ (B''.side i).midpoint)
    -- The sub-box for this choice contains x
    let B' : Box d := {
      side := fun i => if c i then (B''.side i).bisect.snd else (B''.side i).bisect.fst
    }
    refine ⟨B', ?_, ?_⟩
    · -- B' ∈ subdivide_iter B (k+1)
      simp only [subdivide_iter_succ, Finset.mem_biUnion]
      exact ⟨B'', hB''_mem, by simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨c, rfl⟩⟩
    · -- x ∈ B'.toSet: for each i, x i is in the appropriate half
      intro i hi
      have hx_i : x i ∈ (B''.side i).toSet := by
        have := hx_B''
        simp only [toSet] at this
        exact this i (Set.mem_univ i)
      simp only [B']
      by_cases hm : x i ≥ (B''.side i).midpoint
      · have hc : c i = true := decide_eq_true hm
        simp only [hc, ite_true]
        exact (BoundedInterval.mem_bisect_snd_iff (B''.side i) (x i) hx_i).mpr hm
      · push_neg at hm
        have hc : c i = false := decide_eq_false (not_le.mpr hm)
        simp only [hc]
        exact (BoundedInterval.mem_bisect_fst_iff (B''.side i) (x i) hx_i).mpr (le_of_lt hm)

/-- Box volume is non-negative (product of non-negative interval lengths). -/
lemma volume_nonneg {d : ℕ} (B : Box d) : 0 ≤ B.volume := by
  unfold volume
  apply Finset.prod_nonneg
  intro i _
  unfold BoundedInterval.length
  exact le_max_right _ _

end Box

namespace Lebesgue_outer_measure

/-- Any ℕ-indexed cover gives an upper bound on outer measure.
    Follows directly from the infimum definition. -/
lemma le_of_nat_cover {d:ℕ} (hd: 0 < d) (E: Set (EuclideanSpace' d))
    (S : ℕ → Box d) (hcover : E ⊆ ⋃ n, (S n).toSet) :
    Lebesgue_outer_measure E ≤ ∑' n, (S n).volume.toEReal := by
  rw [Lebesgue_outer_measure_eq_nat_indexed hd]
  apply csInf_le
  · -- Show the set is bounded below by 0
    use 0
    intro v hv
    obtain ⟨S', _, rfl⟩ := hv
    apply tsum_nonneg
    intro n
    exact EReal.coe_nonneg.mpr (Box.volume_nonneg _)
  · -- S is in the set of covers
    exact ⟨S, hcover, rfl⟩

/-- Upper bound from finset-indexed cover: if a set is covered by ⋃ n, ⋃ B ∈ I n, B.toSet
    where each I n is a finite set of boxes, then the outer measure is bounded by the
    sum of volumes.

    Proof strategy:
    1. The sigma type (n : ℕ) × ↑(I n) is countable (and hence encodable)
    2. Use Encodable instance to define S : ℕ → Box d via decoding
    3. Pad with zero-volume box for invalid decodings
    4. Apply le_of_nat_cover and bound the enumerated sum -/
lemma le_of_finset_cover {d:ℕ} (hd: 0 < d) (E: Set (EuclideanSpace' d))
    (I : ℕ → Finset (Box d)) (hcover : E ⊆ ⋃ n, ⋃ B ∈ I n, B.toSet) :
    Lebesgue_outer_measure E ≤ ∑' n, (∑ B ∈ I n, B.volume).toEReal := by
  -- Define the sigma type for enumeration
  let SigmaType := (n : ℕ) × (I n : Set (Box d))
  -- SigmaType is countable (ℕ × finite = countable)
  haveI : Countable SigmaType := instCountableSigma
  -- Get encodable instance from countable
  haveI : Encodable SigmaType := Encodable.ofCountable SigmaType

  -- Construct a zero-volume box for padding (exists when d > 0)
  have ⟨B₀, hB₀⟩ : ∃ B : Box d, B.volume = 0 := by
    use ⟨fun _ => BoundedInterval.Ioc 0 0⟩
    simp only [Box.volume, BoundedInterval.length]
    -- The interval [0, 0] has length max(0-0, 0) = 0
    -- Product of zeros over Fin d (when d > 0) is 0
    have h_fin_nonempty : (Finset.univ : Finset (Fin d)).Nonempty := by
      use ⟨0, hd⟩
      exact Finset.mem_univ _
    obtain ⟨i, hi⟩ := h_fin_nonempty
    apply Finset.prod_eq_zero hi
    simp [sub_self]

  -- Define enumeration using decode₂ (which guarantees encode ∘ decode₂ = id on Some values)
  let S : ℕ → Box d := fun m =>
    match Encodable.decode₂ SigmaType m with
    | some p => p.2.val
    | none => B₀

  -- S covers E: every point in E is in some box from some I n
  -- Key: decode₂ (encode p) = some p, so S (encode p) = p.2.val
  have hS_cover : E ⊆ ⋃ m, (S m).toSet := by
    intro x hx
    -- x is in E ⊆ ⋃ n, ⋃ B ∈ I n, B.toSet
    -- So x ∈ B.toSet for some B ∈ I n for some n
    have hx' := hcover hx
    -- Extract the nested union structure
    rw [Set.mem_iUnion] at hx'
    obtain ⟨n, hx_n⟩ := hx'
    rw [Set.mem_iUnion] at hx_n
    obtain ⟨B, hx_B⟩ := hx_n
    rw [Set.mem_iUnion] at hx_B
    obtain ⟨hB_mem, hx_in_B⟩ := hx_B
    -- The pair (n, ⟨B, hB_mem⟩) is in SigmaType
    let p : SigmaType := ⟨n, ⟨B, hB_mem⟩⟩
    rw [Set.mem_iUnion]
    use Encodable.encode p
    -- S (encode p) = p.2.val = B (using decode₂_encode)
    show x ∈ (S (Encodable.encode p)).toSet
    simp only [Encodable.decode₂_encode, S]
    exact hx_in_B

  -- Apply le_of_nat_cover
  have h_le := le_of_nat_cover hd E S hS_cover

  -- Now bound ∑' m, (S m).volume.toEReal ≤ ∑' n, (∑ B ∈ I n, B.volume).toEReal
  -- Using decode₂, each box B ∈ I n appears exactly once in the LHS (at encode (n, B))
  -- and invalid decodings contribute B₀.volume = 0

  calc Lebesgue_outer_measure E
      ≤ ∑' m, (S m).volume.toEReal := h_le
    _ ≤ ∑' n, (∑ B ∈ I n, B.volume).toEReal := by
        -- The LHS can be rewritten using ENNReal.tsum_decode₂_eq
        -- LHS = ∑' m, (match decode₂ m with | some p => p.2.val.volume | none => 0).toEReal
        --     = ∑' p : SigmaType, p.2.val.volume.toEReal  (by tsum_decode₂_eq for volume)
        --     = ∑' (n, B), B.val.volume.toEReal
        -- RHS = ∑' n, (∑ B ∈ I n, B.volume).toEReal

        -- First, show the sums are equal by converting through sigma type
        have h_eq : ∑' m, (S m).volume.toEReal =
                    ∑' (p : SigmaType), p.2.val.volume.toEReal := by
          -- Use Function.Injective.tsum_eq with encode being injective
          -- Define g : ℕ → EReal as the volume function on decoded values
          let g : ℕ → EReal := fun m =>
            match Encodable.decode₂ SigmaType m with
            | some p => p.2.val.volume.toEReal
            | none => 0
          -- g m = (S m).volume.toEReal because:
          -- - when decode₂ m = some p: g m = p.2.val.volume.toEReal = (S m).volume.toEReal
          -- - when decode₂ m = none: g m = 0, S m = B₀, B₀.volume = 0
          have h_g_eq : ∀ m, g m = (S m).volume.toEReal := by
            intro m
            simp only [g, S]
            cases h : Encodable.decode₂ SigmaType m with
            | none => simp [hB₀]
            | some p => rfl
          -- Support of g is contained in range of encode
          have h_support : Function.support g ⊆ Set.range (Encodable.encode (α := SigmaType)) := by
            intro m hm
            simp only [Function.mem_support, ne_eq, g] at hm
            cases h : Encodable.decode₂ SigmaType m with
            | none => simp [h] at hm
            | some p =>
              rw [Set.mem_range]
              use p
              exact Encodable.decode₂_eq_some.mp h
          have h_inj := Encodable.encode_injective (α := SigmaType)
          have h_val_eq : ∀ p : SigmaType, g (Encodable.encode p) = p.2.val.volume.toEReal := by
            intro p
            simp only [g, Encodable.decode₂_encode]
          calc ∑' m, (S m).volume.toEReal
              = ∑' m, g m := by simp only [h_g_eq]
            _ = ∑' (p : SigmaType), g (Encodable.encode p) := (h_inj.tsum_eq h_support).symm
            _ = ∑' (p : SigmaType), p.2.val.volume.toEReal := by simp only [h_val_eq]

        -- The sigma type sum equals the nested finset sum
        have h_sigma_eq_nested : ∑' (p : SigmaType), p.2.val.volume.toEReal =
                                  ∑' n, (∑ B ∈ I n, B.volume).toEReal := by
          -- Key: SigmaType = (n : ℕ) × ↑(I n) where each fiber ↑(I n) is finite

          -- First, show inner tsum equals finset sum
          have h_inner : ∀ n, ∑' (B : (I n : Set (Box d))), B.val.volume.toEReal =
                              (∑ B ∈ I n, B.volume).toEReal := by
            intro n
            -- Use Finset.fintypeCoeSort for tsum_fintype
            haveI : Fintype (I n : Set (Box d)) := Finset.fintypeCoeSort (I n)
            rw [tsum_fintype]
            have h_nonneg : ∀ B ∈ I n, 0 ≤ B.volume := fun B _ => Box.volume_nonneg B
            -- Convert sum: need to go from ↑↑(I n) to { x // x ∈ I n } to I n
            have h_subtype : ∑ B : { x // x ∈ I n }, B.val.volume = ∑ B ∈ I n, B.volume :=
              Finset.sum_coe_sort (I n) (fun B => B.volume)
            -- Convert from ↑↑(I n) to { x // x ∈ I n } using equivalence
            let e : (I n : Set (Box d)) ≃ { x // x ∈ I n } := {
              toFun := fun ⟨B, hB⟩ => ⟨B, hB⟩
              invFun := fun ⟨B, hB⟩ => ⟨B, hB⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
            }
            -- Use Fintype.sum_equiv - the fintype instances will be handled by congr
            have h_equiv : ∑ B : (I n : Set (Box d)), B.val.volume =
                          ∑ B : { x // x ∈ I n }, B.val.volume :=
              Fintype.sum_equiv e (fun B => B.val.volume) (fun B => B.val.volume)
                (fun ⟨B, hB⟩ => rfl)
            -- Combine: the fintype instances differ but the sums are equal
            have h_sum_real : ∑ B : (I n : Set (Box d)), B.val.volume = ∑ B ∈ I n, B.volume := by
              rw [h_equiv]
              -- Use erw (exact rewrite) which is more lenient with typeclass instances
              erw [h_subtype]
            calc ∑ B : (I n : Set (Box d)), B.val.volume.toEReal
                = (∑ B : (I n : Set (Box d)), B.val.volume).toEReal := by
                    symm
                    apply EReal.coe_finset_sum
                    intro ⟨B, hB⟩ _
                    exact Box.volume_nonneg B
              _ = (∑ B ∈ I n, B.volume).toEReal := by rw [h_sum_real]

          -- Decompose sigma tsum as nested tsum
          have h_sigma_decomp : ∑' (p : SigmaType), p.2.val.volume.toEReal =
                                 ∑' n, ∑' (B : (I n : Set (Box d))), B.val.volume.toEReal := by
            -- Since fibers are finite, each inner sum is a finite sum
            -- For non-negative EReal with finite fibers, tsum_sigma works
            haveI : ∀ n, Fintype (I n : Set (Box d)) := fun n => Finset.fintypeCoeSort (I n)

            -- Use tsum_fintype on inner sum to make it finite, then standard decomposition
            have h_eq_finite : ∀ n, ∑' (B : (I n : Set (Box d))), B.val.volume.toEReal =
                                     ∑ B : (I n : Set (Box d)), B.val.volume.toEReal := by
              intro n
              exact tsum_fintype _
            simp_rw [h_eq_finite]

            -- Lift to ENNReal to use unconditional tsum_sigma
            -- Define ENNReal version of the term
            let f_enn : SigmaType → ENNReal := fun p => ENNReal.ofReal p.2.val.volume

            -- Decomposition holds in ENNReal
            have h_enn_decomp : ∑' p, f_enn p = ∑' n, ∑' (B : (I n : Set (Box d))), f_enn ⟨n, B⟩ :=
              ENNReal.tsum_sigma' _

            -- Define coercion to EReal
            let φ : ENNReal →+ EReal := {
              toFun := fun x => (↑x : EReal)
              map_zero' := rfl
              map_add' := EReal.coe_ennreal_add
            }
            have h_cont : Continuous φ := continuous_coe_ennreal_ereal

            -- Show LHS equals coerced ENNReal sum
            have h_lhs : ∑' (p : SigmaType), p.snd.val.volume.toEReal = ↑(∑' (p : SigmaType), f_enn p) := by
              have h_eq : ∀ p : SigmaType, p.snd.val.volume.toEReal = φ (f_enn p) := by
                intro p
                simp only [f_enn, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
                rw [EReal.coe_ennreal_ofReal, max_eq_left (Box.volume_nonneg _)]
              simp_rw [h_eq]
              exact (Summable.map_tsum ENNReal.summable φ h_cont).symm

            -- Show RHS equals coerced ENNReal sum (using sum instead of tsum for inner)
            have h_rhs : ∑' n, ∑ (B : (I n : Set (Box d))), B.val.volume.toEReal =
                         ↑(∑' n, ∑' (B : (I n : Set (Box d))), f_enn ⟨n, B⟩) := by
              -- Convert inner tsum to sum in ENNReal
              have h_inner_enn : ∀ n, ∑' (B : (I n : Set (Box d))), f_enn ⟨n, B⟩ =
                                      ∑ B, f_enn ⟨n, B⟩ := fun n => tsum_fintype _
              simp_rw [h_inner_enn]

              -- Map coercion through outer sum
              have h_outer : ∑' n, ∑ (B : (I n : Set (Box d))), B.val.volume.toEReal =
                             ↑(∑' n, ∑ (B : (I n : Set (Box d))), f_enn ⟨n, B⟩) := by
                have h_eq_term : ∀ n, ∑ (B : (I n : Set (Box d))), B.val.volume.toEReal = φ (∑ (B : (I n : Set (Box d))), f_enn ⟨n, B⟩) := by
                  intro n
                  rw [map_sum]
                  apply Finset.sum_congr rfl
                  intro (B : (I n : Set (Box d))) _
                  simp only [f_enn, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
                  rw [EReal.coe_ennreal_ofReal, max_eq_left (Box.volume_nonneg _)]
                simp_rw [h_eq_term]
                exact (Summable.map_tsum ENNReal.summable φ h_cont).symm

              exact h_outer

            rw [h_lhs, h_rhs, h_enn_decomp]

          rw [h_sigma_decomp]
          congr 1
          ext n
          exact h_inner n

        rw [h_eq, h_sigma_eq_nested]


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


end Lebesgue_outer_measure

-- ========================================================================
-- End of Helpers for lemma 1.2.5
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

  -- Direction 1: m*(E ∪ F) ≤ m*(E) + m*(F) [Subadditivity]
  have h_le : Lebesgue_outer_measure (E ∪ F) ≤ Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
    -- Use finite_union_le for two sets
    let E' : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
    have h_union : E ∪ F = ⋃ i, E' i := by
      simp only [E']
      ext x
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · intro hx
        cases hx with
        | inl hE => exact ⟨0, hE⟩
        | inr hF => exact ⟨1, hF⟩
      · intro ⟨i, hi⟩
        fin_cases i
        · left; exact hi
        · right; exact hi
    have h_sum : ∑ i : Fin 2, Lebesgue_outer_measure (E' i) =
        Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
      simp only [Fin.sum_univ_two, E', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h_union, ← h_sum]
    exact finite_union_le E'

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

        -- For each box S(n), subdivide k(n) = (S n).iter_count r times
        let k : ℕ → ℕ := fun n => (S n).iter_count r

        -- All refined boxes have diameter < r < set_dist E F
        have h_diam : ∀ n, ∀ B' ∈ Box.subdivide_iter (S n) (k n), B'.diameter < r := by
          intro n B' hB'
          by_cases hnonempty : (S n).toSet.Nonempty
          · exact Box.diameter_lt_of_iter_count (S n) hnonempty r hr_pos B' hB'
          · -- Empty box case: iter_count = 0 when diameter ≤ 0, so subdivide_iter = {S n}
            have h_empty : (S n).toSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
            have h_diam_zero : (S n).diameter = 0 := Box.diameter_of_empty (S n) h_empty
            -- iter_count = 0 since diameter = 0 ≤ 0
            have h_k_zero : k n = 0 := by
              simp only [k, Box.iter_count, h_diam_zero, le_refl, ↓reduceIte]
            -- So subdivide_iter (S n) 0 = {S n}, meaning B' = S n
            rw [h_k_zero, Box.subdivide_iter_zero, Finset.mem_singleton] at hB'
            rw [hB', h_diam_zero]
            exact hr_pos

        -- Partition: for each n, split subdivisions into E-intersecting and F-intersecting
        -- Use classical decidability for the filter predicate
        haveI : ∀ (B' : Box d), Decidable ((B'.toSet ∩ E).Nonempty) := fun _ => Classical.dec _
        haveI : ∀ (B' : Box d), Decidable ((B'.toSet ∩ F).Nonempty) := fun _ => Classical.dec _
        let I_E_n : ℕ → Finset (Box d) := fun n =>
          (Box.subdivide_iter (S n) (k n)).filter (fun B' => (B'.toSet ∩ E).Nonempty)
        let I_F_n : ℕ → Finset (Box d) := fun n =>
          (Box.subdivide_iter (S n) (k n)).filter (fun B' => (B'.toSet ∩ F).Nonempty)

        -- Disjointness at each level n: no box intersects both E and F
        have h_disj_n : ∀ n, Disjoint (I_E_n n) (I_F_n n) := by
          intro n
          rw [Finset.disjoint_filter]
          intro B' hB'_sub hB'_E hB'_F
          -- B' intersects both E and F, but diameter < r < set_dist E F: contradiction
          have h_small : B'.diameter < set_dist E F := by
            calc B'.diameter < r := h_diam n B' hB'_sub
            _ < set_dist E F := hr_lt
          exact Box.not_intersects_both_of_diameter_lt B' E F h_small ⟨hB'_E, hB'_F⟩

        -- E is covered by the E-intersecting subdivisions
        have hE_cover : E ⊆ ⋃ n, ⋃ B' ∈ I_E_n n, B'.toSet := by
          intro x hxE
          have hx_union : x ∈ E ∪ F := Set.mem_union_left F hxE
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hS_cover hx_union)
          obtain ⟨B', hB'_mem, hx_B'⟩ := Box.subdivide_iter_covers (S n) (k n) x hn
          have hB'_in_IE : B' ∈ I_E_n n := by
            rw [Finset.mem_filter]
            exact ⟨hB'_mem, ⟨x, hx_B', hxE⟩⟩
          simp only [Set.mem_iUnion]
          exact ⟨n, ⟨B', ⟨hB'_in_IE, hx_B'⟩⟩⟩

        -- F is covered by the F-intersecting subdivisions
        have hF_cover : F ⊆ ⋃ n, ⋃ B' ∈ I_F_n n, B'.toSet := by
          intro x hxF
          have hx_union : x ∈ E ∪ F := Set.mem_union_right E hxF
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hS_cover hx_union)
          obtain ⟨B', hB'_mem, hx_B'⟩ := Box.subdivide_iter_covers (S n) (k n) x hn
          have hB'_in_IF : B' ∈ I_F_n n := by
            rw [Finset.mem_filter]
            exact ⟨hB'_mem, ⟨x, hx_B', hxF⟩⟩
          simp only [Set.mem_iUnion]
          exact ⟨n, ⟨B', ⟨hB'_in_IF, hx_B'⟩⟩⟩

        -- Volume bounds: m*(E) ≤ sum over E-intersecting boxes
        have hE_bound : Lebesgue_outer_measure E ≤ ∑' n, (∑ B' ∈ I_E_n n, B'.volume).toEReal :=
          le_of_finset_cover hd E I_E_n hE_cover

        have hF_bound : Lebesgue_outer_measure F ≤ ∑' n, (∑ B' ∈ I_F_n n, B'.volume).toEReal :=
          le_of_finset_cover hd F I_F_n hF_cover

        -- Key: disjoint partition means ∑ I_E_n + ∑ I_F_n ≤ ∑ all subdivisions
        have h_sum_le : ∀ n, (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume)
            ≤ ∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume := by
          intro n
          -- Step 1: ∑ A + ∑ B = ∑ (A ∪ B) for disjoint sets
          rw [← Finset.sum_union (h_disj_n n)]
          -- Step 2: A ∪ B ⊆ subdivide_iter since both are filters of it
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Union of filters ⊆ original set
            intro B' hB'
            rw [Finset.mem_union] at hB'
            cases hB' with
            | inl h => exact Finset.filter_subset _ _ h
            | inr h => exact Finset.filter_subset _ _ h
          · -- Volumes are non-negative
            intro B' _ _
            unfold Box.volume
            apply Finset.prod_nonneg
            intro i _
            unfold BoundedInterval.length
            exact le_max_right _ _

        -- Volume equality: sum over subdivisions = original volume
        have h_vol_eq : ∀ n, (S n).toSet.Nonempty →
            (∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume) = (S n).volume := by
          intro n hn
          exact Box.volume_subdivide_iter (S n) hn (k n)

        -- Final calculation: combine bounds
        calc Lebesgue_outer_measure E + Lebesgue_outer_measure F
            ≤ (∑' n, (∑ B' ∈ I_E_n n, B'.volume).toEReal) +
              (∑' n, (∑ B' ∈ I_F_n n, B'.volume).toEReal) :=
                add_le_add hE_bound hF_bound
          _ ≤ ∑' n, (S n).volume.toEReal := by
              -- Convert to ENNReal where we have better tsum properties
              -- Key fact: for non-negative reals, x.toEReal = (x.toNNReal : ENNReal).toEReal
              -- Step 1: Show pointwise (∑ I_E_n) + (∑ I_F_n) ≤ vol(S n)
              have h_pw_le : ∀ n, (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume) ≤ (S n).volume := by
                intro n
                calc (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume)
                    ≤ ∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume := h_sum_le n
                  _ ≤ (S n).volume := by
                    by_cases hn : (S n).toSet.Nonempty
                    · exact le_of_eq (h_vol_eq n hn)
                    · -- Empty box: volume = 0, and sum over subdivisions ≤ 0 = vol
                      have hempty : (S n).toSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
                      have hvol_zero : (S n).volume = 0 := Box.volume_eq_zero_of_empty (S n) hempty
                      rw [hvol_zero]
                      -- subdivide_iter of empty box = {S n} with volume 0
                      have hk_zero : k n = 0 := by
                        simp only [k, Box.iter_count]
                        have hdiam : (S n).diameter = 0 := Box.diameter_of_empty (S n) hempty
                        simp only [hdiam, le_refl, ↓reduceIte]
                      rw [hk_zero, Box.subdivide_iter_zero, Finset.sum_singleton, hvol_zero]

              -- Step 2: Apply helper lemma for tsum inequality in EReal
              have h_E_nonneg : ∀ n, 0 ≤ ∑ B' ∈ I_E_n n, B'.volume := by
                intro n; apply Finset.sum_nonneg; intro B' _; exact Box.volume_nonneg B'
              have h_F_nonneg : ∀ n, 0 ≤ ∑ B' ∈ I_F_n n, B'.volume := by
                intro n; apply Finset.sum_nonneg; intro B' _; exact Box.volume_nonneg B'

              -- Apply the helper lemma
              exact EReal.tsum_add_le_of_nonneg_pointwise h_E_nonneg h_F_nonneg h_pw_le
          _ ≤ Lebesgue_outer_measure (E ∪ F) + (ε : EReal) := hS_vol

      -- From h_eps, conclude the inequality holds
      exact EReal.le_of_forall_pos_le_add' h_eps

  -- Combine both directions
  exact le_antisymm h_le h_ge

example : set_dist (Ico 0 1).toSet (Icc 1 2).toSet = 0 := by
  apply le_antisymm
  · -- set_dist ≤ 0: by contradiction, if set_dist > 0, we find a closer pair
    by_contra hne
    simp only [not_le] at hne
    -- So set_dist > 0
    have hpos := hne
    -- Take ε = set_dist / 2
    set ε := set_dist (Ico 0 1).toSet (Icc 1 2).toSet / 2 with hε_def
    have hε_pos : 0 < ε := by linarith
    -- set_dist ≤ dist(0, 1) = 1, so ε ≤ 1/2
    have h_upper : set_dist (Ico 0 1).toSet (Icc 1 2).toSet ≤ 1 := by
      unfold set_dist
      apply csInf_le
      · use 0
        intro r hr
        obtain ⟨⟨x, y⟩, ⟨_, _⟩, rfl⟩ := hr
        exact dist_nonneg
      · refine ⟨(0, 1), ⟨?_, ?_⟩, ?_⟩
        · norm_num
        · norm_num
        · simp [Real.dist_eq]
    have hε_le : ε ≤ 1/2 := by linarith
    -- The point (1 - ε, 1) has distance ε < set_dist, contradiction
    have hmem : dist (1 - ε) 1 ∈ (fun p : ℝ × ℝ ↦ dist p.1 p.2) '' ((Ico 0 1).toSet ×ˢ (Icc 1 2).toSet) := by
      refine ⟨(1 - ε, 1), ⟨?_, ?_⟩, rfl⟩
      · constructor <;> linarith
      · constructor <;> linarith
    have hdist_val : dist (1 - ε) 1 = ε := by
      rw [Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hε_pos]
    unfold set_dist at hpos hε_def
    have hle : sInf ((fun p : ℝ × ℝ ↦ dist p.1 p.2) '' ((Ico 0 1).toSet ×ˢ (Icc 1 2).toSet)) ≤ ε := by
      apply csInf_le
      · use 0
        intro r hr
        obtain ⟨⟨x, y⟩, ⟨_, _⟩, rfl⟩ := hr
        exact dist_nonneg
      · rw [← hdist_val]; exact hmem
    linarith
  · -- 0 ≤ set_dist: infimum of nonnegative values is nonnegative
    unfold set_dist
    apply le_csInf
    · -- Nonempty
      refine ⟨dist 0 1, (0, 1), ⟨?_, ?_⟩, rfl⟩
      · norm_num
      · norm_num
    · intro r hr
      obtain ⟨⟨x, y⟩, ⟨_, _⟩, rfl⟩ := hr
      exact dist_nonneg

/-- Exercise 1.2.4 -/
theorem dist_of_disj_compact_pos {d:ℕ} (E F: Set (EuclideanSpace' d)) (hE: IsCompact E) (hF: IsCompact F) (hdisj: E ∩ F = ∅) :
    set_dist E F > 0 := by
  sorry

-- ========================================================================
-- Start of Helper lemmas for Lemma 1.2.6
-- ========================================================================

/-- Sum of geometric series δ/2^{n+2} equals δ/2 -/
lemma tsum_geometric_inflate {δ : ℝ} (_hδ : 0 < δ) :
    ∑' n : ℕ, δ / 2^(n+2) = δ / 2 := by
  -- ∑ δ/2^{n+2} = δ/4 * ∑ (1/2)^n = δ/4 * 2 = δ/2
  have h_eq : (fun n => δ / 2^(n+2)) = (fun n => δ / 4 * (1/2 : ℝ)^n) := by
    ext n
    have : (2 : ℝ)^(n+2) = 4 * 2^n := by ring
    rw [this]
    field_simp
  rw [h_eq, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)]
  field_simp; ring
/-- When P_nonempty ⊆ P, the loss from scaling is bounded by δ/4. -/
lemma card_ratio_bound {P_nonempty P : Finset α} (hP_nonempty_sub : P_nonempty ⊆ P)
    {δ : ℝ} (hδ_pos : 0 < δ) (hcard_pos : 0 < P.card) :
    P_nonempty.card * (δ / (4 * P.card)) ≤ δ / 4 := by
  have hP_card_pos : (0 : ℝ) < P.card := Nat.cast_pos.mpr hcard_pos
  have h_card_bound : P_nonempty.card ≤ P.card := Finset.card_le_card hP_nonempty_sub
  have h_div_nonneg : (0 : ℝ) ≤ δ / (4 * P.card) := by positivity
  calc P_nonempty.card * (δ / (4 * P.card))
      ≤ P.card * (δ / (4 * P.card)) := by
        apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_card_bound) h_div_nonneg
    _ = δ / 4 := by field_simp [hP_card_pos.ne.symm]; ring

/-- Sum bound from partition filter: if volumes B' satisfy B.vol ≤ B'.vol + ε,
    then summing over P_nonempty gives total bound with card * ε term. -/
lemma partition_volume_bound {d : ℕ} {P : Finset (Box d)}
    {P_nonempty : Finset (Box d)} (_hP_nonempty_sub : P_nonempty ⊆ P)
    {B' : (B : Box d) → B ∈ P_nonempty → Box d}
    {ε : ℝ} (_hε_pos : 0 < ε)
    (h_vol_bound : ∀ B (hB : B ∈ P_nonempty), B.volume ≤ (B' B hB).volume + ε) :
    ∑ B ∈ P_nonempty, B.volume ≤
      ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume + P_nonempty.card * ε := by
  calc ∑ B ∈ P_nonempty, B.volume
      = ∑ x : { B // B ∈ P_nonempty }, x.1.volume := by rw [← Finset.sum_coe_sort]
    _ ≤ ∑ x : { B // B ∈ P_nonempty }, ((B' x.1 x.2).volume + ε) := by
        apply Finset.sum_le_sum
        intro ⟨B, hB⟩ _
        exact h_vol_bound B hB
    _ = ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume + ∑ _ : { B // B ∈ P_nonempty }, ε :=
        Finset.sum_add_distrib
    _ = ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume + P_nonempty.card * ε := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, ← smul_eq_mul]
        have : (Finset.univ : Finset { B // B ∈ P_nonempty }).image (fun x => x.val) = P_nonempty := by
          ext B
          simp only [Finset.mem_image]
          constructor
          · intro ⟨a, _, ha_eq⟩; rw [← ha_eq]; exact a.property
          · intro hB; exact ⟨⟨B, hB⟩, Finset.mem_univ _, rfl⟩
        rw [← Finset.card_univ, ← this]
        rw [Finset.card_image_of_injective _ (fun x y h => Subtype.ext h)]
        simp [smul_eq_mul]

/-- Shrunk boxes B' inherit injectivity from parent boxes' disjointness when B' are nonempty. -/
lemma injective_of_shrunk_nonempty {d : ℕ} {P : Finset (Box d)}
    {P_nonempty : Finset (Box d)} (hP_nonempty_sub : P_nonempty ⊆ P)
    {B' : (B : Box d) → B ∈ P_nonempty → Box d}
    (hP_disj : (P : Set (Box d)).PairwiseDisjoint Box.toSet)
    (h_sub : ∀ B (hB : B ∈ P_nonempty), (B' B hB).toSet ⊆ B.toSet)
    (h_nonempty : ∀ B (hB : B ∈ P_nonempty), (B' B hB).toSet.Nonempty) :
    Function.Injective (fun x : { B // B ∈ P_nonempty } => B' x.1 x.2) := by
  intro ⟨B₁, hB₁⟩ ⟨B₂, hB₂⟩ h_boxes_eq
  by_contra h_ne
  have hB₁P : B₁ ∈ P := hP_nonempty_sub hB₁
  have hB₂P : B₂ ∈ P := hP_nonempty_sub hB₂
  have h_orig_ne : B₁ ≠ B₂ := fun h_eq_B => h_ne (Subtype.ext h_eq_B)
  have h_orig_disj : Disjoint B₁.toSet B₂.toSet := hP_disj hB₁P hB₂P h_orig_ne
  have h_B'₁_nonempty : (B' B₁ hB₁).toSet.Nonempty := h_nonempty B₁ hB₁
  have h_in_inter : (B' B₁ hB₁).toSet ⊆ B₁.toSet ∩ B₂.toSet := by
    intro x hx
    have h_toSet_eq : (B' B₁ hB₁).toSet = (B' B₂ hB₂).toSet := congr_arg Box.toSet h_boxes_eq
    exact ⟨h_sub B₁ hB₁ hx, h_sub B₂ hB₂ (h_toSet_eq ▸ hx)⟩
  have h_inter_empty : B₁.toSet ∩ B₂.toSet = ∅ := Set.disjoint_iff_inter_eq_empty.mp h_orig_disj
  rw [h_inter_empty] at h_in_inter
  exact Set.not_nonempty_empty (h_B'₁_nonempty.mono h_in_inter)

/-- Every bounded interval (Ioo, Icc, Ioc, Ico) is a bounded set -/
lemma BoundedInterval.isBounded (I: BoundedInterval) : Bornology.IsBounded I.toSet := by
  cases I with
  | Ioo a b => simp only [toSet]; exact Metric.isBounded_Ioo a b
  | Icc a b => simp only [toSet]; exact Metric.isBounded_Icc a b
  | Ioc a b => simp only [toSet]; exact Metric.isBounded_Ioc a b
  | Ico a b => simp only [toSet]; exact Metric.isBounded_Ico a b

/-- Every box is bounded (product of bounded intervals) -/
lemma Box.isBounded {d:ℕ} (B: Box d) : Bornology.IsBounded B.toSet := by
  unfold Box.toSet
  apply Bornology.IsBounded.pi
  intro i
  exact BoundedInterval.isBounded (B.side i)

/-- Enlarge a box to an open box with controlled volume increase -/
lemma Box.inflate {d:ℕ} (B: Box d) (δ: ℝ) (hδ: 0 < δ) :
    ∃ B': Box d, B.toSet ⊆ interior B'.toSet ∧ IsOpen (interior B'.toSet) ∧ |B'|ᵥ ≤ |B|ᵥ + δ := by
  -- Handle dimension 0 separately (trivial case)
  by_cases hd : d = 0
  · subst hd
    -- In dimension 0, any box works - volume is always 1 (empty product)
    use B
    refine ⟨?_, isOpen_interior, by linarith⟩
    -- B.toSet ⊆ interior B.toSet: in dim 0, B.toSet = Set.univ which is open
    have hB_univ : B.toSet = Set.univ := by
      rw [Box.toSet, ← Set.empty_pi (fun i => (B.side i).toSet)]
      congr 1; ext i; exact Fin.elim0 i
    rw [hB_univ, interior_univ]
  -- Dimension d > 0: use continuity argument to find small enough ε
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- Define the expanded volume function f(ε) = ∏ᵢ (Lᵢ + 2ε)
  let f : ℝ → ℝ := fun ε => ∏ i : Fin d, (|B.side i|ₗ + 2 * ε)
  -- f is continuous
  have hf_cont : Continuous f := by
    apply continuous_finset_prod
    intro i _
    exact (continuous_const.add (continuous_const.mul continuous_id))
  -- f(0) = |B|ᵥ
  have hf_zero : f 0 = |B|ᵥ := by simp only [f, mul_zero, add_zero, Box.volume]
  -- By continuity at 0, there exists ε > 0 such that f(ε) < |B|ᵥ + δ
  have hf_cont_at : ContinuousAt f 0 := hf_cont.continuousAt
  rw [Metric.continuousAt_iff] at hf_cont_at
  obtain ⟨ε', hε'_pos, hε'_bound⟩ := hf_cont_at δ hδ
  -- Take ε = ε'/2 > 0 to ensure we're well within the δ-ball
  let ε := ε' / 2
  have hε_pos : 0 < ε := by positivity
  have hε_lt : ε < ε' := by simp only [ε]; nlinarith [hε'_pos]
  -- Construct the inflated box with Ioo intervals
  let B' : Box d := ⟨fun i => BoundedInterval.Ioo ((B.side i).a - ε) ((B.side i).b + ε)⟩
  use B'
  constructor
  · -- Prove B.toSet ⊆ interior B'.toSet
    -- First show B'.toSet is open (product of open intervals)
    have hB'_open : IsOpen B'.toSet := by
      rw [Box.toSet]
      apply isOpen_set_pi (Set.finite_univ)
      intro i _
      simp only [B', BoundedInterval.toSet]
      exact isOpen_Ioo
    -- So interior B'.toSet = B'.toSet
    rw [hB'_open.interior_eq]
    -- Now show B.toSet ⊆ B'.toSet
    intro x hx
    rw [Box.toSet, Set.mem_pi] at hx ⊢
    intro i _
    simp only [B', BoundedInterval.toSet, Set.mem_Ioo, BoundedInterval.a, BoundedInterval.b]
    -- Get hx for this specific index i after the case split
    cases hside : (B.side i) with
    | Ioo a b =>
      have hxi := hx i (Set.mem_univ i)
      simp only [BoundedInterval.toSet, hside, Set.mem_Ioo, BoundedInterval.a, BoundedInterval.b] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Icc a b =>
      have hxi := hx i (Set.mem_univ i)
      simp only [BoundedInterval.toSet, hside, Set.mem_Icc, BoundedInterval.a, BoundedInterval.b] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Ioc a b =>
      have hxi := hx i (Set.mem_univ i)
      simp only [BoundedInterval.toSet, hside, Set.mem_Ioc, BoundedInterval.a, BoundedInterval.b] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Ico a b =>
      have hxi := hx i (Set.mem_univ i)
      simp only [BoundedInterval.toSet, hside, Set.mem_Ico, BoundedInterval.a, BoundedInterval.b] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
  constructor
  · -- IsOpen (interior B'.toSet) is trivially true
    exact isOpen_interior
  · -- Prove |B'|ᵥ ≤ |B|ᵥ + δ
    -- |B'|ᵥ = ∏ᵢ |B'.side i|ₗ ≤ ∏ᵢ (|B.side i|ₗ + 2ε) = f(ε)
    have hB'_vol_le : |B'|ᵥ ≤ f ε := by
      simp only [Box.volume, f, B']
      apply Finset.prod_le_prod
      · intro i _; exact BoundedInterval.length_nonneg _
      · intro i _
        simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
        -- Need: max(b + ε - (a - ε), 0) ≤ max(b - a, 0) + 2ε
        have h_ineq : ∀ (a b : ℝ), max (b + ε - (a - ε)) 0 ≤ max (b - a) 0 + 2 * ε := by
          intro a b
          have h1 : b + ε - (a - ε) = b - a + 2 * ε := by ring
          rw [h1]
          by_cases hab : b ≥ a
          · have h2 : max (b - a) 0 = b - a := max_eq_left (by linarith : 0 ≤ b - a)
            have h3 : max (b - a + 2 * ε) 0 = b - a + 2 * ε := max_eq_left (by linarith)
            rw [h2, h3]
          · push_neg at hab
            have h2 : max (b - a) 0 = 0 := max_eq_right (by linarith : b - a ≤ 0)
            rw [h2, zero_add]
            exact max_le (by linarith) (by linarith)
        exact h_ineq (B.side i).a (B.side i).b
    calc |B'|ᵥ ≤ f ε := hB'_vol_le
         _ ≤ |B|ᵥ + δ := by
           -- Use continuity bound: |f(ε) - f(0)| < δ since |ε - 0| < ε'
           have hε_in_ball : dist ε 0 < ε' := by
             simp only [Real.dist_eq, sub_zero, abs_of_pos hε_pos]
             exact hε_lt
           have h_dist := hε'_bound hε_in_ball
           rw [Real.dist_eq, hf_zero] at h_dist
           have h_abs := abs_sub_lt_iff.mp h_dist
           linarith

/-- Shrink a box to a closed sub-box with controlled volume decrease.
    The output is always nonempty when the input is nonempty. -/
lemma Box.shrink_to_closed {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (δ: ℝ) (hδ: 0 < δ) :
    ∃ B': Box d, B'.toSet ⊆ B.toSet ∧ IsClosed B'.toSet ∧ |B'|ᵥ ≥ |B|ᵥ - δ ∧ B'.toSet.Nonempty := by
  -- Handle dimension 0 separately (trivial case)
  by_cases hd : d = 0
  · subst hd
    use B
    have h_closed : IsClosed B.toSet := by
      have : B.toSet = Set.univ := by
        rw [Box.toSet, ← Set.empty_pi (fun i => (B.side i).toSet)]
        congr 1; ext i; exact Fin.elim0 i
      rw [this]; exact isClosed_univ
    exact ⟨Set.Subset.refl _, h_closed, by linarith, hB⟩
  -- Dimension d > 0
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  have h_sides_nonempty : ∀ i : Fin d, (B.side i).toSet.Nonempty :=
    fun i => Box.side_nonempty_of_nonempty B hB i
  -- Check if all sides have strictly positive length
  by_cases h_all_pos : ∀ i : Fin d, 0 < |B.side i|ₗ
  · -- Non-degenerate case: all sides have positive length
    -- Define shrunken volume function g(ε) = ∏ᵢ max(Lᵢ - 2ε, 0)
    let g : ℝ → ℝ := fun ε => ∏ i : Fin d, max (|B.side i|ₗ - 2 * ε) 0
    -- g is continuous (max ∘ (f, g) is continuous when f, g are)
    have hg_cont : Continuous g := by
      apply continuous_finset_prod
      intro i _
      apply Continuous.max
      · exact continuous_const.sub (continuous_const.mul continuous_id)
      · exact continuous_const
    have hg_zero : g 0 = |B|ᵥ := by
      simp only [g, mul_zero, sub_zero, Box.volume]
      congr 1; ext i
      exact max_eq_left (BoundedInterval.length_nonneg _)
    -- By continuity, ∃ ε > 0 with g(ε) close to g(0)
    have hg_cont_at : ContinuousAt g 0 := hg_cont.continuousAt
    rw [Metric.continuousAt_iff] at hg_cont_at
    obtain ⟨ε', hε'_pos, hε'_bound⟩ := hg_cont_at δ hδ
    -- Find minimum side length
    let lengths : Finset ℝ := Finset.univ.image (fun i => |B.side i|ₗ)
    have hne_lengths : lengths.Nonempty := by
      simp only [lengths, Finset.image_nonempty]
      exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hd_pos⟩⟩
    let L := lengths.min' hne_lengths
    have hL_pos : 0 < L := by
      have : L ∈ lengths := Finset.min'_mem _ _
      simp only [lengths, Finset.mem_image, Finset.mem_univ, true_and] at this
      obtain ⟨i, hi⟩ := this
      rw [←hi]; exact h_all_pos i
    have hL_bound : ∀ i : Fin d, L ≤ |B.side i|ₗ := fun i =>
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    -- Take ε = min(ε'/2, L/4)
    let ε := min (ε' / 2) (L / 4)
    have hε_pos : 0 < ε := by positivity
    have hε_lt_half : ε < ε' := by
      calc ε ≤ ε' / 2 := min_le_left _ _
           _ < ε' := by linarith
    have hε_lt_L : ε < L / 2 := by
      calc ε ≤ L / 4 := min_le_right _ _
           _ < L / 2 := by linarith
    -- Construct shrunken box
    let B' : Box d := ⟨fun i => BoundedInterval.Icc ((B.side i).a + ε) ((B.side i).b - ε)⟩
    use B'
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- B'.toSet ⊆ B.toSet
      -- Strategy: Icc (a+ε) (b-ε) ⊆ Ioo a b ⊆ (B.side i).toSet
      intro x hx
      rw [Box.toSet, Set.mem_pi] at hx ⊢
      intro i _; specialize hx i (Set.mem_univ i)
      simp only [B', BoundedInterval.toSet, Set.mem_Icc] at hx
      have hne := h_sides_nonempty i
      have hε_small : 2 * ε < |B.side i|ₗ := by
        calc 2 * ε < 2 * (L / 2) := by linarith [hε_lt_L]
             _ = L := by ring
             _ ≤ |B.side i|ₗ := hL_bound i
      -- Show x i ∈ (B.side i).toSet using case analysis on the interval type
      have h_len_pos := h_all_pos i
      simp only [BoundedInterval.length] at h_len_pos hε_small
      have h_max : max ((B.side i).b - (B.side i).a) 0 = (B.side i).b - (B.side i).a := by
        apply max_eq_left; linarith
      rw [h_max] at h_len_pos hε_small
      -- x i ∈ Icc (a+ε) (b-ε), which is strictly inside any interval [a,b] variant
      cases hside : (B.side i) with
      | Ioo a b =>
        simp only [BoundedInterval.toSet, Set.mem_Ioo, hside, BoundedInterval.a, BoundedInterval.b] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      | Icc a b =>
        simp only [BoundedInterval.toSet, Set.mem_Icc, hside, BoundedInterval.a, BoundedInterval.b] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      | Ioc a b =>
        simp only [BoundedInterval.toSet, Set.mem_Ioc, hside, BoundedInterval.a, BoundedInterval.b] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      | Ico a b =>
        simp only [BoundedInterval.toSet, Set.mem_Ico, hside, BoundedInterval.a, BoundedInterval.b] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · -- IsClosed B'.toSet
      rw [Box.toSet]; apply isClosed_set_pi; intro i _
      simp only [B', BoundedInterval.toSet]; exact isClosed_Icc
    · -- Volume bound
      have hB'_vol : |B'|ᵥ = g ε := by
        simp only [Box.volume, g, B']; congr 1; ext i
        simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
        -- Both sides now have the same match expressions; use congr to unify
        have h_len := hL_bound i
        have h_pos_len : |B.side i|ₗ - 2 * ε > 0 := by
          calc |B.side i|ₗ - 2 * ε ≥ L - 2 * ε := by linarith
               _ > L - 2 * (L / 2) := by linarith [hε_lt_L]
               _ = 0 := by ring
        have h_ab : (B.side i).a ≤ (B.side i).b := by
          have := h_all_pos i
          simp only [BoundedInterval.length] at this
          by_contra h_neg; push_neg at h_neg
          have : max ((B.side i).b - (B.side i).a) 0 = 0 := max_eq_right (by linarith)
          linarith
        simp only [BoundedInterval.length] at h_pos_len
        have h_max : max ((B.side i).b - (B.side i).a) 0 = (B.side i).b - (B.side i).a := max_eq_left (by linarith)
        rw [h_max] at h_pos_len
        -- Goal: max (b - ε - (a + ε)) 0 = max (max (b - a) 0 - 2 * ε) 0
        -- First simplify RHS using h_max
        conv_rhs => rw [h_max]
        -- Now goal is: max (b - ε - (a + ε)) 0 = max (b - a - 2 * ε) 0
        -- The inner expressions are equal by ring
        congr 1
        ring
      rw [hB'_vol]
      have hε_in_ball : dist ε 0 < ε' := by simp only [Real.dist_eq, sub_zero, abs_of_pos hε_pos]; exact hε_lt_half
      have h_dist := hε'_bound hε_in_ball
      rw [Real.dist_eq, hg_zero] at h_dist
      have h_abs := abs_sub_lt_iff.mp h_dist
      linarith
    · -- B'.toSet.Nonempty (non-degenerate case)
      -- The shrunk box has sides [a+ε, b-ε] where 2ε < L (min side length)
      -- So a+ε < b-ε for each side, making each coordinate interval nonempty
      -- Product of nonempty sets is nonempty
      rw [Box.toSet]
      apply Set.pi_nonempty_iff.mpr
      intro i
      simp only [B', BoundedInterval.toSet, Set.mem_univ, true_implies]
      rw [← Set.nonempty_def, Set.nonempty_Icc]
      -- Need: (B.side i).a + ε ≤ (B.side i).b - ε, i.e., 2ε ≤ (B.side i).b - (B.side i).a
      have h_side_pos := h_all_pos i
      simp only [BoundedInterval.length] at h_side_pos
      have h_ab : (B.side i).a ≤ (B.side i).b := by
        by_contra h_neg; push_neg at h_neg
        have : max ((B.side i).b - (B.side i).a) 0 = 0 := max_eq_right (by linarith)
        linarith
      have h_max : max ((B.side i).b - (B.side i).a) 0 = (B.side i).b - (B.side i).a := max_eq_left (by linarith)
      rw [h_max] at h_side_pos
      have h_2ε_lt : 2 * ε < (B.side i).b - (B.side i).a := by
        calc 2 * ε < 2 * (L / 2) := by linarith [hε_lt_L]
             _ = L := by ring
             _ ≤ |B.side i|ₗ := hL_bound i
             _ = (B.side i).b - (B.side i).a := by simp only [BoundedInterval.length, h_max]
      linarith
  · -- Degenerate case: some side has zero length, volume is 0
    push_neg at h_all_pos
    obtain ⟨i₀, hi₀⟩ := h_all_pos
    have hvol_zero : |B|ᵥ = 0 := by
      simp only [Box.volume]
      apply Finset.prod_eq_zero (Finset.mem_univ i₀)
      have h := BoundedInterval.length_nonneg (B.side i₀); linarith
    obtain ⟨x, hx⟩ := hB
    let B' : Box d := ⟨fun i => BoundedInterval.Icc (x i) (x i)⟩
    use B'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      rw [Box.toSet, Set.mem_pi] at hy hx ⊢
      intro i _
      specialize hy i (Set.mem_univ i)
      specialize hx i (Set.mem_univ i)
      simp only [B', BoundedInterval.toSet, Set.mem_Icc] at hy
      have heq : y i = x i := le_antisymm hy.2 hy.1
      rw [heq]; exact hx
    · rw [Box.toSet]; apply isClosed_set_pi; intro i _
      simp only [B', BoundedInterval.toSet]; exact isClosed_Icc
    · have hvol' : |B'|ᵥ = 0 := by
        simp only [Box.volume, B']
        have h0 : (⟨0, hd_pos⟩ : Fin d) ∈ Finset.univ := Finset.mem_univ _
        apply Finset.prod_eq_zero h0
        simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b, sub_self]
        exact max_eq_right (le_refl 0)
      rw [hvol', hvol_zero]; linarith
    · -- B'.toSet.Nonempty (degenerate case): B' = {x} is a singleton containing x
      use x
      rw [Box.toSet, Set.mem_pi]
      intro i _
      simp only [B', BoundedInterval.toSet, Set.mem_Icc, le_refl, and_self]

namespace IsElementary
/-- Elementary sets are bounded (finite union of bounded boxes) -/
lemma isBounded {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) :
    Bornology.IsBounded E := by
  obtain ⟨S, hS_eq⟩ := hE
  rw [hS_eq]
  rw [Bornology.isBounded_biUnion_finset]
  intro B _
  exact Box.isBounded B

/-- Elementary measure of empty set is zero (handles proof term mismatch) -/
lemma measure_of_empty_eq {d : ℕ} {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) (hempty : E = ∅) : hE.measure = 0 := by
  have : hE.measure = (IsElementary.empty d).measure :=
    IsElementary.measure_eq_of_set_eq hE (IsElementary.empty d) hempty
  rw [this, IsElementary.measure_of_empty]


/-- Finite indexed union of boxes is elementary (uses IsElementary.union' which takes a finset of sets) -/
lemma iUnion_boxes {d : ℕ} {ι : Type*} [Fintype ι] (B : ι → Box d) :
    IsElementary (⋃ i, (B i).toSet) := by
  classical
  -- Convert indexed union to finset-based union
  let S : Finset (Set (EuclideanSpace' d)) := Finset.univ.image (fun i => (B i).toSet)
  have hS_elem : ∀ E ∈ S, IsElementary E := by
    intro E hE
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hE
    obtain ⟨i, rfl⟩ := hE
    exact IsElementary.box (B i)
  have h_eq : ⋃ i, (B i).toSet = ⋃ E ∈ S, E := by
    ext x
    simp only [S, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ⟨i, hi⟩; exact ⟨(B i).toSet, ⟨i, rfl⟩, hi⟩
    · intro ⟨_, ⟨i, rfl⟩, hi⟩; exact ⟨i, hi⟩
  rw [h_eq]
  exact IsElementary.union' hS_elem

/-- The measure of a finite union of boxes (indexed by finset membership) is at most the sum of volumes.
    This is finite subadditivity specialized to boxes with a finset index. -/
lemma measure_le_finset_boxes_volume' {d : ℕ} (t : Finset ℕ) (B : ℕ → Box d) :
    (IsElementary.iUnion_boxes (fun (n : { n // n ∈ t }) => B n.1)).measure ≤ ∑ n ∈ t, (B n).volume := by
  classical
  -- Convert to the Finset of sets form and use IsElementary.measure_of_union'
  haveI : DecidableEq (Set (EuclideanSpace' d)) := Classical.decEq _
  let S_sets : Finset (Set (EuclideanSpace' d)) := t.image (fun n => (B n).toSet)
  have hS_elem : ∀ E ∈ S_sets, IsElementary E := by
    intro E hE
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hE
    exact IsElementary.box (B n)
  -- The subtype union equals the union over S_sets
  have h_union_eq : ⋃ (n : { n // n ∈ t }), (B n.1).toSet = ⋃ E ∈ S_sets, E := by
    ext x
    simp only [Set.mem_iUnion, S_sets]
    constructor
    · intro ⟨⟨n, hn⟩, hx⟩
      exact ⟨(B n).toSet, Finset.mem_image.mpr ⟨n, hn, rfl⟩, hx⟩
    · intro ⟨E, hE_mem, hx⟩
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hE_mem
      exact ⟨⟨n, hn⟩, hx⟩
  -- Apply measure_eq_of_set_eq to link the elementary witnesses
  have h_measure_eq : (IsElementary.iUnion_boxes (fun (n : { n // n ∈ t }) => B n.1)).measure =
      (IsElementary.union' hS_elem).measure :=
    IsElementary.measure_eq_of_set_eq _ _ h_union_eq
  rw [h_measure_eq]
  -- Apply finite subadditivity from IsElementary.measure_of_union'
  have h_sub := IsElementary.measure_of_union' hS_elem
  -- Reindex the sum: need to show ∑ E : S_sets, (hS_elem E _).measure ≤ ∑ n ∈ t, (B n).volume
  calc (IsElementary.union' hS_elem).measure
      ≤ ∑ E : S_sets, (hS_elem E.val E.property).measure := h_sub
    _ ≤ ∑ n ∈ t, (B n).volume := by
        -- Each elementary measure = box volume, and S_sets.image is subset of t
        -- Use sum over image ≤ sum over domain
        have h_term_eq : ∀ (E : { E // E ∈ S_sets }),
            (hS_elem E.1 E.2).measure = (B (Finset.mem_image.mp E.2).choose).volume := by
          intro ⟨E, hE⟩
          -- choose_spec gives (choose ∈ t ∧ (B choose).toSet = E)
          have h_spec := (Finset.mem_image.mp hE).choose_spec
          let n := (Finset.mem_image.mp hE).choose
          have h_eq : (B n).toSet = E := h_spec.2
          have hB_elem := IsElementary.box (B n)
          have hE_eq : E = (B n).toSet := h_eq.symm
          -- Goal: (hS_elem E hE).measure = (B n).volume
          rw [IsElementary.measure_eq_of_set_eq (hS_elem E hE) hB_elem hE_eq]
          rw [IsElementary.measure_of_box (B n)]
        -- The preimages are a subset of t, so sum ≤ sum over t
        -- Build preimage function: for each E ∈ S_sets, pick n ∈ t such that (B n).toSet = E
        let f : { E // E ∈ S_sets } → ℕ := fun E => (Finset.mem_image.mp E.2).choose
        have hf_mem : ∀ E, f E ∈ t := fun ⟨E, hE⟩ =>
          (Finset.mem_image.mp hE).choose_spec.1
        have hf_eq : ∀ E, (B (f E)).toSet = E.1 := fun ⟨E, hE⟩ =>
          (Finset.mem_image.mp hE).choose_spec.2
        -- Show that f is injective (different sets → different indices via chosen representatives)
        have hf_inj : Function.Injective f := by
          intro ⟨E₁, hE₁⟩ ⟨E₂, hE₂⟩ h_eq
          apply Subtype.ext
          calc E₁ = (B (f ⟨E₁, hE₁⟩)).toSet := (hf_eq ⟨E₁, hE₁⟩).symm
            _ = (B (f ⟨E₂, hE₂⟩)).toSet := by rw [h_eq]
            _ = E₂ := hf_eq ⟨E₂, hE₂⟩
        -- The image of f is a subset of t
        have h_image_sub : (Finset.univ : Finset { E // E ∈ S_sets }).image f ⊆ t := by
          intro n hn
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hn
          obtain ⟨E, rfl⟩ := hn
          exact hf_mem E
        -- Use Finset.sum_image with injectivity
        calc ∑ E : S_sets, (hS_elem E.val E.property).measure
            = ∑ E : S_sets, (B (f E)).volume := Finset.sum_congr rfl (fun E _ => h_term_eq E)
          _ = ∑ n ∈ (Finset.univ : Finset { E // E ∈ S_sets }).image f, (B n).volume := by
              rw [Finset.sum_image (fun E₁ _ E₂ _ h => hf_inj h)]
          _ ≤ ∑ n ∈ t, (B n).volume :=
              Finset.sum_le_sum_of_subset_of_nonneg h_image_sub
                (fun n _ _ => Box.volume_nonneg (B n))

/-- For any box cover of an elementary set, the sum of volumes bounds the measure from below.
    This is the key step using Heine-Borel compactness: inflate boxes to open cover,
    extract finite subcover of compact approximation, use finite subadditivity. -/
lemma measure_le_cover_sum {d : ℕ} (_hd : 0 < d) {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) (S : ℕ → Box d) (hS_cover : E ⊆ ⋃ n, (S n).toSet) :
    (hE.measure : EReal) ≤ ∑' n, (S n).volume.toEReal := by
  -- Handle empty case directly
  by_cases hE_empty : E = ∅
  · rw [hE.measure_of_empty_eq hE_empty]
    simp only [EReal.coe_zero]
    positivity
  -- E is nonempty
  have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  -- Get partition of E
  obtain ⟨P, hP_disj, hP_eq⟩ := hE.partition
  have hP_nonempty : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hP_empty
    rw [hP_empty] at hP_eq
    simp at hP_eq
    exact hE_empty hP_eq
  -- Use ε-argument: show hE.measure ≤ ∑|S_n| + ε for all ε > 0
  apply EReal.le_of_forall_pos_le_add'
  intro δ hδ_pos
  have hδ4_pos : 0 < δ / 4 := by linarith
  -- Step 1: Inflate each S_n to open S'_n with controlled volume increase
  have h_inflate : ∀ n : ℕ, ∃ S'_n : Box d,
      (S n).toSet ⊆ interior S'_n.toSet ∧ IsOpen (interior S'_n.toSet) ∧
      S'_n.volume ≤ (S n).volume + δ / 2^(n+2) := by
    intro n
    exact Box.inflate (S n) (δ / 2^(n+2)) (by positivity)
  choose S' hS'_subset hS'_open hS'_vol using h_inflate
  -- Step 2: {interior (S' n)} is an open cover of E
  have h_open_cover : E ⊆ ⋃ n, interior (S' n).toSet := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hS_cover hx)
    exact Set.mem_iUnion.mpr ⟨n, hS'_subset n hn⟩
  -- Step 3: Shrink partition boxes to get compact approximation K
  have hcard_pos : 0 < P.card := Finset.card_pos.mpr hP_nonempty
  have h_shrink : ∀ B ∈ P, B.toSet.Nonempty → ∃ B' : Box d,
      B'.toSet ⊆ B.toSet ∧ IsClosed B'.toSet ∧ B'.volume ≥ B.volume - δ / (4 * P.card) ∧ B'.toSet.Nonempty := by
    intro B _ hB_nonempty
    exact Box.shrink_to_closed B hB_nonempty (δ / (4 * P.card)) (by positivity)
  -- Step 4: Build compact set K from shrunk partition boxes
  -- Filter to nonempty boxes (using classical decidability)
  haveI : DecidablePred (fun (B : Box d) => B.toSet.Nonempty) := Classical.decPred _
  let P_nonempty := P.filter (fun B => B.toSet.Nonempty)
  -- For each nonempty box in P, choose a closed shrunk box
  have h_shrink' : ∀ B ∈ P_nonempty, ∃ B' : Box d,
      B'.toSet ⊆ B.toSet ∧ IsClosed B'.toSet ∧ B'.volume ≥ B.volume - δ / (4 * P.card) ∧ B'.toSet.Nonempty := by
    intro B hB
    have hBP : B ∈ P := Finset.mem_filter.mp hB |>.1
    have hB_ne : B.toSet.Nonempty := Finset.mem_filter.mp hB |>.2
    exact h_shrink B hBP hB_ne
  choose B' hB'_sub hB'_closed hB'_vol hB'_nonempty using h_shrink'
  -- Define K directly as union of shrunk boxes over P_nonempty
  let K := ⋃ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).toSet
  -- Step 5: K is closed (finite union of closed sets)
  have hK_closed : IsClosed K := by
    show IsClosed (⋃ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).toSet)
    haveI : Finite { B // B ∈ P_nonempty } := Finset.finite_toSet P_nonempty |>.to_subtype
    apply isClosed_iUnion_of_finite
    intro ⟨B, hB⟩
    exact hB'_closed B hB
  -- Step 6: K is bounded (K ⊆ E which is bounded)
  have hK_subset_E : K ⊆ E := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨⟨B, hB⟩, hx_in_B'⟩ := hx
    have hBP : B ∈ P := Finset.mem_filter.mp hB |>.1
    rw [hP_eq]
    exact Set.mem_biUnion hBP (hB'_sub B hB hx_in_B')
  have hK_bounded : Bornology.IsBounded K := hE.isBounded.subset hK_subset_E
  -- Step 7: K is compact (Heine-Borel)
  have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bounded
  -- Step 8: K ⊆ ⋃ interior S'_n (since K ⊆ E ⊆ ⋃ interior S'_n)
  have hK_cover : K ⊆ ⋃ n, interior (S' n).toSet := hK_subset_E.trans h_open_cover
  -- Step 9: Apply Heine-Borel to get finite subcover
  obtain ⟨t, ht_cover⟩ := hK_compact.elim_finite_subcover
    (fun n => interior (S' n).toSet) (fun n => isOpen_interior) hK_cover
  -- Step 10: Volume calculation chain
  -- We have: K ⊆ ⋃ n ∈ t, interior (S' n).toSet ⊆ ⋃ n ∈ t, (S' n).toSet
  -- Strategy: hE.measure ≤ m(K) + δ/4 ≤ ∑_{n∈t} |S'_n| + δ/4 ≤ ∑_all |S_n| + δ
  -- Step 10a: m(E) ≤ m(K) + δ/4 (K approximates E with controlled volume loss)
  -- Each shrunk box B' has |B'| ≥ |B| - δ/(4*|P|), so total loss ≤ δ/4
  have h_K_approx : hE.measure ≤ ∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume + δ / 4 := by
    -- Strategy: hE.measure = ∑ B ∈ P, B.volume (via disjoint partition)
    -- For nonempty B: B.volume ≤ B'.volume + δ/(4*|P|)
    -- For empty B: B.volume = 0
    -- Sum: hE.measure ≤ ∑ B'.volume + |P_nonempty| * δ/(4*|P|) ≤ ∑ B'.volume + δ/4
    have hE_measure : hE.measure = ∑ B ∈ P, B.volume := hE.measure_eq hP_disj hP_eq
    -- Split P into nonempty and empty boxes
    have hP_split : P = P_nonempty ∪ (P.filter (fun B => ¬(B.toSet).Nonempty)) := by
      ext B; simp [P_nonempty]; tauto
    -- Empty boxes have volume 0
    have h_empty_vol : ∀ B ∈ P.filter (fun B => ¬(B.toSet).Nonempty), B.volume = 0 := by
      intro B hB
      simp only [Finset.mem_filter] at hB
      exact Box.volume_eq_zero_of_empty B (Set.not_nonempty_iff_eq_empty.mp hB.2)
    -- Sum over empty boxes is 0
    have h_empty_sum : ∑ B ∈ P.filter (fun B => ¬(B.toSet).Nonempty), B.volume = 0 := by
      exact Finset.sum_eq_zero h_empty_vol
    -- Rewrite sum over P
    have h_sum_split : ∑ B ∈ P, B.volume = ∑ B ∈ P_nonempty, B.volume + ∑ B ∈ P.filter (fun B => ¬(B.toSet).Nonempty), B.volume := by
      rw [← Finset.sum_union]
      · rw [← hP_split]
      · apply Finset.disjoint_left.2
        intro B hB₁ hB₂
        simp only [P_nonempty, Finset.mem_filter] at hB₁ hB₂
        exact hB₂.2 hB₁.2
    rw [hE_measure, h_sum_split, h_empty_sum, add_zero]
    -- For each nonempty B: B.volume ≤ B'.volume + δ/(4*|P|)
    have h_vol_bound : ∀ B (hB : B ∈ P_nonempty), B.volume ≤ (B' B hB).volume + δ / (4 * P.card) := by
      intro B hB; linarith [hB'_vol B hB]
    -- Use helper lemmas to bound the sum
    have hP_nonempty_sub : P_nonempty ⊆ P := Finset.filter_subset _ P
    have h_sum_bound := partition_volume_bound hP_nonempty_sub (by positivity : 0 < δ / (4 * P.card)) h_vol_bound
    have h_loss_bound := card_ratio_bound hP_nonempty_sub hδ_pos hcard_pos
    linarith [h_sum_bound, h_loss_bound]
  -- Step 10b: K is elementary (finite union of closed boxes)
  have hK_elem : IsElementary K := by
    exact IsElementary.iUnion_boxes (fun (x : { B // B ∈ P_nonempty }) => B' x.1 x.2)
  -- Step 10c: m(K) ≤ ∑_{n∈t} |S'_n| (K covered by finite boxes)
  have h_K_cover_bound : hK_elem.measure ≤ ∑ n ∈ t, (S' n).volume := by
    -- Build elementary set from union of covering boxes
    have hU_elem : IsElementary (⋃ (n : { n // n ∈ t }), (S' n.1).toSet) :=
      IsElementary.iUnion_boxes (fun (n : { n // n ∈ t }) => S' n.1)
    -- Show K ⊆ ⋃ n ∈ t, S'_n
    have hK_sub_U : K ⊆ ⋃ (n : { n // n ∈ t }), (S' n.1).toSet := by
      intro x hx
      obtain ⟨n, hn, hx_in⟩ := Set.mem_iUnion₂.mp (ht_cover hx)
      exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, interior_subset hx_in⟩
    -- Apply measure monotonicity and disjoint union formula
    calc hK_elem.measure
        ≤ hU_elem.measure := hK_elem.measure_mono hU_elem hK_sub_U
      _ ≤ ∑ n ∈ t, (S' n).volume := IsElementary.measure_le_finset_boxes_volume' t S'
  -- Step 10d: Finite sum ≤ infinite sum
  have h_finite_le_tsum : (∑ n ∈ t, (S' n).volume : EReal) ≤ ∑' n, (S' n).volume.toEReal := by
    -- For nonnegative terms, finite partial sum ≤ infinite sum
    exact EReal.finset_sum_le_tsum (fun n => Box.volume_nonneg (S' n)) t
  -- Step 10e: ∑_all |S'_n| ≤ ∑_all |S_n| + δ/2 (from hS'_vol)
  have h_inflate_bound : (∑' n, (S' n).volume.toEReal : EReal) ≤ ∑' n, (S n).volume.toEReal + δ / 2 := by
    -- Each |S'_n| ≤ |S_n| + δ/2^{n+2}, and ∑ δ/2^{n+2} = δ/2
    have h_pointwise : ∀ n, (S' n).volume.toEReal ≤ (S n).volume.toEReal + (δ / 2^(n+2) : ℝ) := by
      intro n
      have hvol := hS'_vol n
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe hvol
    -- Key: ∑' n, δ / 2^(n+2) = δ/2 (geometric series)
    have h_geom : ∑' n : ℕ, (δ / 2^(n+2) : ℝ) = δ / 2 := tsum_geometric_inflate hδ_pos
    -- EReal tsum arithmetic: route through ENNReal where tsum properties are cleaner
    -- Use EReal.tsum_add_le_of_nonneg_pointwise from our helper library
    -- We need: ∑' (S' n).vol.toEReal ≤ ∑' (S n).vol.toEReal + δ/2
    -- From h_pointwise: (S' n).vol ≤ (S n).vol + δ/2^(n+2)
    -- And h_geom: ∑' δ/2^(n+2) = δ/2
    -- Strategy: Apply tsum_add_le_of_nonneg_pointwise to get
    --   ∑' (S' n).vol + ∑' 0 ≤ ∑' ((S n).vol + δ/2^(n+2))
    -- Then decompose RHS using tsum properties
    have h_S'_nonneg : ∀ n, 0 ≤ (S' n).volume := fun n => Box.volume_nonneg (S' n)
    have h_S_nonneg : ∀ n, 0 ≤ (S n).volume := fun n => Box.volume_nonneg (S n)
    have h_geom_nonneg : ∀ n, (0 : ℝ) ≤ δ / 2^(n+2) := fun n => by positivity
    -- Use the helper lemma with f = S'.vol, g = 0 (trivially), h = S.vol + δ/2^{n+2}
    have h_bound : (∑' n : ℕ, (S' n).volume.toEReal) + (∑' n : ℕ, (0 : ℝ).toEReal) ≤
        ∑' n : ℕ, ((S n).volume + δ / 2^(n+2)).toEReal := by
      apply EReal.tsum_add_le_of_nonneg_pointwise h_S'_nonneg (fun _ => le_refl 0)
      intro n; simp only [add_zero]; exact hS'_vol n
    simp only [EReal.coe_zero, tsum_zero, add_zero] at h_bound
    -- Now show: ∑' ((S n).vol + δ/2^{n+2}).toEReal ≤ ∑' (S n).vol.toEReal + δ/2
    have h_rhs_bound : (∑' n : ℕ, ((S n).volume + δ / 2^(n+2)).toEReal) ≤
        ∑' n : ℕ, (S n).volume.toEReal + (δ / 2 : ℝ) := by
      -- Route through ENNReal where tsum_add works cleanly
      let f : ℕ → ENNReal := fun n => ENNReal.ofReal ((S n).volume)
      let g : ℕ → ENNReal := fun n => ENNReal.ofReal (δ / 2^(n+2))
      have h_f_eq : ∀ n, (f n).toEReal = (S n).volume.toEReal := fun n => by
        simp only [f, EReal.coe_ennreal_ofReal, max_eq_left (h_S_nonneg n)]
      have h_g_eq : ∀ n, (g n).toEReal = (δ / 2^(n+2) : ℝ).toEReal := fun n => by
        simp only [g, EReal.coe_ennreal_ofReal, max_eq_left (h_geom_nonneg n)]
      have h_fg_eq : ∀ n, ((S n).volume + δ / 2^(n+2)).toEReal = (f n + g n).toEReal := fun n => by
        simp only [EReal.coe_ennreal_add, h_f_eq, h_g_eq]
        rw [← EReal.coe_add]
      -- Rewrite LHS
      conv_lhs => congr; ext n; rw [h_fg_eq]
      -- Use ENNReal tsum properties via coercion
      have h_sum_fg : (∑' n, (f n + g n).toEReal) = (∑' n, (f n).toEReal) + (∑' n, (g n).toEReal) := by
        rw [← EReal.tsum_add_coe_ennreal]
      rw [h_sum_fg]
      -- Now show ∑' (f n).toEReal = ∑' (S n).vol.toEReal
      have h_lhs_eq : ∑' n, (f n).toEReal = ∑' n, (S n).volume.toEReal := tsum_congr h_f_eq
      -- And ∑' (g n).toEReal = (δ/2).toEReal
      have h_rhs_eq : (∑' n, (g n).toEReal) = (δ / 2 : ℝ).toEReal := by
        conv_lhs => congr; ext n; rw [h_g_eq]
        -- Need: ∑' n, (δ/2^(n+2)).toEReal = (δ/2).toEReal
        -- Since all terms are nonneg and we have h_geom summability
        have h_geom_summable : Summable (fun n => δ / 2^(n+2) : ℕ → ℝ) := by
          have : Summable (fun n => δ / 4 * (1/2 : ℝ)^n) :=
            Summable.mul_left (δ / 4) (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))
          refine Summable.congr this ?_
          intro n; field_simp; ring_nf
          left; trivial
        rw [← h_geom]
        -- Convert: ∑' real.toEReal = (∑' real).toEReal for summable nonneg
        symm
        -- Use Summable.map_tsum to show coercion commutes with tsum
        let φ : ℝ →+ EReal := {
          toFun := (↑·)
          map_zero' := EReal.coe_zero
          map_add' := fun x y => EReal.coe_add x y
        }
        have h_cont : Continuous φ := continuous_coe_real_ereal
        have h_map := Summable.map_tsum h_geom_summable φ h_cont
        -- h_map: φ (∑' (i : ℕ), δ / 2 ^ (i + 2)) = ∑' (i : ℕ), φ (δ / 2 ^ (i + 2))
        -- Since φ = (↑·), this is: ↑(∑' (i : ℕ), δ / 2 ^ (i + 2)) = ∑' (i : ℕ), ↑(δ / 2 ^ (i + 2))
        -- Goal: ↑(∑' (n : ℕ), δ / 2 ^ (n + 2)) = ∑' (n : ℕ), ↑(δ / 2 ^ (n + 2))
        -- Rewrite both sides to use φ, then apply h_map.symm and match variable names
        -- Since φ = (↑·), we can use h_map.symm after matching variable names
        have h_eq_lhs : ↑(∑' (n : ℕ), δ / 2 ^ (n + 2)) = φ (∑' (n : ℕ), δ / 2 ^ (n + 2)) := by
          congr 1
        have h_eq_rhs : ∑' (n : ℕ), ↑(δ / 2 ^ (n + 2)) = ∑' (n : ℕ), φ (δ / 2 ^ (n + 2)) :=
          tsum_congr (fun n => rfl)
        rw [h_eq_lhs, h_eq_rhs, ← h_map.symm]
      rw [h_lhs_eq, h_rhs_eq]
    exact le_trans h_bound h_rhs_bound
  -- Combine the bounds: work entirely in EReal
  -- Step: m(E) ≤ sum of shrunk B' volumes + δ/4
  have h_step1 : (hE.measure : EReal) ≤ ((∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume) + δ / 4 : ℝ) := by
    exact_mod_cast h_K_approx
  -- Step: sum of B' ≤ m(K) (when K = ⋃ B')
  have h_step2 : (∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume : EReal) ≤ (hK_elem.measure : EReal) := by
    -- K = ⋃ B' is a disjoint union (since B' ⊆ B and original B are disjoint)
    -- For disjoint unions: m(K) = ∑ |B'|, so we have equality
    -- The B' boxes form a disjoint partition of K
    have h_B'_disj : (Finset.univ : Finset { B // B ∈ P_nonempty }).toSet.PairwiseDisjoint
        (fun x => (B' x.1 x.2).toSet) := by
      intro ⟨B₁, hB₁⟩ _ ⟨B₂, hB₂⟩ _ hne
      have hB₁P : B₁ ∈ P := Finset.mem_filter.mp hB₁ |>.1
      have hB₂P : B₂ ∈ P := Finset.mem_filter.mp hB₂ |>.1
      have h_orig_disj := hP_disj hB₁P hB₂P (by
        intro h_eq
        apply hne
        cases h_eq
        rfl)
      exact Set.disjoint_of_subset (hB'_sub B₁ hB₁) (hB'_sub B₂ hB₂) h_orig_disj
    -- Build finset of B' boxes
    let T := Finset.univ.image (fun (x : { B // B ∈ P_nonempty }) => B' x.1 x.2)
    -- Show T is pairwise disjoint
    have hT_disj : T.toSet.PairwiseDisjoint Box.toSet := by
      intro box₁ hbox₁ box₂ hbox₂ hne
      simp only [T, Finset.mem_coe, Finset.mem_image] at hbox₁ hbox₂
      obtain ⟨⟨B₁, hB₁⟩, _, rfl⟩ := hbox₁
      obtain ⟨⟨B₂, hB₂⟩, _, rfl⟩ := hbox₂
      have hB₁P : B₁ ∈ P := Finset.mem_filter.mp hB₁ |>.1
      have hB₂P : B₂ ∈ P := Finset.mem_filter.mp hB₂ |>.1
      have h_disj_orig : Disjoint B₁.toSet B₂.toSet := hP_disj hB₁P hB₂P (by
        intro h_eq
        apply hne
        simp only [h_eq])
      exact Set.disjoint_of_subset (hB'_sub B₁ hB₁) (hB'_sub B₂ hB₂) h_disj_orig
    -- Show K = ⋃ B ∈ T
    have hK_eq : K = ⋃ box ∈ T, box.toSet := by
      simp only [K, T]
      ext x
      simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and, exists_prop]
      refine ⟨fun ⟨⟨B, hB⟩, hx⟩ => ?_, fun ⟨_, ⟨⟨B, hB⟩, rfl⟩, hx⟩ => ?_⟩
      · exact ⟨B' B hB, ⟨⟨B, hB⟩, rfl⟩, hx⟩
      · exact ⟨⟨B, hB⟩, hx⟩
    -- Apply IsElementary.measure_eq
    have h_measure_eq := hK_elem.measure_eq hT_disj hK_eq
    -- Convert to desired inequality
    rw [h_measure_eq]
    -- B' is injective because B' boxes are subsets of pairwise disjoint original boxes
    have hP_nonempty_sub : P_nonempty ⊆ P := Finset.filter_subset _ P
    have h_B'_inj : Function.Injective (fun x : { B // B ∈ P_nonempty } => B' x.1 x.2) :=
      injective_of_shrunk_nonempty hP_nonempty_sub hP_disj hB'_sub hB'_nonempty
    -- Now use sum_image with injectivity
    have h_sum_eq : ∑ B ∈ T, B.volume = ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume := by
      simp only [T]
      rw [Finset.sum_image (fun x _ y _ h => h_B'_inj h)]
    rw [h_sum_eq]
    -- Convert finset sum to EReal using coe_finset_sum (volumes are nonnegative)
    have h_vol_nonneg : ∀ x : { B // B ∈ P_nonempty }, 0 ≤ (B' x.1 x.2).volume := fun x => Box.volume_nonneg _
    rw [← EReal.coe_finset_sum (fun x _ => h_vol_nonneg x)]
  -- Step: m(K) ≤ ∑_{n∈t} |S'_n|
  have h_step3 : (hK_elem.measure : EReal) ≤ (∑ n ∈ t, (S' n).volume : ℝ) := by
    exact_mod_cast h_K_cover_bound
  -- Step: finite sum ≤ tsum (h_finite_le_tsum already has matching types)
  have h_step4 : (∑ n ∈ t, (S' n).volume.toEReal) ≤ ∑' n, (S' n).volume.toEReal :=
    h_finite_le_tsum
  -- Final chain: m(E) ≤ ∑ B' + δ/4 ≤ m(K) + δ/4 ≤ ∑_{n∈t} S'_n + δ/4
  --              ≤ ∑'_n S'_n + δ/4 ≤ ∑'_n S_n + δ/2 + δ/4 ≤ ∑'_n S_n + δ
  -- First, convert h_step1 to separate the sum and δ/4 parts
  have h_sum_B'_nonneg : 0 ≤ ∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume :=
    Finset.sum_nonneg (fun x _ => Box.volume_nonneg _)
  have h_vol_nonneg' : ∀ x : { B // B ∈ P_nonempty }, 0 ≤ (B' x.1 x.2).volume := fun x => Box.volume_nonneg _
  have h_coe_sum : (∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume : EReal) =
      ∑ (x : { B // B ∈ P_nonempty }), ((B' x.1 x.2).volume : EReal) := rfl
  -- Chain: m(E) ≤ ∑ B' + δ/4 ≤ m(K) + δ/4 ≤ ∑_{t} S' + δ/4 ≤ ∑' S' + δ/4 ≤ ∑' S + δ/2 + δ/4
  calc (hE.measure : EReal)
      ≤ ((∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume) + δ / 4 : ℝ) := h_step1
    _ = (∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume : EReal) + (δ / 4 : ℝ) := by
        rw [EReal.coe_add (∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume) (δ / 4)]
        congr 1
        rw [EReal.coe_finset_sum (fun x _ => h_vol_nonneg' x)]
    _ ≤ (hK_elem.measure : EReal) + (δ / 4 : ℝ) := by
        apply add_le_add_right
        rw [h_coe_sum]
        exact h_step2
    _ ≤ (∑ n ∈ t, (S' n).volume : ℝ) + (δ / 4 : ℝ) := by
        apply add_le_add_right h_step3
    _ = (∑ n ∈ t, ((S' n).volume : EReal)) + (δ / 4 : ℝ) := by
        congr 1
        rw [EReal.coe_finset_sum (fun n _ => Box.volume_nonneg _)]
    _ ≤ (∑' n, (S' n).volume : EReal) + (δ / 4 : ℝ) := by
        apply add_le_add_right
        exact h_step4
    _ ≤ (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) + (δ / 4 : ℝ) := by
        have h1 : (∑' n, (S' n).volume : EReal) ≤ (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) := h_inflate_bound
        calc (∑' n, (S' n).volume : EReal) + (δ / 4 : ℝ)
            ≤ ((∑' n, (S n).volume : EReal) + (δ / 2 : ℝ)) + (δ / 4 : ℝ) := add_le_add_right h1 _
          _ = (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) + (δ / 4 : ℝ) := rfl
    _ = (∑' n, (S n).volume : EReal) + ((δ / 2 : ℝ) + (δ / 4 : ℝ)) := by rw [add_assoc]
    _ = (∑' n, (S n).volume : EReal) + (3 * δ / 4 : ℝ) := by
        congr 1
        rw [← EReal.coe_add (δ / 2) (δ / 4)]
        congr 1
        ring
    _ ≤ (∑' n, (S n).volume : EReal) + (δ : ℝ) := by
        apply add_le_add_left
        exact_mod_cast (by linarith : (3 * δ / 4 : ℝ) ≤ δ)

/-- Direction 1: Elementary measure is a lower bound for outer measure
    (Partition gives a finite cover, outer measure is infimum over covers)
    Uses measure_le_cover_sum for the core Heine-Borel argument. -/
lemma measure_le_outer_measure {d:ℕ} (hd: 0 < d) {E: Set (EuclideanSpace' d)}
    (hE: IsElementary E) : (hE.measure : EReal) ≤ Lebesgue_outer_measure E := by
  -- Use ε-argument: show ∀ ε > 0, hE.measure ≤ m*(E) + ε
  apply EReal.le_of_forall_pos_le_add'
  intro ε hε_pos
  -- E has finite outer measure (bounded by elementary measure via Jordan)
  have h_finite : Lebesgue_outer_measure E ≠ ⊤ := by
    have h1 : Lebesgue_outer_measure E ≤ (Jordan_outer_measure E : EReal) :=
      Lebesgue_outer_measure_le_Jordan hE.isBounded
    have h2 : Jordan_outer_measure E ≤ hE.measure := Jordan_outer_le hE (Set.Subset.refl E)
    have h3 : Lebesgue_outer_measure E ≤ (hE.measure : EReal) := calc Lebesgue_outer_measure E
        ≤ (Jordan_outer_measure E : EReal) := h1
      _ ≤ (hE.measure : EReal) := by exact_mod_cast h2
    exact ne_top_of_le_ne_top (EReal.coe_ne_top hE.measure) h3
  -- Get ε/2-close cover
  have hε2_pos : 0 < ε / 2 := by linarith
  obtain ⟨S, hS_cover, hS_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd E (ε / 2) hε2_pos h_finite
  -- Use helper lemma for the core bound
  have h_cover_bound : (hE.measure : EReal) ≤ ∑' n, (S n).volume.toEReal :=
    hE.measure_le_cover_sum hd S hS_cover
  calc (hE.measure : EReal)
      ≤ ∑' n, (S n).volume.toEReal := h_cover_bound
    _ ≤ Lebesgue_outer_measure E + (ε / 2 : ℝ) := hS_sum
    _ ≤ Lebesgue_outer_measure E + ε := by
        apply add_le_add_left
        exact_mod_cast (by linarith : ε / 2 ≤ ε)

/-- Direction 2: Outer measure is bounded by elementary measure
    (Uses: m*(E) ≤ J*(E) for bounded E, and J*(E) ≤ hE.measure for elementary E) -/
lemma outer_measure_le_measure {d:ℕ} (_hd: 0 < d) {E: Set (EuclideanSpace' d)}
    (hE: IsElementary E) : Lebesgue_outer_measure E ≤ (hE.measure : EReal) := by
  -- Step 1: Lebesgue outer measure ≤ Jordan outer measure (for bounded sets)
  have h_le_jordan : Lebesgue_outer_measure E ≤ Jordan_outer_measure E :=
    Lebesgue_outer_measure_le_Jordan hE.isBounded
  -- Step 2: Jordan outer measure ≤ elementary measure (by Jordan_outer_le with E ⊆ E)
  have h_jordan_le : Jordan_outer_measure E ≤ hE.measure :=
    Jordan_outer_le hE (Set.Subset.refl E)
  -- Combine: m*(E) ≤ J*(E) ≤ hE.measure (with EReal coercion)
  calc Lebesgue_outer_measure E
      ≤ Jordan_outer_measure E := h_le_jordan
    _ ≤ hE.measure := by exact_mod_cast h_jordan_le

end IsElementary

/-- Dimension 0 case of Lemma 1.2.6 -/
lemma Lebesgue_outer_measure.elementary_dim_zero (E: Set (EuclideanSpace' 0)) (hE: IsElementary E) :
    Lebesgue_outer_measure E = hE.measure := by
  -- In dimension 0, EuclideanSpace' 0 is a singleton (only the empty function Fin 0 → ℝ)
  -- Outer measure is 1 for nonempty sets, 0 for empty set
  rw [Lebesgue_outer_measure_of_dim_zero]
  by_cases hne : E.Nonempty
  · -- Case: E is nonempty → E = Set.univ (singleton type), outer measure = 1
    simp only [hne, ↓reduceIte]
    -- In dim 0, any nonempty elementary set is Set.univ (entire singleton space)
    -- The partition has one box covering univ, with volume = empty product = 1
    -- So hE.measure = 1
    -- Need to show 1 = hE.measure, i.e., hE.measure = 1
    symm
    -- E = Set.univ since EuclideanSpace' 0 has only one point
    have hE_eq_univ : E = Set.univ := by
      ext x
      constructor
      · intro _; exact Set.mem_univ x
      · intro _
        -- Show x ∈ E using that E is nonempty and the space is a singleton
        obtain ⟨y, hy⟩ := hne
        -- In EuclideanSpace' 0 = (Fin 0 → ℝ), all elements are equal (unique function from empty type)
        have : x = y := by ext i; exact i.elim0
        rw [this]; exact hy
    -- Now show measure of Set.univ in dim 0 is 1
    -- In dim 0, any box B has B.toSet = Set.univ and |B|ᵥ = 1 (empty product)
    -- Construct a box in dim 0 and show its measure is 1
    let B : Box 0 := ⟨fun i => i.elim0⟩
    have hB_univ : B.toSet = Set.univ := by
      ext x
      simp only [Box.toSet, Set.mem_univ, iff_true]
      intro i; exact i.elim0
    have hB_vol : |B|ᵥ = 1 := by
      simp only [Box.volume, Finset.univ_eq_empty, Finset.prod_empty]
    -- E = Set.univ = B.toSet, so hE.measure = (IsElementary.box B).measure = |B|ᵥ = 1
    have h_eq : hE.measure = (IsElementary.box B).measure := by
      apply IsElementary.measure_eq_of_set_eq
      rw [hE_eq_univ, hB_univ]
    rw [h_eq, IsElementary.measure_of_box, hB_vol]
    rfl
  · -- Case: E is empty → outer measure = 0 = hE.measure
    have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hne, if_false]
    -- Need: (0 : EReal) = hE.measure
    -- Use that E = ∅ implies hE.measure = 0
    have h_meas_eq : hE.measure = (IsElementary.empty 0).measure :=
      IsElementary.measure_eq_of_set_eq hE (IsElementary.empty 0) hE_empty
    rw [h_meas_eq, IsElementary.measure_of_empty]
    rfl

-- ========================================================================
-- End of Helper lemmas for Lemma 1.2.6
-- ========================================================================
/-- Lemma 1.2.6 (Outer measure of elementary sets).
    For any elementary set E, Lebesgue outer measure equals elementary measure. -/
theorem Lebesgue_outer_measure.elementary {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsElementary E) :
    Lebesgue_outer_measure E = hE.measure := by
  by_cases hd : d = 0
  · -- Dimension 0 case: trivial edge case (EuclideanSpace' 0 is a singleton)
    -- In dim 0, all boxes have volume 1, E is either empty (measure 0) or univ (measure 1)
    subst hd
    -- This edge case requires careful handling of the partition structure in dim 0
    -- For now, defer to a helper lemma
    exact Lebesgue_outer_measure.elementary_dim_zero E hE
  · -- Dimension > 0 case
    push_neg at hd
    have hd' : 0 < d := Nat.pos_of_ne_zero hd
    apply le_antisymm
    · exact IsElementary.outer_measure_le_measure hd' hE
    · exact IsElementary.measure_le_outer_measure hd' hE

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
