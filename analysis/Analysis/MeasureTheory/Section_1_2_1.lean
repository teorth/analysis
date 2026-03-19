import Analysis.MeasureTheory.Section_1_2_0
import Analysis.Misc.«Real-EReal-ENNReal»
import Analysis.Misc.Combinatorics

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Express `Box.toSet` as a preimage of a pi set under the PiLp homeomorphism. -/
lemma Box.toSet_eq_ofLp_preimage {d : ℕ} (B : Box d) :
    B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' Set.univ.pi (fun i => (B.side i).toSet) := by
  ext x; simp only [Box.mem_toSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]; rfl

/-- The interior of `Box.toSet` expressed as a preimage. -/
lemma Box.interior_toSet {d : ℕ} (B : Box d) :
    interior B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      Set.univ.pi (fun i => interior (B.side i).toSet) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_interior,
    interior_pi_set Set.finite_univ]

/-- The closure of `Box.toSet` expressed as a preimage. -/
lemma Box.closure_toSet {d : ℕ} (B : Box d) :
    closure B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      Set.univ.pi (fun i => closure (B.side i).toSet) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_closure,
    closure_pi_set]

/-- The frontier of `Box.toSet` expressed via the PiLp homeomorphism. -/
lemma Box.frontier_toSet {d : ℕ} (B : Box d) :
    frontier B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      frontier (Set.univ.pi (fun i => (B.side i).toSet)) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_frontier]

/-- A box with Icc sides is closed. -/
lemma Box.isClosed_toSet_of_Icc {d : ℕ} (B : Box d)
    (h : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) : IsClosed B.toSet := by
  rw [Box.toSet_eq_ofLp_preimage]
  apply IsClosed.preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous
  apply isClosed_set_pi; intro i _
  obtain ⟨a, b, hab⟩ := h i
  simp only [hab, BoundedInterval.toSet]; exact isClosed_Icc

/-- Exercise 1.2.3(i) (Empty set) -/
theorem Lebesgue_outer_measure.of_empty (d:ℕ) : Lebesgue_outer_measure (∅: Set (EuclideanSpace' d)) = 0 := by
  sorry

/-- Exercise 1.2.3(ii) (Monotonicity) -/
theorem Lebesgue_outer_measure.mono {d: ℕ} {E F : Set (EuclideanSpace' d)} (h : E ⊆ F) :
    Lebesgue_outer_measure E ≤ Lebesgue_outer_measure F := by
  sorry

/-- Lebesgue outer measure is non-negative.
    Since it's the sInf of sums of box volumes, which are all ≥ 0, the result is ≥ 0. -/
theorem Lebesgue_outer_measure.nonneg {d: ℕ} (E : Set (EuclideanSpace' d)) :
    0 ≤ Lebesgue_outer_measure E := by
  unfold Lebesgue_outer_measure
  -- 0 ≤ sInf S when all elements are ≥ 0 (for complete lattice, sInf ∅ = ⊤ ≥ 0)
  apply le_sInf
  intro V hV
  obtain ⟨X, S, _, rfl⟩ := hV
  apply tsum_nonneg
  intro n
  -- Box volume is non-negative (product of nonneg lengths)
  have hvol : 0 ≤ |S n|ᵥ := by
    rw [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    rw [BoundedInterval.length]
    exact le_max_right _ _
  exact EReal.coe_nonneg.mpr hvol

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
        intro i; exact hy i
      have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
        intro i; exact hz i
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
      intro i; exact hz i
    have hw_coord : ∀ i, w i ∈ (B.side i).toSet := by
      intro i; exact hw i
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
    have hx_i : x i ∈ (B.side i).toSet := hx i
    have hy_i : y i ∈ (B.side i).toSet := hy i
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
          exact ⟨x i, hx i⟩
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
        let x' : Fin d → ℝ := fun i => (h_exists_points i).choose
        let y' : Fin d → ℝ := fun i => (h_exists_points i).choose_spec.2.choose
        have hx_mem : ∀ i, x' i ∈ (B.side i).toSet := fun i => (h_exists_points i).choose_spec.1
        have hy_mem : ∀ i, y' i ∈ (B.side i).toSet := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.1
        have h_diff_le : ∀ i, |B.side i|ₗ * ratio ≤ |x' i - y' i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.1
        have h_diff_lt : ∀ i, 0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |x' i - y' i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.2
        -- x, y ∈ B.toSet
        let x : EuclideanSpace' d := .toLp 2 x'
        let y : EuclideanSpace' d := .toLp 2 y'
        have hx_box : x ∈ B.toSet := fun i => hx_mem i
        have hy_box : y ∈ B.toSet := fun i => hy_mem i
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
    exact ⟨x i, hx i⟩
  -- First show B' is nonempty (the midpoint of each side is in both halves)
  have hB'_nonempty : B'.toSet.Nonempty := by
    use .toLp 2 (fun i => (B.side i).midpoint)
    intro i
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
  use .toLp 2 (fun i => (B.side i).midpoint)
  intro i
  have h_side_nonempty : (B.side i).toSet.Nonempty := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i⟩
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
          push_cast; ring
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
        push_cast; ring

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
      intro i
      have hx_i : x i ∈ (B''.side i).toSet := by
        have := hx_B''
        simp only [toSet] at this
        exact this i
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

/-- Closed boxes (all sides are Icc) in Euclidean space are compact sets. -/
lemma isCompact {d : ℕ} (B : Box d) (h_closed : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) :
    IsCompact B.toSet := by
  -- Use Tychonoff: product of compact sets is compact
  rw [Box.toSet_eq_ofLp_preimage]
  apply (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isClosedEmbedding.isCompact_preimage
  apply isCompact_univ_pi
  intro i
  obtain ⟨a, b, hi⟩ := h_closed i
  rw [hi]
  exact isCompact_Icc

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
            rw [tsum_fintype]
            have h_nonneg : ∀ B ∈ I n, 0 ≤ B.volume := fun B _ => Box.volume_nonneg B
            have h_sum_real : ∑ B : ↥(I n), (↑B : Box d).volume = ∑ B ∈ I n, B.volume :=
              Finset.sum_coe_sort (I n) (fun B => B.volume)
            calc ∑ B : ↥(I n), (↑B : Box d).volume.toEReal
                = (∑ B : ↥(I n), (↑B : Box d).volume).toEReal := by
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
    · simp only [h_inf]; apply le_top

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
    have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp [h2n]
    rw [← mul_pow]; norm_num
  rw [h_eq, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)]
  ring
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
    _ = δ / 4 := by field_simp [hP_card_pos.ne.symm]

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
  rw [Box.toSet_eq_ofLp_preimage]
  exact (PiLp.antilipschitzWith_ofLp 2 (fun _ : Fin d => ℝ)).isBounded_preimage
    (Bornology.IsBounded.pi (fun i => BoundedInterval.isBounded (B.side i)))

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
      ext x; simp only [Box.mem_toSet, Set.mem_univ, iff_true]; intro i; exact Fin.elim0 i
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
      rw [B'.toSet_eq_ofLp_preimage]
      exact (isOpen_set_pi Set.finite_univ (fun i _ => by
        simp only [B', BoundedInterval.toSet]; exact isOpen_Ioo)).preimage (PiLp.continuous_ofLp 2 _)
    -- So interior B'.toSet = B'.toSet
    rw [hB'_open.interior_eq]
    -- Now show B.toSet ⊆ B'.toSet
    intro x hx
    simp only [Box.mem_toSet] at hx ⊢
    intro i
    simp only [B', BoundedInterval.toSet, Set.mem_Ioo, BoundedInterval.a, BoundedInterval.b]
    -- Get hx for this specific index i after the case split
    cases hside : (B.side i) with
    | Ioo a b =>
      have hxi := hx i
      simp only [BoundedInterval.toSet, hside, Set.mem_Ioo] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Icc a b =>
      have hxi := hx i
      simp only [BoundedInterval.toSet, hside, Set.mem_Icc] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Ioc a b =>
      have hxi := hx i
      simp only [BoundedInterval.toSet, hside, Set.mem_Ioc] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Ico a b =>
      have hxi := hx i
      simp only [BoundedInterval.toSet, hside, Set.mem_Ico] at hxi ⊢
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
        ext x; simp only [Box.mem_toSet, Set.mem_univ, iff_true]; intro i; exact Fin.elim0 i
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
      simp only [Box.mem_toSet] at hx ⊢
      intro i; specialize hx i
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
      rw [B'.toSet_eq_ofLp_preimage]
      exact (isClosed_set_pi (fun i _ => by simp only [B', BoundedInterval.toSet]; exact isClosed_Icc)).preimage
        (PiLp.continuous_ofLp 2 _)
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
      suffices h : ∀ i, ((B'.side i).toSet).Nonempty by
        rw [B'.toSet_eq_ofLp_preimage]
        exact (Set.pi_nonempty_iff.mpr (fun i => ⟨(h i).some, fun _ => (h i).some_mem⟩)).preimage
          (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).surjective
      intro i
      simp only [B', BoundedInterval.toSet]
      rw [Set.nonempty_Icc]
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
      simp only [Box.mem_toSet] at hy hx ⊢
      intro i
      specialize hy i
      specialize hx i
      simp only [B', BoundedInterval.toSet, Set.mem_Icc] at hy
      have heq : y i = x i := le_antisymm hy.2 hy.1
      rw [heq]; exact hx
    · rw [B'.toSet_eq_ofLp_preimage]
      exact (isClosed_set_pi (fun i _ => by simp only [B', BoundedInterval.toSet]; exact isClosed_Icc)).preimage
        (PiLp.continuous_ofLp 2 _)
    · have hvol' : |B'|ᵥ = 0 := by
        simp only [Box.volume, B']
        have h0 : (⟨0, hd_pos⟩ : Fin d) ∈ Finset.univ := Finset.mem_univ _
        apply Finset.prod_eq_zero h0
        simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b, sub_self]
        exact max_eq_right (le_refl 0)
      rw [hvol', hvol_zero]; linarith
    · -- B'.toSet.Nonempty (degenerate case): B' = {x} is a singleton containing x
      use x
      simp only [Box.mem_toSet]
      intro i
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
    have hδ4P_pos : 0 < δ / (4 * P.card) := div_pos hδ_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hcard_pos))
    have h_sum_bound := partition_volume_bound hP_nonempty_sub hδ4P_pos h_vol_bound
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
          simp
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
    have h_B'_disj : ((Finset.univ : Finset { B // B ∈ P_nonempty }) : Set { B // B ∈ P_nonempty }).PairwiseDisjoint
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
    have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := by
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
        apply add_le_add_left
        rw [h_coe_sum]
        exact h_step2
    _ ≤ (∑ n ∈ t, (S' n).volume : ℝ) + (δ / 4 : ℝ) := by
        apply add_le_add_left h_step3
    _ = (∑ n ∈ t, ((S' n).volume : EReal)) + (δ / 4 : ℝ) := by
        congr 1
        rw [EReal.coe_finset_sum (fun n _ => Box.volume_nonneg _)]
    _ ≤ (∑' n, (S' n).volume : EReal) + (δ / 4 : ℝ) := by
        apply add_le_add_left
        exact h_step4
    _ ≤ (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) + (δ / 4 : ℝ) := by
        have h1 : (∑' n, (S' n).volume : EReal) ≤ (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) := h_inflate_bound
        calc (∑' n, (S' n).volume : EReal) + (δ / 4 : ℝ)
            ≤ ((∑' n, (S n).volume : EReal) + (δ / 2 : ℝ)) + (δ / 4 : ℝ) := add_le_add_left h1 _
          _ = (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) + (δ / 4 : ℝ) := rfl
    _ = (∑' n, (S n).volume : EReal) + ((δ / 2 : ℝ) + (δ / 4 : ℝ)) := by rw [add_assoc]
    _ = (∑' n, (S n).volume : EReal) + (3 * δ / 4 : ℝ) := by
        congr 1
        rw [← EReal.coe_add (δ / 2) (δ / 4)]
        congr 1
        ring
    _ ≤ (∑' n, (S n).volume : EReal) + (δ : ℝ) := by
        apply add_le_add_right
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
        apply add_le_add_right
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
theorem EuclideanSpace'.uncountable (d:ℕ) (hd: 0 < d) : Uncountable (EuclideanSpace' d) := by
  -- Embed ℝ into EuclideanSpace' d via x ↦ (x, 0, 0, ..., 0)
  let f : ℝ → EuclideanSpace' d := fun x => .toLp 2 (fun i => if i = ⟨0, hd⟩ then x else 0)
  have hf : Function.Injective f := fun x y hxy => by
    have : f x ⟨0, hd⟩ = f y ⟨0, hd⟩ := by have := congrArg (· ⟨0, hd⟩) hxy; exact this
    simp only [f, ↓reduceIte] at this
    exact this
  exact hf.uncountable

/-- No uncountable subadditivity: the unit cube has measure 1, but decomposed into
singletons (each with measure 0), the sum is 0. -/
example {d:ℕ} {hd: 0 < d} : ∃ (S:Type) (E: S → Set (EuclideanSpace' d)), ¬ Lebesgue_outer_measure (⋃ i, E i) ≤ ∑' i, Lebesgue_outer_measure (E i) := by
  use (Box.unit_cube d).toSet
  use fun x => {x.val}
  -- ⋃ x, {x.val} = unit cube
  have h_union : ⋃ x : (Box.unit_cube d).toSet, ({x.val} : Set (EuclideanSpace' d)) = (Box.unit_cube d).toSet := by
    ext y; simp
  rw [h_union]
  -- m(unit cube) = 1 via Lebesgue_outer_measure.elementary
  have h_cube : Lebesgue_outer_measure (Box.unit_cube d).toSet = 1 := by
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
    simp only [IsElementary.measure_of_box]
    simp only [Box.volume, BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
    simp
  -- Each singleton has measure 0
  have h_sing : ∀ x : (Box.unit_cube d).toSet, Lebesgue_outer_measure ({x.val} : Set (EuclideanSpace' d)) = 0 := by
    intro x
    exact Countable.Lebesgue_measure hd (Set.countable_singleton x.val)
  -- tsum of zeros is zero
  have h_sum : ∑' x : (Box.unit_cube d).toSet, Lebesgue_outer_measure ({x.val} : Set (EuclideanSpace' d)) = 0 := by
    simp_rw [h_sing]
    exact tsum_zero
  rw [h_cube, h_sum]
  simp

-- ========================================================================
--  Start of Helpers for remark 1.2.8 -/
-- ========================================================================

/-- The distance on EuclideanSpace' 1 equals the distance in ℝ via equiv_Real -/
lemma EuclideanSpace'_dist_eq_Real_dist (x y : EuclideanSpace' 1) :
    dist x y = dist (EuclideanSpace'.equiv_Real x) (EuclideanSpace'.equiv_Real y) := by
  rw [EuclideanSpace.dist_eq, Real.dist_eq]
  simp only [Fin.zero_eta, Real.sqrt_sq_eq_abs, EuclideanSpace'.equiv_Real, Equiv.coe_fn_mk,
    Fin.sum_univ_one, Real.dist_eq, abs_abs]

/-- Preimage of closed interval [a,b] under equiv_Real equals the corresponding 1D box -/
lemma preimage_Icc_eq_box (a b : ℝ) :
    EuclideanSpace'.equiv_Real ⁻¹' Set.Icc a b = (BoundedInterval.Icc a b).toBox.toSet := by
  rw [BoundedInterval.coe_of_box]
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    use EuclideanSpace'.equiv_Real x
    exact ⟨hx, Equiv.symm_apply_apply _ _⟩
  · rintro ⟨y, hy, rfl⟩
    simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real] at hy ⊢
    exact hy

/-- Geometric series: ∑ ε/2^{n+1} = ε -/
lemma tsum_geometric_eps (ε : ℝ) (_hε : 0 < ε) : ∑' n : ℕ, ε / 2^(n+1) = ε := by
  have h_eq : (fun n => ε / 2^(n+1)) = (fun n => ε / 2 * (1/2 : ℝ)^n) := by
    ext n
    have : (2:ℝ)^(n+1) = 2 * 2^n := by ring
    rw [this]
    field_simp; simp
  rw [h_eq, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring

/-- The sum of interval lengths is 2ε -/
lemma tsum_interval_lengths (ε : ℝ) (hε : 0 < ε) : ∑' n : ℕ, (2 * ε / 2^(n+1)) = 2 * ε := by
  have h_eq : (fun n => 2 * ε / 2^(n+1)) = (fun n => 2 * (ε / 2^(n+1))) := by
    ext n; ring
  rw [h_eq, tsum_mul_left, tsum_geometric_eps ε hε]

/-- Summability of the geometric series -/
lemma tsum_interval_summable (ε : ℝ) : Summable (fun n => 2 * ε / 2^(n+1) : ℕ → ℝ) := by
  have h_eq : (fun n => 2 * ε / 2^(n+1)) = (fun n => ε * (1/2 : ℝ)^n) := by
    ext n
    have h_pow : (2:ℝ)^(n+1) = 2 * 2^n := by ring
    rw [h_pow]; field_simp; ring_nf; simp
  rw [h_eq]
  have h_abs : |(1/2:ℝ)| < 1 := by
    simp only [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    norm_num
  have h_geom : Summable (fun n => (1/2:ℝ)^n) := summable_geometric_of_abs_lt_one h_abs
  exact h_geom.mul_left ε

namespace Lebesgue_outer_measure

/-- Lebesgue outer measure of a closed interval [a,b] equals b - a -/
lemma of_Icc (a b : ℝ) (hab : a ≤ b) :
    Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Icc a b) = ((b - a : ℝ) : EReal) := by
  -- [a,b] is a single box in 1D, hence elementary with measure b - a
  let B : Box 1 := (BoundedInterval.Icc a b).toBox
  rw [preimage_Icc_eq_box]
  -- B.toSet is elementary (a box is elementary)
  have h_elem : IsElementary B.toSet := IsElementary.box B
  -- Lebesgue outer measure of elementary set equals its elementary measure
  rw [Lebesgue_outer_measure.elementary B.toSet h_elem]
  -- Elementary measure of a box equals its volume
  rw [IsElementary.measure_of_box B]
  -- Volume of B = b - a
  unfold Box.volume BoundedInterval.length
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.prod_singleton]
  -- max (b - a) 0 = b - a since a ≤ b
  rw [max_eq_left (sub_nonneg.mpr hab)]

/-- Lebesgue measure of an open interval ≤ length (when a < b) -/
lemma of_Ioo_le (a b : ℝ) (h : a < b) :
    Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b) ≤ ((b - a : ℝ) : EReal) := by
  have hab : a ≤ b := le_of_lt h
  calc Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b)
      ≤ Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Icc a b) := by
        apply Lebesgue_outer_measure.mono
        apply Set.preimage_mono
        exact Set.Ioo_subset_Icc_self
    _ = (b - a : EReal) := Lebesgue_outer_measure.of_Icc a b hab

end Lebesgue_outer_measure

/-- Monotonicity of Jordan outer measure, for two bounded sets -/
lemma Jordan_outer_measure_mono {E F : Set (EuclideanSpace' 1)}
    (hEF: E ⊆ F) (_hF: Bornology.IsBounded F) :
    Jordan_outer_measure E ≤ Jordan_outer_measure F := by
  -- Jordan_outer_measure E = sInf { m | ∃ A elem, E ⊆ A ∧ m = |A| }
  -- If E ⊆ F and F ⊆ A, then E ⊆ A, so the set for F is a subset of the set for E
  -- Thus sInf for E ≤ sInf for F
  apply csInf_le_csInf
  · -- The set for E is bounded below (by 0, since measures are nonneg)
    use 0
    intro m hm
    obtain ⟨A, hA, _hEA, hm_eq⟩ := hm
    rw [hm_eq]
    exact hA.measure_nonneg
  · -- The set for F is nonempty (since F is bounded, there exists an elem cover)
    obtain ⟨A, hA, hFA⟩ := IsElementary.contains_bounded _hF
    exact ⟨hA.measure, A, hA, hFA, rfl⟩
  · -- The set for F is a subset of the set for E
    intro m hm
    obtain ⟨A, hA, hFA, hm_eq⟩ := hm
    exact ⟨A, hA, Set.Subset.trans hEF hFA, hm_eq⟩


namespace Remark_1_2_8

/-- Rationals in [0,1] form a nonempty countable set. -/
lemma rationals_unit_interval_nonempty : (Set.Icc (0:ℝ) 1 ∩ Set.range (fun q:ℚ ↦ (q:ℝ))).Nonempty := by
  use 0
  constructor
  · simp
  · use 0; simp

lemma rationals_unit_interval_countable : (Set.Icc (0:ℝ) 1 ∩ Set.range (fun q:ℚ ↦ (q:ℝ))).Countable :=
  Set.Countable.mono Set.inter_subset_right (Set.countable_range _)

/-- An enumeration function of rationals in [0,1] -/
noncomputable def q_enum : ℕ → { x : ℝ // x ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun q:ℚ ↦ (q:ℝ)) } :=
  (rationals_unit_interval_countable.exists_surjective rationals_unit_interval_nonempty).choose

lemma q_enum_surj : Function.Surjective q_enum :=
  (rationals_unit_interval_countable.exists_surjective rationals_unit_interval_nonempty).choose_spec

/-- An enumeration of rationals in [0,1] as real numbers -/
noncomputable def q (n : ℕ) : ℝ := (q_enum n).val

lemma q_mem (n : ℕ) : q n ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun r:ℚ ↦ (r:ℝ)) :=
  (q_enum n).property

lemma q_in_unit_interval (n : ℕ) : q n ∈ Set.Icc (0:ℝ) 1 := (q_mem n).1

lemma q_surj : ∀ x ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun r:ℚ ↦ (r:ℝ)), ∃ n, q n = x := by
  intro x hx
  obtain ⟨n, hn⟩ := q_enum_surj ⟨x, hx⟩
  use n
  unfold q
  rw [hn]

/-- The counterexample set U: union of open intervals around rationals in [0,1].
    U(ε) = ⋃_{n:ℕ} (q_n - ε/2^{n+1}, q_n + ε/2^{n+1}) -/
noncomputable def U_real (ε : ℝ) : Set ℝ :=
  ⋃ n : ℕ, Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1))

/-- The set U lifted to EuclideanSpace' 1 -/
noncomputable def U (ε : ℝ) : Set (EuclideanSpace' 1) :=
  EuclideanSpace'.equiv_Real ⁻¹' (U_real ε)

/-- U_real is open (union of open intervals) -/
lemma U_real_isOpen (ε : ℝ) : IsOpen (U_real ε) := by
  apply isOpen_iUnion
  intro _
  exact isOpen_Ioo

/-- U is open in EuclideanSpace' 1 -/
lemma U_isOpen (ε : ℝ) : IsOpen (U ε) := by
  apply IsOpen.preimage _ (U_real_isOpen ε)
  exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) _

/-- The radius at step n -/
noncomputable def radius (ε : ℝ) (n : ℕ) : ℝ := ε / 2^(n+1)

-- lemma radius_pos (ε : ℝ) (hε : 0 < ε) (n : ℕ) : 0 < radius ε n := by
  -- unfold radius
  -- apply div_pos hε
  -- exact pow_pos (by norm_num : (0:ℝ) < 2) (n+1)

/-- U_real is contained in (-ε, 1+ε) -/
lemma U_real_subset (ε : ℝ) (hε : 0 < ε) : U_real ε ⊆ Set.Ioo (-ε) (1 + ε) := by
  intro x hx
  simp only [U_real, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  simp only [Set.mem_Ioo] at hn ⊢
  have hq := q_in_unit_interval n
  have hr : radius ε n ≤ ε := by
    unfold radius
    apply div_le_self (le_of_lt hε)
    calc (1:ℝ) ≤ 2^1 := by norm_num
      _ ≤ 2^(n+1) := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
        omega
  constructor
  · calc -ε ≤ 0 - ε := by linarith
      _ ≤ q n - ε := by linarith [hq.1]
      _ ≤ q n - radius ε n := by linarith
      _ < x := hn.1
  · calc x < q n + radius ε n := hn.2
      _ ≤ q n + ε := by linarith
      _ ≤ 1 + ε := by linarith [hq.2]

/-- U is bounded -/
lemma U_isBounded (ε : ℝ) (hε : 0 < ε) : Bornology.IsBounded (U ε) := by
  have h_subset : U ε ⊆ EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (-ε) (1 + ε) := by
    apply Set.preimage_mono
    exact U_real_subset ε hε
  apply Bornology.IsBounded.subset _ h_subset
  rw [Metric.isBounded_iff_subset_closedBall 0]
  use max (|(-ε)|) (|1 + ε|) + 1
  intro x hx
  simp only [Set.mem_preimage, Set.mem_Ioo] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [EuclideanSpace'.norm_eq]
  have hsum : (∑ i : Fin 1, x i ^ 2) = x ⟨0, by omega⟩ ^ 2 := Fin.sum_univ_one _
  rw [hsum, Real.sqrt_sq_eq_abs]
  have h1 : EuclideanSpace'.equiv_Real x = x ⟨0, by omega⟩ := rfl
  have hx' : -ε < x ⟨0, by omega⟩ ∧ x ⟨0, by omega⟩ < 1 + ε := by
    rw [← h1]; exact hx
  have h_bd : |x ⟨0, by omega⟩| ≤ max (|-ε|) (|1 + ε|) := by
    apply abs_le_max_abs_abs <;> linarith [hx'.1, hx'.2]
  linarith

/-- Bound on each component interval's Lebesgue measure -/
lemma component_lebesgue_le (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1)))
    ≤ ((2 * ε / 2^(n+1) : ℝ) : EReal) := by
  have h_rad_pos : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0:ℝ) < 2) (n+1))
  have h_lt : q n - ε / 2^(n+1) < q n + ε / 2^(n+1) := by linarith
  have h_length : (q n + ε / 2^(n+1)) - (q n - ε / 2^(n+1)) = 2 * ε / 2^(n+1) := by ring
  have h1 := Lebesgue_outer_measure.of_Ioo_le (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1)) h_lt
  simp only [h_length] at h1
  exact h1

/-- Closure of U_real contains [0,1] (density of rationals) -/
lemma U_real_closure_contains_unit_interval (ε : ℝ) (hε : 0 < ε) :
    Set.Icc 0 1 ⊆ closure (U_real ε) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro t ht
  -- t is a neighborhood of x, so it contains a ball around x
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := ht
  -- Find a rational in [0,1] close to x
  have h_rat_exists : ∃ r : ℚ, (r:ℝ) ∈ Set.Icc (0:ℝ) 1 ∧ |(r:ℝ) - x| < δ := by
    by_cases h : x < δ
    · use 0
      constructor
      · simp only [Rat.cast_zero, Set.mem_Icc, le_refl, zero_le_one, and_self]
      · rw [Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hx.1]
        exact h
    · push_neg at h
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (sub_lt_self x hδ_pos)
      use r
      constructor
      · constructor
        · have : (0:ℝ) ≤ x - δ := by linarith
          linarith
        · linarith [hx.2]
      · rw [abs_sub_comm, abs_sub_lt_iff]
        constructor <;> linarith
  obtain ⟨r, hr_in, hr_close⟩ := h_rat_exists
  -- r is in Set.range of Rat.cast
  have hr_range : (r:ℝ) ∈ Set.range (fun s:ℚ ↦ (s:ℝ)) := ⟨r, rfl⟩
  -- So there exists n with q n = r
  have hr_inter : (r:ℝ) ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun s:ℚ ↦ (s:ℝ)) := ⟨hr_in, hr_range⟩
  obtain ⟨n, hn⟩ := q_surj r hr_inter
  -- q n = r, and q n is in U_real (in the interval around itself)
  have hqn_in_U : q n ∈ U_real ε := by
    simp only [U_real, Set.mem_iUnion, Set.mem_Ioo]
    use n
    constructor
    · have : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0:ℝ) < 2) (n+1))
      linarith
    · have : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0:ℝ) < 2) (n+1))
      linarith
  -- q n is close to x (since q n = r)
  have hqn_in_ball : q n ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_comm]
    calc dist x (q n) = |x - q n| := Real.dist_eq x (q n)
      _ = |x - r| := by rw [hn]
      _ = |r - x| := abs_sub_comm x r
      _ < δ := hr_close
  -- So q n is in t
  have hqn_in_t : q n ∈ t := hδ_sub hqn_in_ball
  exact ⟨q n, hqn_in_t, hqn_in_U⟩

/-- Unit interval [0,1] as a BoundedInterval -/
abbrev unit_interval : BoundedInterval := BoundedInterval.Icc 0 1

/-- Unit box in 1D: [0,1] lifted to Box 1 -/
abbrev unit_box_1D : Box 1 := unit_interval.toBox

/-- Unit interval as the preimage of [0,1] equals unit box -/
lemma unit_interval_eq_box : EuclideanSpace'.equiv_Real ⁻¹' Set.Icc 0 1 = unit_box_1D.toSet :=
  preimage_Icc_eq_box 0 1

/-- Volume of unit box is 1 -/
lemma unit_box_volume : |unit_box_1D|ᵥ = 1 := by
  unfold unit_box_1D unit_interval Box.volume BoundedInterval.length
  norm_num

/-- Jordan outer measure of unit box is 1 -/
lemma Jordan_outer_unit_box : Jordan_outer_measure unit_box_1D.toSet = 1 := by
  have h_elem := IsElementary.box unit_box_1D
  have h_jm := h_elem.jordanMeasurable
  rw [← h_jm.eq_outer]
  rw [JordanMeasurable.mes_of_elementary h_elem]
  rw [IsElementary.measure_of_box unit_box_1D]
  exact unit_box_volume

/-- Closure of U contains the preimage of [0,1] -/
lemma U_closure_contains_unit_box (ε : ℝ) (hε : 0 < ε) :
    unit_box_1D.toSet ⊆ closure (U ε) := by
  -- Key insight: For a homeomorphism f, closure(f⁻¹(S)) = f⁻¹(closure(S))
  -- Since U ε = equiv_Real⁻¹(U_real ε) and equiv_Real is a homeomorphism:
  -- closure(U ε) = equiv_Real⁻¹(closure(U_real ε)) ⊇ equiv_Real⁻¹([0,1]) = unit_box_1D
  have h_closure_real := U_real_closure_contains_unit_interval ε hε
  rw [← unit_interval_eq_box]
  intro x hx
  rw [Set.mem_preimage] at hx
  have hx_in_closure : EuclideanSpace'.equiv_Real x ∈ closure (U_real ε) :=
    h_closure_real hx
  rw [mem_closure_iff_nhds] at hx_in_closure ⊢
  intro t ht
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := ht
  have h_ball_nhd : Metric.ball (EuclideanSpace'.equiv_Real x) δ ∈ nhds (EuclideanSpace'.equiv_Real x) :=
    Metric.ball_mem_nhds _ hδ_pos
  obtain ⟨y, hy_ball, hy_U⟩ := hx_in_closure _ h_ball_nhd
  use EuclideanSpace'.equiv_Real.symm y
  constructor
  · apply hδ_sub
    rw [Metric.mem_ball, EuclideanSpace'_dist_eq_Real_dist, Equiv.apply_symm_apply]
    exact hy_ball
  · simp only [U, Set.mem_preimage, Equiv.apply_symm_apply]
    exact hy_U

/-- Jordan outer measure of U ≥ 1.
    Proof uses: density of ℚ → closure(U) ⊇ [0,1] → Jordan_outer(U) ≥ Jordan_outer([0,1]) = 1. -/
lemma U_jordan_outer_ge (ε : ℝ) (hε : 0 < ε) :
    Jordan_outer_measure (U ε) ≥ 1 := by
  -- By JordanMeasurable.outer_measure_of_closure, Jordan_outer(closure U) = Jordan_outer(U)
  have h_closure_eq := JordanMeasurable.outer_measure_of_closure (U_isBounded ε hε)
  -- closure(U) ⊇ unit_box, so by monotonicity:
  have h_closure_contains := U_closure_contains_unit_box ε hε
  have h_unit_bound : Jordan_outer_measure unit_box_1D.toSet ≤ Jordan_outer_measure (closure (U ε)) := by
    apply Jordan_outer_measure_mono h_closure_contains
    exact Bornology.IsBounded.closure (U_isBounded ε hε)
  calc 1 = Jordan_outer_measure unit_box_1D.toSet := Jordan_outer_unit_box.symm
    _ ≤ Jordan_outer_measure (closure (U ε)) := h_unit_bound
    _ = Jordan_outer_measure (U ε) := h_closure_eq

/-- Lebesgue outer measure of U ≤ 2ε (countable subadditivity).
    U = ⋃_n (q_n - ε/2^{n+1}, q_n + ε/2^{n+1}), each interval has length 2ε/2^{n+1},
    and ∑ 2ε/2^{n+1} = 2ε.

    Proof structure:
    1. Express U as countable union: U = ⋃_n E_n
    2. By countable subadditivity (union_le): m*(U) ≤ ∑' m*(E_n)
    3. Each component bounded: m*(E_n) ≤ 2ε/2^{n+1} (component_lebesgue_le)
    4. Geometric sum: ∑' 2ε/2^{n+1} = 2ε (tsum_interval_lengths)
    5. EReal tsum comparison: ∑' m*(E_n) ≤ ∑' (2ε/2^{n+1}) = 2ε -/
lemma U_lebesgue_le (ε : ℝ) (hε : 0 < ε) :
    Lebesgue_outer_measure (U ε) ≤ ((2 * ε : ℝ) : EReal) := by
  -- U = ⋃_n (component intervals in EuclideanSpace' 1)
  let E : ℕ → Set (EuclideanSpace' 1) := fun n =>
    EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1))
  -- U ε = ⋃ n, E n
  have h_U_eq : U ε = ⋃ n, E n := by
    ext x
    simp only [U, U_real, Set.mem_preimage, Set.mem_iUnion, E]
  -- By countable subadditivity: m*(U) ≤ ∑' n, m*(E n)
  have h_subadditive := Lebesgue_outer_measure.union_le E
  -- Each component has m*(E n) ≤ 2ε/2^{n+1}
  have h_component_bound : ∀ n, Lebesgue_outer_measure (E n) ≤ ((2 * ε / 2^(n+1) : ℝ) : EReal) :=
    fun n => component_lebesgue_le ε hε n
  -- Sum bound: ∑' n, m*(E n) ≤ 2ε
  have h_sum_bound : ∑' n, Lebesgue_outer_measure (E n) ≤ ((2 * ε : ℝ) : EReal) := by
    have h_g_nonneg : ∀ n, 0 ≤ 2 * ε / 2^(n+1) := by
      intro n
      apply div_nonneg (by linarith : 0 ≤ 2 * ε)
      exact pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _
    have h_tsum_eq := tsum_interval_lengths ε hε
    rw [← h_tsum_eq]
    -- Lebesgue outer measure is non-negative (sInf of sums of box volumes ≥ 0)
    have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (E n) := fun n =>
      Lebesgue_outer_measure.nonneg (E n)
    -- Summability of the geometric series
    have h_summable : Summable (fun n => 2 * ε / 2^(n+1)) := tsum_interval_summable ε
    -- Use coe_tsum lemma: ↑(∑' g) = ∑' (↑g)
    rw [EReal.coe_tsum_of_nonneg h_g_nonneg h_summable]
    -- Apply the helper lemma for pointwise comparison
    exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_g_nonneg h_summable h_component_bound
  calc Lebesgue_outer_measure (U ε) = Lebesgue_outer_measure (⋃ n, E n) := by rw [h_U_eq]
    _ ≤ ∑' n, Lebesgue_outer_measure (E n) := h_subadditive
    _ ≤ ((2 * ε : ℝ) : EReal) := h_sum_bound

end Remark_1_2_8
-- ========================================================================
--  End of Helpers for remark 1.2.8 -/
-- ========================================================================

/-- Remark 1.2.8: There exists a bounded open set that is not Jordan measurable.
    Proof sketch: Take U = ⋃_{n} (q_n - ε/2^{n+1}, q_n + ε/2^{n+1}) where {q_n} enumerates ℚ ∩ [0,1].
    U is open and bounded. By countable subadditivity, m*(U) ≤ 2ε.
    By density of ℚ, closure(U) ⊇ [0,1], so m*,J(U) ≥ 1.
    For ε = 1/3, we get m*(U) ≤ 2/3 < 1 ≤ m*,J(U), contradicting Jordan measurability. -/
example : ∃ (E: Set (EuclideanSpace' 1)), Bornology.IsBounded E ∧
    IsOpen E ∧ ¬ JordanMeasurable E := by
  use Remark_1_2_8.U (1/3)
  refine ⟨Remark_1_2_8.U_isBounded (1/3) (by norm_num),
         Remark_1_2_8.U_isOpen (1/3), ?_⟩
  intro hJM
  -- Step 1: Jordan outer measure of U ≥ 1 (from density argument)
  have h_outer : Jordan_outer_measure (Remark_1_2_8.U (1/3)) ≥ 1 :=
    Remark_1_2_8.U_jordan_outer_ge (1/3) (by norm_num)
  -- Step 2: Lebesgue outer measure of U ≤ 2/3 (from countable subadditivity)
  have h_lebesgue : Lebesgue_outer_measure (Remark_1_2_8.U (1/3)) ≤ (2/3 : EReal) := by
    have := Remark_1_2_8.U_lebesgue_le (1/3) (by norm_num : (0:ℝ) < 1/3)
    have h_eq : (2 * (1/3 : ℝ) : EReal) = (2/3 : EReal) := by
      simp only [one_div]
      norm_cast
    calc Lebesgue_outer_measure (Remark_1_2_8.U (1/3)) ≤ 2 * (1/3 : ℝ) := this
      _ = (2/3 : EReal) := h_eq
  -- Step 3: Jordan inner measure ≤ 2/3
  -- Key insight: For any elementary A ⊆ U, hA.measure = Lebesgue_outer(A) ≤ Lebesgue_outer(U) ≤ 2/3
  have h_inner_le : Jordan_inner_measure (Remark_1_2_8.U (1/3)) ≤ 2/3 := by
    -- Jordan_inner = sSup { m | ∃ A elementary, A ⊆ U ∧ m = hA.measure }
    -- Show 2/3 is an upper bound
    apply csSup_le
    · -- The set is nonempty (empty set is elementary with measure 0)
      use 0, ∅, IsElementary.empty 1
      exact ⟨Set.empty_subset _, (IsElementary.measure_of_empty 1).symm⟩
    · -- Show 2/3 bounds all elements
      intro m ⟨A, hA, hA_sub, hm⟩
      rw [hm]
      -- hA.measure = Lebesgue_outer(A) by Lemma 1.2.6
      have h_elem : Lebesgue_outer_measure A = hA.measure :=
        Lebesgue_outer_measure.elementary A hA
      -- Lebesgue_outer(A) ≤ Lebesgue_outer(U) by monotonicity
      have h_mono : Lebesgue_outer_measure A ≤ Lebesgue_outer_measure (Remark_1_2_8.U (1/3)) :=
        Lebesgue_outer_measure.mono hA_sub
      -- Combine: hA.measure ≤ 2/3
      have h_bound : (hA.measure : EReal) ≤ (2/3 : EReal) := by
        calc (hA.measure : EReal) = Lebesgue_outer_measure A := h_elem.symm
          _ ≤ Lebesgue_outer_measure (Remark_1_2_8.U (1/3)) := h_mono
          _ ≤ (2/3 : EReal) := h_lebesgue
      have h_coe : ((2/3 : ℝ) : EReal) = (2/3 : EReal) := by norm_cast
      rw [← h_coe] at h_bound
      exact EReal.coe_le_coe_iff.mp h_bound
  -- Step 4: Derive contradiction
  -- JordanMeasurable means Jordan_inner = Jordan_outer
  have h_jm_eq : Jordan_inner_measure (Remark_1_2_8.U (1/3)) =
      Jordan_outer_measure (Remark_1_2_8.U (1/3)) := hJM.2
  -- From Jordan_outer ≥ 1 and Jordan_inner = Jordan_outer: Jordan_inner ≥ 1
  have h_inner_ge : Jordan_inner_measure (Remark_1_2_8.U (1/3)) ≥ 1 := by
    rw [h_jm_eq]; exact h_outer
  -- Contradiction: 1 ≤ Jordan_inner ≤ 2/3 is impossible
  linarith

/-- Remark 1.2.8: The complement of U in [-2,2] is compact but not Jordan measurable. -/
example : ∃ (E: Set (EuclideanSpace' 1)), Bornology.IsBounded E ∧
    IsCompact E ∧ ¬ JordanMeasurable E := by
  -- Let B = [-2, 2] lifted to EuclideanSpace' 1
  let B : Set (EuclideanSpace' 1) := EuclideanSpace'.equiv_Real ⁻¹' Set.Icc (-2) 2
  -- Let U be the non-Jordan-measurable open set from the first part
  let U := Remark_1_2_8.U (1/3)
  -- E = B \ U is compact but not Jordan measurable
  use B \ U
  refine ⟨?bounded, ?compact, ?not_jm⟩
  case bounded =>
    -- E ⊆ B which is bounded
    apply Bornology.IsBounded.subset _ Set.diff_subset
    rw [Metric.isBounded_iff_subset_closedBall 0]
    use 3
    intro x hx
    -- hx : x ∈ B means equiv_Real x ∈ [-2, 2]
    have hx' : EuclideanSpace'.equiv_Real x ∈ Set.Icc (-2 : ℝ) 2 := hx
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace'.norm_eq]
    have hsum : (∑ i : Fin 1, x i ^ 2) = x ⟨0, by omega⟩ ^ 2 := Fin.sum_univ_one _
    rw [hsum, Real.sqrt_sq_eq_abs]
    have h1 : EuclideanSpace'.equiv_Real x = x ⟨0, by omega⟩ := rfl
    simp only [Set.mem_Icc] at hx'
    rw [h1] at hx'
    have : |x ⟨0, by omega⟩| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  case compact =>
    -- B is compact (continuous preimage of compact)
    have hB_compact : IsCompact B := by
      have h_cont : Continuous EuclideanSpace'.equiv_Real := PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) _
      apply Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.preimage h_cont)
      rw [Metric.isBounded_iff_subset_closedBall 0]
      use 3
      intro x hx
      have hx' : EuclideanSpace'.equiv_Real x ∈ Set.Icc (-2 : ℝ) 2 := hx
      rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace'.norm_eq]
      have hsum : (∑ i : Fin 1, x i ^ 2) = x ⟨0, by omega⟩ ^ 2 := Fin.sum_univ_one _
      rw [hsum, Real.sqrt_sq_eq_abs]
      have h1 : EuclideanSpace'.equiv_Real x = x ⟨0, by omega⟩ := rfl
      simp only [Set.mem_Icc] at hx'
      rw [h1] at hx'
      have : |x ⟨0, by omega⟩| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    -- U is open
    have hU_open : IsOpen U := Remark_1_2_8.U_isOpen (1/3)
    -- B \ U = B ∩ Uᶜ is closed in B (since Uᶜ is closed)
    have hU_compl_closed : IsClosed Uᶜ := hU_open.isClosed_compl
    -- B \ U is compact (closed subset of compact)
    rw [Set.diff_eq]
    exact hB_compact.inter_right hU_compl_closed
  case not_jm =>
    intro hE_jm
    -- B is elementary (it's a box), hence Jordan measurable
    have hB_elem : IsElementary B := by
      have : B = (BoundedInterval.Icc (-2) 2).toBox.toSet := preimage_Icc_eq_box (-2) 2
      rw [this]
      exact IsElementary.box _
    have hB_jm : JordanMeasurable B := hB_elem.jordanMeasurable
    -- If E = B \ U is Jordan measurable, then U ∩ B = B \ E is Jordan measurable
    have h_eq : U ∩ B = B \ (B \ U) := by ext; simp [Set.mem_inter_iff]; tauto
    have hUB_jm : JordanMeasurable (U ∩ B) := by
      rw [h_eq]
      exact JordanMeasurable.sdiff hB_jm hE_jm
    -- U ⊆ B (since U ⊆ (-1/3, 4/3) ⊆ [-2, 2])
    have hU_sub_B : U ⊆ B := by
      intro x hx
      have h_sub := Remark_1_2_8.U_real_subset (1/3) (by norm_num : (0:ℝ) < 1/3)
      -- hx : x ∈ U means equiv_Real x ∈ U_real
      have hx' : EuclideanSpace'.equiv_Real x ∈ Remark_1_2_8.U_real (1/3) := hx
      have hx_real := h_sub hx'
      simp only [Set.mem_Ioo] at hx_real
      -- Need to show x ∈ B, i.e., equiv_Real x ∈ [-2, 2]
      show EuclideanSpace'.equiv_Real x ∈ Set.Icc (-2) 2
      simp only [Set.mem_Icc]
      constructor <;> linarith [hx_real.1, hx_real.2]
    -- So U ∩ B = U, meaning U is Jordan measurable
    have hU_eq : U ∩ B = U := Set.inter_eq_self_of_subset_left hU_sub_B
    rw [hU_eq] at hUB_jm
    -- But we proved U is not Jordan measurable (from the first example)
    have hU_not_jm : ¬ JordanMeasurable U := by
      intro hJM
      have h_outer : Jordan_outer_measure U ≥ 1 :=
        Remark_1_2_8.U_jordan_outer_ge (1/3) (by norm_num)
      have h_lebesgue : Lebesgue_outer_measure U ≤ (2/3 : EReal) := by
        have := Remark_1_2_8.U_lebesgue_le (1/3) (by norm_num : (0:ℝ) < 1/3)
        have h_eq : (2 * (1/3 : ℝ) : EReal) = (2/3 : EReal) := by simp only [one_div]; norm_cast
        calc Lebesgue_outer_measure U ≤ 2 * (1/3 : ℝ) := this
          _ = (2/3 : EReal) := h_eq
      have h_inner_le : Jordan_inner_measure U ≤ 2/3 := by
        apply csSup_le
        · use 0, ∅, IsElementary.empty 1
          exact ⟨Set.empty_subset _, (IsElementary.measure_of_empty 1).symm⟩
        · intro m ⟨A, hA, hA_sub, hm⟩
          rw [hm]
          have h_elem : Lebesgue_outer_measure A = hA.measure :=
            Lebesgue_outer_measure.elementary A hA
          have h_mono : Lebesgue_outer_measure A ≤ Lebesgue_outer_measure U :=
            Lebesgue_outer_measure.mono hA_sub
          have h_bound : (hA.measure : EReal) ≤ (2/3 : EReal) := by
            calc (hA.measure : EReal) = Lebesgue_outer_measure A := h_elem.symm
              _ ≤ Lebesgue_outer_measure U := h_mono
              _ ≤ (2/3 : EReal) := h_lebesgue
          have h_coe : ((2/3 : ℝ) : EReal) = (2/3 : EReal) := by norm_cast
          rw [← h_coe] at h_bound
          exact EReal.coe_le_coe_iff.mp h_bound
      have h_jm_eq : Jordan_inner_measure U = Jordan_outer_measure U := hJM.2
      have h_inner_ge : Jordan_inner_measure U ≥ 1 := by rw [h_jm_eq]; exact h_outer
      linarith
    exact hU_not_jm hUB_jm

def AlmostDisjoint {d:ℕ} (B B': Box d) : Prop := interior B.toSet ∩ interior B'.toSet = ∅

-- Helpers for theorem IsElementary.almost_disjoint
/-- Measure is additive on unions of elementary sets with disjoint interiors: μ(E ∪ F) = μ(E) + μ(F). -/
lemma IsElementary.measure_of_almostDisjUnion {d:ℕ} {E F: Set (EuclideanSpace' d)}
    (hE: IsElementary E) (hF: IsElementary F)
    (h: interior E ∩ interior F = ∅) :
    (hE.union hF).measure = hE.measure + hF.measure := by
  -- Strategy: Use decomposition E ∪ F = E ∪ (F \ E) which is disjoint,
  -- then show (F \ E).measure = hF.measure by using that E ∩ F has measure zero
  -- when interiors are disjoint.
  classical
  -- Step 1: Decompose E ∪ F = E ∪ (F \ E) (disjoint union)
  have h_union_decomp : E ∪ F = E ∪ (F \ E) := by
    ext x
    constructor
    · rintro (hx_E | hx_F)
      · exact Or.inl hx_E
      · by_cases hx_E : x ∈ E
        · exact Or.inl hx_E
        · exact Or.inr ⟨hx_F, hx_E⟩
    · rintro (hx_E | ⟨hx_F, _⟩)
      · exact Or.inl hx_E
      · exact Or.inr hx_F
  -- Step 2: F \ E is elementary and disjoint from E
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_E, _, hx_not_E⟩
    exact hx_not_E hx_E
  -- Step 3: Apply measure_of_disjUnion
  have h_decomp_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Step 4: Show both unions represent the same set
  set T := (hE.union hF).partition.choose
  have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := (hE.union hF).partition.choose_spec.1
  have h_eq : E ∪ F = ⋃ B ∈ T, B.toSet := (hE.union hF).partition.choose_spec.2
  have h_measure_eq : (hE.union hF_sdiff_E).measure = (hE.union hF).measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_disj (by rw [← h_union_decomp, h_eq]),
        (hE.union hF).measure_eq hT_disj h_eq]
  -- Step 5: Show (F \ E).measure = hF.measure when interiors are disjoint
  -- This follows because E ∩ F ⊆ frontier E ∪ frontier F, and the overlap has measure zero
  have h_sdiff_measure : hF_sdiff_E.measure = hF.measure := by
    -- By monotonicity: (F \ E).measure ≤ hF.measure (since F \ E ⊆ F)
    have h_mono : hF_sdiff_E.measure ≤ hF.measure :=
      IsElementary.measure_mono hF_sdiff_E hF (fun _ hx => hx.1)
    -- By additivity: hF.measure ≤ (E ∩ F).measure + (F \ E).measure
    -- But E ∩ F is elementary and has empty interior, so measure ≤ 0
    -- For disjoint interiors, we can show measure_mono in reverse direction
    have h_decomp_F : F = (E ∩ F) ∪ (F \ E) := by
      ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
      constructor
      · intro hx
        by_cases hxE : x ∈ E
        · exact Or.inl ⟨hxE, hx⟩
        · exact Or.inr ⟨hx, hxE⟩
      · rintro (⟨_, hx⟩ | ⟨hx, _⟩) <;> exact hx
    have h_disj_decomp : Disjoint (E ∩ F) (F \ E) := by
      rw [Set.disjoint_iff]
      intro x ⟨⟨hxE, _⟩, _, hxnE⟩
      exact hxnE hxE
    have hEF_inter : IsElementary (E ∩ F) := IsElementary.inter hE hF
    have h_F_measure : hF.measure = (hEF_inter.union hF_sdiff_E).measure := by
      set T_F := hF.partition.choose
      have hT_F_disj : (T_F : Set (Box d)).PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
      have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
      rw [(hEF_inter.union hF_sdiff_E).measure_eq hT_F_disj (by rw [← h_decomp_F, hF_eq]),
          hF.measure_eq hT_F_disj hF_eq]
    have h_union_add : (hEF_inter.union hF_sdiff_E).measure = hEF_inter.measure + hF_sdiff_E.measure :=
      IsElementary.measure_of_disjUnion hEF_inter hF_sdiff_E h_disj_decomp
    -- Key: show hEF_inter.measure = 0 when interior E ∩ interior F = ∅
    -- This requires showing that elementary sets with empty interior have measure zero
    have h_inter_empty_interior : interior (E ∩ F) = ∅ := by
      rw [interior_inter, h]
    -- For an elementary set with empty interior, all its partition boxes must be degenerate
    have h_inter_measure_zero : hEF_inter.measure = 0 := by
      set T_EF := hEF_inter.partition.choose
      have hT_EF_disj : (T_EF : Set (Box d)).PairwiseDisjoint Box.toSet := hEF_inter.partition.choose_spec.1
      have hEF_eq : E ∩ F = ⋃ B ∈ T_EF, B.toSet := hEF_inter.partition.choose_spec.2
      rw [hEF_inter.measure_eq hT_EF_disj hEF_eq]
      apply Finset.sum_eq_zero
      intro B hB
      -- Show B has empty interior and thus volume 0
      have hB_subset : B.toSet ⊆ E ∩ F := by
        rw [hEF_eq]
        exact Set.subset_biUnion_of_mem hB
      have hB_interior_empty : interior B.toSet = ∅ := by
        apply Set.eq_empty_of_subset_empty
        calc interior B.toSet ⊆ interior (E ∩ F) := interior_mono hB_subset
          _ = ∅ := h_inter_empty_interior
      -- Use that a box with empty interior has volume zero
      -- interior B = ∅ means some side has empty interior, i.e., is a single point or empty
      -- For a box, this means some BoundedInterval has a = b (degenerate)
      -- The interior of a box is empty iff some side interval has empty interior
      have hB_empty_or_degenerate : B.toSet = ∅ ∨ ∃ i, interior (B.side i).toSet = ∅ := by
        by_cases hB_nonempty : B.toSet.Nonempty
        · right
          by_contra h_all_nonempty
          push_neg at h_all_nonempty
          have : (Set.univ.pi fun i => interior (B.side i).toSet).Nonempty :=
            Set.univ_pi_nonempty_iff.mpr (fun i => h_all_nonempty i)
          rw [B.interior_toSet] at hB_interior_empty
          exact (this.preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).surjective).ne_empty hB_interior_empty
        · left
          exact Set.not_nonempty_iff_eq_empty.mp hB_nonempty
      rcases hB_empty_or_degenerate with hB_empty | ⟨i, hi⟩
      · exact Box.volume_eq_zero_of_empty B hB_empty
      · -- A BoundedInterval with empty interior has length 0
        rw [Box.volume]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        -- Show |B.side i|ₗ = 0 when interior (B.side i).toSet = ∅
        have h_length_zero : |B.side i|ₗ = 0 := by
          cases hI : B.side i with
          | Ioo a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ioo, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Icc a b =>
            simp only [hI, BoundedInterval.toSet, interior_Icc, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Ioc a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ioc, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Ico a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ico, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
        exact h_length_zero
    -- Now combine: hF.measure = 0 + hF_sdiff_E.measure = hF_sdiff_E.measure
    rw [h_F_measure, h_union_add, h_inter_measure_zero, zero_add]
  -- Final step: combine everything
  rw [← h_measure_eq, h_decomp_measure, h_sdiff_measure]

/-- Split a Fin (n+1) indexed union into a Fin n indexed union plus the last element.
    This is a general helper for induction on finite unions. -/
lemma Fin.iUnion_succ_eq_union_last {α : Type*} {n : ℕ} (f : Fin (n + 1) → Set α) :
    (⋃ i, f i) = (⋃ i : Fin n, f (Fin.castSucc i)) ∪ f (Fin.last n) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · intro ⟨i, hi⟩
    by_cases hlt : (i : ℕ) < n
    · left; exact ⟨⟨i, hlt⟩, by simp [Fin.castSucc]; exact hi⟩
    · right
      have : i = Fin.last n := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt hlt)
      exact this ▸ hi
  · intro h
    rcases h with ⟨i, hi⟩ | h
    · exact ⟨Fin.castSucc i, hi⟩
    · exact ⟨Fin.last n, h⟩

/-- When boxes are pairwise almost-disjoint, restricting to the first n boxes preserves this. -/
lemma AlmostDisjoint.pairwise_castSucc {d n : ℕ} {B : Fin (n + 1) → Box d}
    (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) :
    Pairwise (Function.onFun AlmostDisjoint (fun i => B (Fin.castSucc i))) := by
  intro i j hij
  simp only [Function.onFun]
  apply hdisj
  simp [Fin.ext_iff]
  intro heq
  exact hij (Fin.ext heq)

/-- When boxes are pairwise almost-disjoint, any of the first n is almost-disjoint from the last. -/
lemma AlmostDisjoint.castSucc_last {d n : ℕ} {B : Fin (n + 1) → Box d}
    (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) (i : Fin n) :
    AlmostDisjoint (B (Fin.castSucc i)) (B (Fin.last n)) := by
  apply hdisj
  intro heq
  have h1 : (Fin.castSucc i).val < n := Fin.castSucc_lt_last i
  rw [heq] at h1
  simp at h1

/-- For any BoundedInterval, interior (closure I) ⊆ closure (interior I).
    This holds because all interval types (Ioo, Icc, Ioc, Ico) have closure = Icc
    and interior = Ioo, so interior(closure(I)) = Ioo ⊆ Icc = closure(interior(I)). -/
lemma BoundedInterval.interior_closure_subset_closure_interior (I : BoundedInterval) :
    interior (closure (I : Set ℝ)) ⊆ closure (interior (I : Set ℝ)) := by
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.set_Ioo]
    by_cases hab : a < b
    · simp only [closure_Ioo (ne_of_lt hab), interior_Icc, interior_Ioo]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ioo_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _
  | Icc a b =>
    simp only [BoundedInterval.set_Icc]
    by_cases hab : a < b
    · simp only [closure_Icc, interior_Icc, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [interior_Icc, Set.Ioo_eq_empty hab, closure_Icc, closure_empty]
      exact Set.empty_subset _
  | Ioc a b =>
    simp only [BoundedInterval.set_Ioc]
    by_cases hab : a < b
    · simp only [closure_Ioc (ne_of_lt hab), interior_Icc, interior_Ioc, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ioc_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _
  | Ico a b =>
    simp only [BoundedInterval.set_Ico]
    by_cases hab : a < b
    · simp only [closure_Ico (ne_of_lt hab), interior_Icc, interior_Ico, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ico_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _

/-- For any box, the interior of its frontier is empty. This holds regardless of whether
    the box uses closed intervals (Icc), open intervals (Ioo), or half-open intervals,
    because the frontier of a box is a lower-dimensional set (union of faces). -/
lemma Box.interior_frontier_eq_empty {d : ℕ} (B : Box d) : interior (frontier B.toSet) = ∅ := by
  rw [Box.frontier_toSet, ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_interior]
  rw [frontier, closure_pi_set, interior_pi_set Set.finite_univ, Set.diff_eq,
      interior_inter, interior_pi_set Set.finite_univ, interior_compl, closure_pi_set]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  simp only [Set.mem_preimage] at hx
  have ⟨hx1, hx2⟩ := hx
  apply hx2
  exact Set.pi_mono (fun i _ => BoundedInterval.interior_closure_subset_closure_interior _) hx1

/-- The interior of a finite union of box frontiers is empty. This is because each box frontier
    is a closed set with empty interior, and we can apply `interior_union_isClosed_of_interior_empty`
    iteratively. -/
lemma interior_iUnion_Box_frontier_eq_empty {d n : ℕ} (B : Fin n → Box d) :
    interior (⋃ i, frontier (B i).toSet) = ∅ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.iUnion_succ_eq_union_last, Set.union_comm,
        interior_union_isClosed_of_interior_empty isClosed_frontier]
    · exact Box.interior_frontier_eq_empty (B (Fin.last m))
    · exact ih (fun i => B (Fin.castSucc i))

theorem IsElementary.almost_disjoint {d k:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) (B: Fin k → Box d) (hEB: E = ⋃ i, (B i).toSet) (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) : hE.measure = ∑ i, |B i|ᵥ := by
  induction k generalizing E with
  | zero =>
    -- E = ⋃ i : Fin 0, (B i).toSet = ∅, so hE.measure = 0 = ∑ i : Fin 0, ...
    simp_all
  | succ n ih =>
    -- Define B' : Fin n → Box d as the first n boxes, and B_last as the last
    let B' : Fin n → Box d := fun i => B (Fin.castSucc i)
    let E' : Set (EuclideanSpace' d) := ⋃ i : Fin n, (B' i).toSet
    let B_last := B (Fin.last n)

    -- Split E using the helper lemma
    have hE_split : E = E' ∪ B_last.toSet := by
      simp only [hEB, E', B', B_last]
      exact Fin.iUnion_succ_eq_union_last (fun i => (B i).toSet)

    -- Show B' is almost disjoint using helper
    have hdisj' : Pairwise (Function.onFun AlmostDisjoint B') :=
      AlmostDisjoint.pairwise_castSucc hdisj

    -- E' is elementary (finite union of boxes)
    have hE'_elem : IsElementary E' := by
      classical
      have h_eq : E' = ⋃ E ∈ (Finset.univ : Finset (Fin n)).image (fun i => (B' i).toSet), E := by
        ext x
        simp only [E', Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and, exists_prop]
        constructor
        · intro ⟨i, hi⟩; exact ⟨(B' i).toSet, ⟨i, rfl⟩, hi⟩
        · intro ⟨_, ⟨i, rfl⟩, hi⟩; exact ⟨i, hi⟩
      rw [h_eq]
      apply IsElementary.union'
      intro E hE
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hE
      obtain ⟨i, rfl⟩ := hE
      exact IsElementary.box _

    -- Apply induction hypothesis to get measure of E'
    have hE'_eq : E' = ⋃ i, (B' i).toSet := rfl
    have hE'_measure : hE'_elem.measure = ∑ i : Fin n, (B' i).volume := ih hE'_elem B' hE'_eq hdisj'

    -- B_last is elementary (single box)
    have hB_last_elem : IsElementary B_last.toSet := IsElementary.box B_last

    -- Each B' i is almost-disjoint from B_last using helper
    have h_almost_disj_last : ∀ i : Fin n, AlmostDisjoint (B' i) B_last :=
      fun i => AlmostDisjoint.castSucc_last hdisj i

    -- Show interior E' ∩ interior B_last = ∅ (almost-disjoint as sets)
    have h_interior_disj : interior E' ∩ interior B_last.toSet = ∅ := by
      rw [← interior_inter]
      have h_inter_eq : E' ∩ B_last.toSet = ⋃ i : Fin n, ((B' i).toSet ∩ B_last.toSet) := by
        simp only [E', Set.iUnion_inter]
      rw [h_inter_eq]
      -- Prove interior of union is empty
      apply Set.eq_empty_of_forall_notMem
      intro y hy
      rw [mem_interior_iff_mem_nhds] at hy
      obtain ⟨U, hU_sub, hU_open, hy_in_U⟩ := mem_nhds_iff.mp hy
      -- y ∈ interior B_last (since the union is contained in B_last)
      have hy_int_Blast : y ∈ interior B_last.toSet := by
        apply interior_mono (Set.iUnion_subset fun i => Set.inter_subset_right)
        rw [mem_interior_iff_mem_nhds]
        exact mem_nhds_iff.mpr ⟨U, hU_sub, hU_open, hy_in_U⟩
      -- Define U' = U ∩ interior B_last
      let U' := U ∩ interior B_last.toSet
      have hU'_open : IsOpen U' := hU_open.inter isOpen_interior
      have hU'_nonempty : U'.Nonempty := ⟨y, hy_in_U, hy_int_Blast⟩
      -- U' ⊆ ⋃ i, frontier (B' i) (each point is in some B' i but not its interior)
      have h_U'_in_frontier : U' ⊆ ⋃ i : Fin n, frontier (B' i).toSet := by
        intro z ⟨hz_U, hz_int_Blast⟩
        have hz_union : z ∈ ⋃ i : Fin n, ((B' i).toSet ∩ B_last.toSet) := hU_sub hz_U
        simp only [Set.mem_iUnion] at hz_union ⊢
        obtain ⟨i, hz_Bi, _⟩ := hz_union
        use i
        rw [frontier_eq_closure_inter_closure]
        refine ⟨subset_closure hz_Bi, ?_⟩
        rw [mem_closure_iff]
        intro V hV_open hz_V
        by_contra h_empty
        push_neg at h_empty
        rw [Set.eq_empty_iff_forall_notMem] at h_empty
        have hV_sub : V ⊆ (B' i).toSet := fun w hw => by
          by_contra h_not_in
          exact h_empty w ⟨hw, h_not_in⟩
        have hz_int_Bi : z ∈ interior (B' i).toSet := by
          rw [mem_interior_iff_mem_nhds]
          exact Filter.mem_of_superset (hV_open.mem_nhds hz_V) hV_sub
        have h_disj := h_almost_disj_last i
        rw [AlmostDisjoint, Set.eq_empty_iff_forall_notMem] at h_disj
        exact h_disj z ⟨hz_int_Bi, hz_int_Blast⟩
      -- Use the helper: finite union of box frontiers has empty interior
      have h_union_empty_int : interior (⋃ i : Fin n, frontier (B' i).toSet) = ∅ :=
        interior_iUnion_Box_frontier_eq_empty B'
      -- U' ⊆ set with empty interior, but U' is open nonempty. Contradiction!
      have : interior U' ⊆ interior (⋃ i : Fin n, frontier (B' i).toSet) := interior_mono h_U'_in_frontier
      rw [h_union_empty_int] at this
      exact Set.not_nonempty_empty ((Set.eq_empty_of_subset_empty this).symm ▸ (hU'_open.interior_eq ▸ hU'_nonempty))

    -- Apply measure additivity for almost-disjoint sets
    have h_union_elem : IsElementary (E' ∪ B_last.toSet) := hE'_elem.union hB_last_elem
    have h_measure_add : h_union_elem.measure = hE'_elem.measure + hB_last_elem.measure :=
      IsElementary.measure_of_almostDisjUnion hE'_elem hB_last_elem h_interior_disj
    have h_measure_eq : hE.measure = h_union_elem.measure :=
      IsElementary.measure_eq_of_set_eq hE h_union_elem hE_split
    have h_B_last_measure : hB_last_elem.measure = B_last.volume :=
      IsElementary.measure_of_box B_last

    -- Final computation
    rw [Fin.sum_univ_castSucc, h_measure_eq, h_measure_add, hE'_measure, h_B_last_measure]

/-- Restricting pairwise almost-disjoint from ℕ to Fin N preserves the property. -/
lemma AlmostDisjoint.restrict_fin {d : ℕ} {B : ℕ → Box d}
    (h : Pairwise (Function.onFun AlmostDisjoint B)) (N : ℕ) :
    Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => B i.val)) := by
  intro i j hij
  simp only [Function.onFun]
  apply h
  intro heq
  exact hij (Fin.ext heq)

/-- For nonneg Real sequences, if all partial sums are ≤ c (an EReal bound), then tsum ≤ c.
    This is the converse direction of `EReal.finset_sum_le_tsum`. -/
lemma EReal.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : EReal}
    (hf : ∀ n, 0 ≤ f n) (h : ∀ N, (∑ i ∈ Finset.range N, f i : EReal) ≤ c) :
    ∑' n, (f n).toEReal ≤ c := by
  -- Convert to ENNReal where tsum_le_of_sum_range_le is available
  let g : ℕ → ENNReal := fun n => ENNReal.ofReal (f n)
  -- Show (f n).toEReal = (g n : EReal)
  have hf_eq : ∀ n, (f n).toEReal = (g n : EReal) := fun n => by
    simp only [g, EReal.coe_ennreal_ofReal, max_eq_left (hf n)]
  -- Rewrite tsum using term equality
  have h_tsum_eq : ∑' n, (f n).toEReal = (∑' n, g n : ENNReal).toEReal := by
    have h1 : ∑' n, (f n).toEReal = ∑' n, (g n : EReal) := tsum_congr hf_eq
    have h2 : ∑' n, (g n : EReal) = (∑' n, g n : ENNReal).toEReal := by
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := by simp
        map_add' := EReal.coe_ennreal_add
      }
      have h_map : φ (∑' n, g n) = ∑' n, φ (g n) :=
        Summable.map_tsum (f := g) ENNReal.summable φ continuous_coe_ennreal_ereal
      exact h_map.symm
    exact h1.trans h2
  rw [h_tsum_eq]
  -- If c = ⊤, trivially true
  by_cases hc : c = ⊤
  · rw [hc]; exact le_top
  -- c ≥ 0 since it bounds nonneg partial sums
  have hc_nn : 0 ≤ c := by
    have h0 : (∑ i ∈ Finset.range 0, f i : EReal) ≤ c := h 0
    simp at h0; exact h0
  -- Get partial sum bounds in ENNReal
  have h_enn : ∀ N, ∑ i ∈ Finset.range N, g i ≤ c.toENNReal := by
    intro N
    have h_sum_eq : (∑ i ∈ Finset.range N, g i : ENNReal).toEReal = (∑ i ∈ Finset.range N, f i : EReal) := by
      rw [EReal.coe_ennreal_finset_sum]
      exact Finset.sum_congr rfl (fun n _ => (hf_eq n).symm)
    have h_le : (∑ i ∈ Finset.range N, g i : ENNReal).toEReal ≤ c := by rw [h_sum_eq]; exact h N
    rw [← EReal.coe_toENNReal hc_nn] at h_le
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h_le
  have h_tsum_enn : ∑' n, g n ≤ c.toENNReal := ENNReal.tsum_le_of_sum_range_le h_enn
  -- Convert back: ↑(∑' g) ≤ ↑(c.toENNReal) and c.toENNReal.toEReal = c (when 0 ≤ c)
  have h_coe_le : (∑' n, g n : ENNReal).toEReal ≤ (c.toENNReal).toEReal :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_tsum_enn
  calc (∑' n, g n : ENNReal).toEReal ≤ (c.toENNReal).toEReal := h_coe_le
    _ = c := EReal.coe_toENNReal hc_nn

/-- Lemma 1.2.9 (Outer measure of countable unions of almost disjoint boxes).
    For pairwise almost disjoint boxes, m*(⋃ Bᵢ) = ∑' m*(Bᵢ) = ∑' |Bᵢ|. -/
theorem Lebesgue_outer_measure.union_of_almost_disjoint {d:ℕ} {B : ℕ → Box d} (h : Pairwise (Function.onFun AlmostDisjoint B)) :
    Lebesgue_outer_measure (⋃ i, (B i).toSet) = ∑' i, Lebesgue_outer_measure (B i).toSet := by
  -- Simplify: m*(Bᵢ) = |Bᵢ| for each box (Lemma 1.2.6 + measure_of_box)
  have h_box_measure : ∀ i, Lebesgue_outer_measure (B i).toSet = (B i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box (B i)),
        IsElementary.measure_of_box]
  simp_rw [h_box_measure]
  -- The proof establishes equality by showing both ≤ and ≥
  apply le_antisymm
  -- Upper bound: m*(⋃ Bᵢ) ≤ ∑' |Bᵢ| by countable subadditivity
  · calc Lebesgue_outer_measure (⋃ i, (B i).toSet)
        ≤ ∑' i, Lebesgue_outer_measure (B i).toSet := Lebesgue_outer_measure.union_le _
      _ = ∑' i, (B i).volume.toEReal := by simp_rw [h_box_measure]
  -- Lower bound: ∑' |Bᵢ| ≤ m*(⋃ Bᵢ) by taking limit of finite partial sums
  · -- For each N, the finite union ⋃ i : Fin N, (B i) is contained in ⋃ i, (B i)
    -- So m*(⋃ i : Fin N, (B i)) ≤ m*(⋃ i, (B i)) by monotonicity
    -- And m*(⋃ i : Fin N, (B i)) = ∑ i : Fin N, |B i| by IsElementary.almost_disjoint
    -- Taking N → ∞ gives the result

    -- Step 1: For each N, show finite partial sum ≤ outer measure
    have h_finite_le : ∀ N : ℕ, (∑ i : Fin N, (B i.val).volume : EReal) ≤
        Lebesgue_outer_measure (⋃ i, (B i).toSet) := by
      intro N
      -- The finite union is contained in the countable union
      have h_subset : (⋃ i : Fin N, (B i.val).toSet) ⊆ (⋃ i, (B i).toSet) := by
        apply Set.iUnion_subset
        intro i
        exact Set.subset_iUnion (fun n => (B n).toSet) i.val
      -- By monotonicity: m*(finite union) ≤ m*(countable union)
      have h_mono := Lebesgue_outer_measure.mono h_subset
      -- The finite union is elementary (union of boxes)
      have hElem : IsElementary (⋃ i : Fin N, (B i.val).toSet) :=
        IsElementary.iUnion_boxes (fun i : Fin N => B i.val)
      -- m*(finite union) = m(finite union) since it's elementary
      have h_elem_eq : Lebesgue_outer_measure (⋃ i : Fin N, (B i.val).toSet) = hElem.measure :=
        Lebesgue_outer_measure.elementary _ hElem
      -- Pairwise almost disjoint for Fin N
      have h_pw : Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => B i.val)) :=
        AlmostDisjoint.restrict_fin h N
      -- m(finite union) = ∑ |B i| by IsElementary.almost_disjoint
      have h_sum_eq : hElem.measure = ∑ i : Fin N, (B i.val).volume :=
        IsElementary.almost_disjoint hElem (fun i : Fin N => B i.val) rfl h_pw
      have h_coe_sum : (∑ i : Fin N, (B i.val).volume : EReal) = (∑ i : Fin N, (B i.val).volume : ℝ).toEReal := by
        rw [EReal.coe_finset_sum (fun i _ => Box.volume_nonneg (B i.val))]
      calc (∑ i : Fin N, (B i.val).volume : EReal)
          = ((∑ i : Fin N, (B i.val).volume : ℝ) : EReal) := h_coe_sum
        _ = (hElem.measure : EReal) := by rw [h_sum_eq]
        _ = Lebesgue_outer_measure (⋃ i : Fin N, (B i.val).toSet) := h_elem_eq.symm
        _ ≤ Lebesgue_outer_measure (⋃ i, (B i).toSet) := h_mono

    -- Step 2: Take limit - convert Fin N sum to Finset.range N sum and use EReal lemma
    have h_range_le : ∀ N : ℕ, (∑ i ∈ Finset.range N, (B i).volume : EReal) ≤
        Lebesgue_outer_measure (⋃ i, (B i).toSet) := by
      intro N
      have h_eq : (∑ i ∈ Finset.range N, ((B i).volume : EReal)) = (∑ i : Fin N, ((B i.val).volume : EReal)) := by
        conv_lhs => rw [← Fin.sum_univ_eq_sum_range (fun i => ((B i).volume : EReal)) N]
      rw [h_eq]
      exact h_finite_le N

    -- Step 3: Apply EReal.tsum_le_of_sum_range_le
    exact EReal.tsum_le_of_sum_range_le (fun n => Box.volume_nonneg (B n)) h_range_le

theorem Lebesgue_outer_measure.univ {d:ℕ} {hd: 0 < d} : Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) = ⊤ := by
  -- Strategy: Show m*(univ) ≥ N for any N by taking N disjoint unit boxes, hence m*(univ) = ⊤

  -- Define unit box at integer lattice point a
  let UnitBox : (Fin d → ℤ) → Box d := fun a => { side := fun i => Icc (a i : ℝ) ((a i : ℝ) + 1) }

  -- Each unit box has volume 1
  have h_vol : ∀ a : Fin d → ℤ, (UnitBox a).volume = 1 := by
    intro a
    simp only [Box.volume, UnitBox]
    simp only [BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
    simp only [add_sub_cancel_left]
    simp only [max_eq_left (by norm_num : (0:ℝ) ≤ 1)]
    simp only [Finset.prod_const_one]

  -- Unit boxes at different lattice points have disjoint interiors
  have h_almost_disj : ∀ a b : Fin d → ℤ, a ≠ b → AlmostDisjoint (UnitBox a) (UnitBox b) := by
    intro a b hab
    simp only [AlmostDisjoint]
    -- Interior of Icc-box is Ioo-box
    have h_int : ∀ c : Fin d → ℤ, interior (UnitBox c).toSet =
        {x | ∀ i, x i ∈ Set.Ioo (c i : ℝ) ((c i : ℝ) + 1)} := by
      intro c
      rw [Box.interior_toSet]
      ext x; simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_setOf_eq, UnitBox, BoundedInterval.toSet, interior_Icc]; rfl
    rw [h_int a, h_int b]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ha hb
    apply hab
    funext i
    -- ha says: ∀ j, x j ∈ Ioo (a j) (a j + 1)
    -- So for coordinate i: a i < x i < a i + 1, meaning ⌊x i⌋ = a i
    have hai : x i ∈ Set.Ioo (a i : ℝ) ((a i : ℝ) + 1) := ha i
    have hbi : x i ∈ Set.Ioo (b i : ℝ) ((b i : ℝ) + 1) := hb i
    rw [Set.mem_Ioo] at hai hbi
    have ha_floor : (⌊x i⌋ : ℤ) = a i := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hai.1.le
      · exact_mod_cast hai.2
    have hb_floor : (⌊x i⌋ : ℤ) = b i := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hbi.1.le
      · exact_mod_cast hbi.2
    exact ha_floor.symm.trans hb_floor

  -- For any N, take N disjoint unit boxes (all with first coordinate 0,..,N-1, rest 0)
  have h_arb_large : ∀ N : ℕ, (N : EReal) ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) := by
    intro N
    -- Define N unit boxes at (0,0,...), (1,0,...), ..., (N-1,0,...)
    let pts : Fin N → (Fin d → ℤ) := fun n => fun i =>
      if i = ⟨0, hd⟩ then (n : ℤ) else 0
    -- These points are all distinct
    have h_pts_inj : Function.Injective pts := by
      intro m n hmn
      have : pts m ⟨0, hd⟩ = pts n ⟨0, hd⟩ := by rw [hmn]
      simp only [pts, ↓reduceIte] at this
      exact Fin.ext (Int.ofNat_injective this)
    -- The union of these N unit boxes is contained in univ
    have h_subset : (⋃ n : Fin N, (UnitBox (pts n)).toSet) ⊆ Set.univ := Set.subset_univ _
    -- By monotonicity
    -- The boxes are pairwise almost disjoint
    have h_pw : Pairwise (Function.onFun AlmostDisjoint (fun n : Fin N => UnitBox (pts n))) := by
      intro i j hij
      simp only [Function.onFun]
      apply h_almost_disj
      intro heq
      exact hij (h_pts_inj heq)
    -- Apply IsElementary.almost_disjoint for finite unions
    have hElem : IsElementary (⋃ n : Fin N, (UnitBox (pts n)).toSet) :=
      IsElementary.iUnion_boxes (fun n => UnitBox (pts n))

    -- N = ∑ |UnitBox| because each has volume 1
    have h_sum_vol : (∑ n : Fin N, (UnitBox (pts n)).volume) = N := by
      simp only [h_vol, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]

    -- ∑ volumes = measure of union (by IsElementary.almost_disjoint)
    have h_elem_eq : hElem.measure = ∑ n : Fin N, (UnitBox (pts n)).volume :=
      IsElementary.almost_disjoint hElem (fun n => UnitBox (pts n)) rfl h_pw

    calc (N : EReal)
        = ((N : ℕ) : ℝ) := (EReal.coe_coe_eq_natCast N).symm
      _ = ↑(∑ n : Fin N, (UnitBox (pts n)).volume) := by rw [h_sum_vol]
      _ = ↑hElem.measure := by rw [h_elem_eq]
      _ = Lebesgue_outer_measure (⋃ n : Fin N, (UnitBox (pts n)).toSet) := by
          rw [← Lebesgue_outer_measure.elementary _ hElem]
      _ ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) :=
          Lebesgue_outer_measure.mono h_subset

  -- Since m*(univ) ≥ N for all N, we have m*(univ) = ⊤
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  -- Find N > r
  obtain ⟨N, hN⟩ := exists_nat_gt r
  calc (r : EReal) < (N : ℝ) := EReal.coe_lt_coe hN
    _ = (N : EReal) := EReal.coe_coe_eq_natCast N
    _ ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) := h_arb_large N

/-- Remark 1.2.10 -/
theorem Box.sum_volume_eq {d:ℕ} (B B': ℕ → Box d) (hdisj: Pairwise (Function.onFun AlmostDisjoint B)) (hdisj': Pairwise (Function.onFun AlmostDisjoint B')) (hcover: (⋃ n, (B n).toSet) = (⋃ n, (B' n).toSet)) :
    ∑' n, (B n).volume = ∑' n, (B' n).volume := by
  -- Establish outer measure equality using union_of_almost_disjoint (Lemma 1.2.9)
  have hB := Lebesgue_outer_measure.union_of_almost_disjoint hdisj
  have hB' := Lebesgue_outer_measure.union_of_almost_disjoint hdisj'
  -- Simplify: m*(Bᵢ) = |Bᵢ|.toEReal for each box
  have h_box : ∀ i, Lebesgue_outer_measure (B i).toSet = (B i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _), IsElementary.measure_of_box]
  have h_box' : ∀ i, Lebesgue_outer_measure (B' i).toSet = (B' i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _), IsElementary.measure_of_box]
  simp_rw [h_box] at hB
  simp_rw [h_box'] at hB'
  -- Now: ∑' |B n|.toEReal = m*(⋃ B n) = m*(⋃ B' n) = ∑' |B' n|.toEReal
  have h_eq : (∑' n, ((B n).volume : EReal)) = (∑' n, ((B' n).volume : EReal)) := by
    rw [← hB, hcover, hB']
  -- Define ENNReal versions and work through ENNReal
  have h_vol_nn : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
  have h_vol_nn' : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
  let f : ℕ → ENNReal := fun n => ENNReal.ofReal (B n).volume
  let f' : ℕ → ENNReal := fun n => ENNReal.ofReal (B' n).volume
  -- Key: (B n).volume.toEReal = (f n : EReal) for nonneg volumes
  have hf_eq : ∀ n, ((B n).volume : EReal) = (f n : EReal) := fun n => by
    simp only [f, EReal.coe_ennreal_ofReal, max_eq_left (h_vol_nn n)]
  have hf'_eq : ∀ n, ((B' n).volume : EReal) = (f' n : EReal) := fun n => by
    simp only [f', EReal.coe_ennreal_ofReal, max_eq_left (h_vol_nn' n)]
  -- Rewrite h_eq using ENNReal
  simp_rw [hf_eq, hf'_eq] at h_eq
  -- ENNReal tsums commute with coercion to EReal
  have h_ennreal_eq : (∑' n, f n : ENNReal) = ∑' n, f' n := by
    have h_coe : ∀ (g : ℕ → ENNReal), (∑' n, g n : ENNReal).toEReal = ∑' n, (g n : EReal) := by
      intro g
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := by simp
        map_add' := EReal.coe_ennreal_add
      }
      exact Summable.map_tsum ENNReal.summable φ continuous_coe_ennreal_ereal
    rw [← h_coe f, ← h_coe f'] at h_eq
    exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp h_eq
  -- Transfer back to ℝ using ENNReal.toReal
  have h_toReal_eq : (∑' n, f n).toReal = (∑' n, f' n).toReal := by rw [h_ennreal_eq]
  -- Use ENNReal.tsum_toReal_eq for finite-valued functions
  have hf_ne_top : ∀ n, f n ≠ ⊤ := fun n => ENNReal.ofReal_ne_top
  have hf'_ne_top : ∀ n, f' n ≠ ⊤ := fun n => ENNReal.ofReal_ne_top
  rw [ENNReal.tsum_toReal_eq hf_ne_top, ENNReal.tsum_toReal_eq hf'_ne_top] at h_toReal_eq
  -- Simplify: (ENNReal.ofReal x).toReal = x for x ≥ 0
  simp only [f, f', ENNReal.toReal_ofReal (h_vol_nn _), ENNReal.toReal_ofReal (h_vol_nn' _)] at h_toReal_eq
  exact h_toReal_eq

/-- Exercise 1.2.5: For any set that equals a countable union of almost disjoint boxes,
    the Lebesgue outer measure equals the Jordan inner measure. -/
theorem Lebesgue_outer_measure.eq_Jordan_inner_of_boxes {d:ℕ} (E: Set (EuclideanSpace' d)) (B: ℕ → Box d)
    (hE: E = ⋃ n, (B n).toSet) (hdisj: Pairwise (Function.onFun AlmostDisjoint B)) :
    Lebesgue_outer_measure E = Jordan_inner_measure E := by
  sorry

def IsCube {d:ℕ} (B: Box d) : Prop := ∃ r, ∀ i, |B.side i|ₗ = r

noncomputable def DyadicCube {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : Box d := { side := fun i ↦ Icc (a i/2^n) ((a i + 1)/2^n) }

lemma DyadicCube.isCube {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : IsCube (DyadicCube n a) := by
  -- All sides have length 1/2^n
  use |2^(-n : ℤ)|
  intro i
  simp only [DyadicCube, BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
  -- Show ((a i + 1)/2^n - a i/2^n) = 1/2^n
  have h : (↑(a i) + 1) / (2:ℝ) ^ n - ↑(a i) / (2:ℝ) ^ n = (2:ℝ) ^ (-n) := by
    simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  rw [h]
  simp only [max_eq_left (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-n))]
  exact (abs_of_nonneg (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-n))).symm

def Box.IsDyadicAtScale {d:ℕ} (B: Box d) (n:ℤ) : Prop := ∃ a: Fin d → ℤ, B = DyadicCube n a

def Box.IsDyadic {d:ℕ} (B: Box d) : Prop := ∃ n:ℕ, B.IsDyadicAtScale n

/-- Dyadic boxes have all sides as closed intervals (Icc). -/
lemma Box.IsDyadic.all_sides_Icc {d : ℕ} {B : Box d} (hB : B.IsDyadic) :
    ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b := by
  obtain ⟨n, ⟨a, rfl⟩⟩ := hB
  intro i
  use a i / 2^n, (a i + 1) / 2^n
  rfl

-- Helper lemmas for Lemma 1.2.11
namespace DyadicCube
/-- The sidelength of a dyadic cube at scale n is 2^(-n). -/
lemma sidelength {d:ℕ} (n:ℤ) (a: Fin d → ℤ) (i : Fin d) :
    |(DyadicCube n a).side i|ₗ = (2:ℝ)^(-n) := by
  simp only [DyadicCube, BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
  have h : (↑(a i) + 1) / (2:ℝ) ^ n - ↑(a i) / (2:ℝ) ^ n = (2:ℝ) ^ (-n) := by
    simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  rw [h, max_eq_left (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-n))]

/-- Dyadic cubes at scale n ≥ 0 have sidelength at most 1. -/
lemma sidelength_le_one {d:ℕ} {n:ℕ} (a: Fin d → ℤ) (i : Fin d) :
    |(DyadicCube (n:ℤ) a).side i|ₗ ≤ 1 := by
  rw [DyadicCube.sidelength]
  have h1 : (1:ℝ) ≤ 2^n := by
    calc (1:ℝ) = 2^(0:ℕ) := by norm_num
      _ ≤ 2^n := pow_le_pow_right₀ (by norm_num : 1 ≤ (2:ℝ)) (Nat.zero_le n)
  calc (2:ℝ)^(-(n:ℤ)) = 1 / 2^n := by rw [zpow_neg, zpow_natCast]; ring
    _ ≤ 1 / 1 := by apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
    _ = 1 := by norm_num

/-- The interior of a dyadic cube. -/
lemma interior {d:ℕ} (n:ℤ) (a: Fin d → ℤ) :
    interior (DyadicCube n a).toSet =
    {x | ∀ i, x i ∈ Set.Ioo ((a i : ℝ) / 2^n) (((a i : ℝ) + 1) / 2^n)} := by
  rw [Box.interior_toSet]
  ext x; simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_setOf_eq, DyadicCube, BoundedInterval.toSet, interior_Icc]; rfl

/-- Dyadic cubes at the same scale with different indices have disjoint interiors. -/
lemma almost_disjoint_same_scale {d:ℕ} {n:ℤ} {a b : Fin d → ℤ} (hab : a ≠ b) :
    AlmostDisjoint (DyadicCube n a) (DyadicCube n b) := by
  simp only [AlmostDisjoint]
  rw [DyadicCube.interior, DyadicCube.interior]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro ha hb
  apply hab
  funext i
  have hai : x i ∈ Set.Ioo ((a i : ℝ) / 2^n) (((a i : ℝ) + 1) / 2^n) := ha i
  have hbi : x i ∈ Set.Ioo ((b i : ℝ) / 2^n) (((b i : ℝ) + 1) / 2^n) := hb i
  rw [Set.mem_Ioo] at hai hbi
  -- Both intervals contain x i, so a i = b i
  have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
  have ha_floor : ⌊x i * 2^n⌋ = a i := by
    apply Int.floor_eq_iff.mpr
    constructor
    · calc (a i : ℝ) = (a i : ℝ) / 2^n * 2^n := by field_simp
        _ ≤ x i * 2^n := by nlinarith [hai.1]
    · calc x i * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith [hai.2]
        _ = (a i : ℝ) + 1 := by field_simp
  have hb_floor : ⌊x i * 2^n⌋ = b i := by
    apply Int.floor_eq_iff.mpr
    constructor
    · calc (b i : ℝ) = (b i : ℝ) / 2^n * 2^n := by field_simp
        _ ≤ x i * 2^n := by nlinarith [hbi.1]
    · calc x i * 2^n < ((b i : ℝ) + 1) / 2^n * 2^n := by nlinarith [hbi.2]
        _ = (b i : ℝ) + 1 := by field_simp
  exact ha_floor.symm.trans hb_floor

/-- The dyadic cubes at scale n cover all of ℝᵈ. -/
lemma cover_univ {d:ℕ} (n:ℤ) :
    (⋃ (a : Fin d → ℤ), (DyadicCube n a).toSet) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  use fun i => ⌊x i * 2^n⌋
  intro i
  simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
  have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
  constructor
  · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
    calc (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i * 2^n / 2^n :=
        div_le_div_of_nonneg_right h1 h2n_pos.le
      _ = x i := by field_simp
  · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
    have hle : x i < ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by
      calc x i = x i * 2^n / 2^n := by field_simp
        _ < (⌊x i * 2^n⌋ + 1) / 2^n := div_lt_div_of_pos_right h2 h2n_pos
        _ = ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by ring
    exact hle.le

/-- Dyadic cubes at the same scale are pairwise almost disjoint. -/
lemma pairwise_almost_disjoint {d:ℕ} (n:ℤ) :
    Pairwise (Function.onFun AlmostDisjoint (DyadicCube n : (Fin d → ℤ) → Box d)) := by
  intro a b hab
  simp only [Function.onFun]
  exact DyadicCube.almost_disjoint_same_scale hab

/-- Two dyadic cubes are either almost disjoint or one contains the other. -/
lemma nesting {d:ℕ} {n m : ℤ} {a : Fin d → ℤ} {b : Fin d → ℤ} :
    AlmostDisjoint (DyadicCube n a) (DyadicCube m b) ∨
    (DyadicCube n a).toSet ⊆ (DyadicCube m b).toSet ∨
    (DyadicCube m b).toSet ⊆ (DyadicCube n a).toSet := by
  -- Case analysis on the relationship between n and m
  rcases lt_trichotomy n m with hn | rfl | hm
  · -- n < m: The cube at scale m has smaller cells (2^(-m) < 2^(-n))
    -- Either DyadicCube m b ⊆ DyadicCube n a (if b is in the right position) or almost disjoint
    -- Check if DyadicCube m b ⊆ DyadicCube n a by checking containment of intervals
    by_cases h_subset : ∀ i, (a i : ℝ) / 2^n ≤ (b i : ℝ) / 2^m ∧ ((b i : ℝ) + 1) / 2^m ≤ ((a i : ℝ) + 1) / 2^n
    · -- DyadicCube m b ⊆ DyadicCube n a
      right; right
      intro x hx i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at hx ⊢
      have hxi := hx i
      exact ⟨le_trans (h_subset i).1 hxi.1, le_trans hxi.2 (h_subset i).2⟩
    · -- Not contained, so they are almost disjoint
      left
      push_neg at h_subset
      obtain ⟨i, hi⟩ := h_subset
      simp only [AlmostDisjoint, DyadicCube.interior]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro ha hb
      have hai := ha i
      have hbi := hb i
      have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
      have h2m_pos : (0:ℝ) < 2^m := zpow_pos (by norm_num : (0:ℝ) < 2) m
      have h_mn_pos : 0 < m - n := Int.sub_pos_of_lt hn
      have h_zpow_eq : (2:ℝ)^(m-n) * 2^n = 2^m := by
        rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
        congr 1
        omega
      -- hi says: if a_i/2^n ≤ b_i/2^m then (a_i+1)/2^n < (b_i+1)/2^m
      -- Case 1: a_i/2^n > b_i/2^m (the hypothesis of hi fails)
      -- Case 2: a_i/2^n ≤ b_i/2^m but (a_i+1)/2^n < (b_i+1)/2^m (hi applies)
      by_cases h_left : (b i : ℝ) / 2^m < (a i : ℝ) / 2^n
      · -- b_i/2^m < a_i/2^n: left endpoint of b is before left endpoint of a
        by_cases h_disj : ((b i : ℝ) + 1) / 2^m ≤ (a i : ℝ) / 2^n
        · -- Intervals (b_i/2^m, (b_i+1)/2^m) and (a_i/2^n, (a_i+1)/2^n) don't overlap
          linarith [hai.1, hbi.2]
        · -- Intervals overlap: b_i/2^m < a_i/2^n < (b_i+1)/2^m
          push_neg at h_disj
          -- a_i * 2^(m-n) lies strictly between b_i and b_i+1
          -- But a_i * 2^(m-n) is an integer (since m > n implies m-n > 0)
          have hlo : (b i : ℝ) < (a i : ℝ) * 2^(m-n) := by
            have h1 : (b i : ℝ) / 2^m * 2^m < (a i : ℝ) / 2^n * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (b i : ℝ) < (a i : ℝ) / 2^n * 2^m := h1
              _ = (a i : ℝ) * (2^m / 2^n) := by ring
              _ = (a i : ℝ) * 2^(m-n) := by rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
          have hhi : (a i : ℝ) * 2^(m-n) < (b i : ℝ) + 1 := by
            have h1 : (a i : ℝ) / 2^n * 2^m < ((b i : ℝ) + 1) / 2^m * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (a i : ℝ) * 2^(m-n) = (a i : ℝ) * (2^m / 2^n) := by
                    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
              _ = (a i : ℝ) / 2^n * 2^m := by ring
              _ < (b i : ℝ) + 1 := h1
          -- a_i * 2^(m-n) is an integer in (b_i, b_i+1), contradiction
          have h_int : ∃ k : ℤ, (a i : ℝ) * 2^(m-n) = k := by
            have h_pos_exp : ∃ p : ℕ, m - n = p ∧ 0 < p := ⟨(m-n).toNat, (Int.toNat_of_nonneg (le_of_lt h_mn_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use a i * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (b i : ℤ) < k ∧ k < b i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
      · -- ¬(b_i/2^m < a_i/2^n), so a_i/2^n ≤ b_i/2^m
        push_neg at h_left
        -- By hi: (a_i+1)/2^n < (b_i+1)/2^m
        have h_right := hi h_left
        by_cases h_disj : ((a i : ℝ) + 1) / 2^n ≤ (b i : ℝ) / 2^m
        · -- Intervals don't overlap
          linarith [hai.2, hbi.1]
        · -- Intervals overlap: b_i/2^m < (a_i+1)/2^n < (b_i+1)/2^m
          push_neg at h_disj
          -- (a_i+1) * 2^(m-n) lies strictly between b_i and b_i+1
          have hlo : (b i : ℝ) < ((a i : ℝ) + 1) * 2^(m-n) := by
            have h1 : (b i : ℝ) / 2^m * 2^m < ((a i : ℝ) + 1) / 2^n * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (b i : ℝ) < ((a i : ℝ) + 1) / 2^n * 2^m := h1
              _ = ((a i : ℝ) + 1) * (2^m / 2^n) := by ring
              _ = ((a i : ℝ) + 1) * 2^(m-n) := by rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
          have hhi : ((a i : ℝ) + 1) * 2^(m-n) < (b i : ℝ) + 1 := by
            have h1 : ((a i : ℝ) + 1) / 2^n * 2^m < ((b i : ℝ) + 1) / 2^m * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc ((a i : ℝ) + 1) * 2^(m-n) = ((a i : ℝ) + 1) * (2^m / 2^n) := by
                    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
              _ = ((a i : ℝ) + 1) / 2^n * 2^m := by ring
              _ < (b i : ℝ) + 1 := h1
          -- (a_i+1) * 2^(m-n) is an integer in (b_i, b_i+1), contradiction
          have h_int : ∃ k : ℤ, ((a i : ℝ) + 1) * 2^(m-n) = k := by
            have h_pos_exp : ∃ p : ℕ, m - n = p ∧ 0 < p := ⟨(m-n).toNat, (Int.toNat_of_nonneg (le_of_lt h_mn_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use (a i + 1) * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_add, Int.cast_one]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (b i : ℤ) < k ∧ k < b i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
  · -- n = m: Same scale, use almost_disjoint_same_scale or equality
    by_cases hab : a = b
    · subst hab
      right; left
      exact Set.Subset.refl _
    · left
      exact DyadicCube.almost_disjoint_same_scale hab
  · -- m < n: The cube at scale n has smaller cells (2^(-n) < 2^(-m))
    -- Either DyadicCube n a ⊆ DyadicCube m b (if a is in the right position) or almost disjoint
    by_cases h_subset : ∀ i, (b i : ℝ) / 2^m ≤ (a i : ℝ) / 2^n ∧ ((a i : ℝ) + 1) / 2^n ≤ ((b i : ℝ) + 1) / 2^m
    · -- DyadicCube n a ⊆ DyadicCube m b
      right; left
      intro x hx i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at hx ⊢
      have hxi := hx i
      exact ⟨le_trans (h_subset i).1 hxi.1, le_trans hxi.2 (h_subset i).2⟩
    · -- Not contained, so they are almost disjoint
      left
      push_neg at h_subset
      obtain ⟨i, hi⟩ := h_subset
      simp only [AlmostDisjoint, DyadicCube.interior]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro ha hb
      have hai := ha i
      have hbi := hb i
      have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
      have h2m_pos : (0:ℝ) < 2^m := zpow_pos (by norm_num : (0:ℝ) < 2) m
      have h_nm_pos : 0 < n - m := Int.sub_pos_of_lt hm
      -- hi says: if b_i/2^m ≤ a_i/2^n then (a_i+1)/2^n > (b_i+1)/2^m
      by_cases h_left : (a i : ℝ) / 2^n < (b i : ℝ) / 2^m
      · -- a_i/2^n < b_i/2^m: left endpoint of a is before left endpoint of b
        by_cases h_disj : ((a i : ℝ) + 1) / 2^n ≤ (b i : ℝ) / 2^m
        · -- Intervals don't overlap
          linarith [hai.2, hbi.1]
        · -- Intervals overlap: a_i/2^n < b_i/2^m < (a_i+1)/2^n
          push_neg at h_disj
          -- b_i * 2^(n-m) lies strictly between a_i and a_i+1
          have hlo : (a i : ℝ) < (b i : ℝ) * 2^(n-m) := by
            have h1 : (a i : ℝ) / 2^n * 2^n < (b i : ℝ) / 2^m * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (a i : ℝ) < (b i : ℝ) / 2^m * 2^n := h1
              _ = (b i : ℝ) * (2^n / 2^m) := by ring
              _ = (b i : ℝ) * 2^(n-m) := by rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
          have hhi : (b i : ℝ) * 2^(n-m) < (a i : ℝ) + 1 := by
            have h1 : (b i : ℝ) / 2^m * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (b i : ℝ) * 2^(n-m) = (b i : ℝ) * (2^n / 2^m) := by
                    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
              _ = (b i : ℝ) / 2^m * 2^n := by ring
              _ < (a i : ℝ) + 1 := h1
          -- b_i * 2^(n-m) is an integer in (a_i, a_i+1), contradiction
          have h_int : ∃ k : ℤ, (b i : ℝ) * 2^(n-m) = k := by
            have h_pos_exp : ∃ p : ℕ, n - m = p ∧ 0 < p := ⟨(n-m).toNat, (Int.toNat_of_nonneg (le_of_lt h_nm_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use b i * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (a i : ℤ) < k ∧ k < a i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
      · -- ¬(a_i/2^n < b_i/2^m), so b_i/2^m ≤ a_i/2^n
        push_neg at h_left
        -- By hi: (a_i+1)/2^n > (b_i+1)/2^m
        have h_right := hi h_left
        by_cases h_disj : ((b i : ℝ) + 1) / 2^m ≤ (a i : ℝ) / 2^n
        · -- Intervals don't overlap
          linarith [hai.1, hbi.2]
        · -- Intervals overlap: a_i/2^n < (b_i+1)/2^m < (a_i+1)/2^n
          push_neg at h_disj
          -- (b_i+1) * 2^(n-m) lies strictly between a_i and a_i+1
          have hlo : (a i : ℝ) < ((b i : ℝ) + 1) * 2^(n-m) := by
            have h1 : (a i : ℝ) / 2^n * 2^n < ((b i : ℝ) + 1) / 2^m * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (a i : ℝ) < ((b i : ℝ) + 1) / 2^m * 2^n := h1
              _ = ((b i : ℝ) + 1) * (2^n / 2^m) := by ring
              _ = ((b i : ℝ) + 1) * 2^(n-m) := by rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
          have hhi : ((b i : ℝ) + 1) * 2^(n-m) < (a i : ℝ) + 1 := by
            have h1 : ((b i : ℝ) + 1) / 2^m * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc ((b i : ℝ) + 1) * 2^(n-m) = ((b i : ℝ) + 1) * (2^n / 2^m) := by
                    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
              _ = ((b i : ℝ) + 1) / 2^m * 2^n := by ring
              _ < (a i : ℝ) + 1 := h1
          -- (b_i+1) * 2^(n-m) is an integer in (a_i, a_i+1), contradiction
          have h_int : ∃ k : ℤ, ((b i : ℝ) + 1) * 2^(n-m) = k := by
            have h_pos_exp : ∃ p : ℕ, n - m = p ∧ 0 < p := ⟨(n-m).toNat, (Int.toNat_of_nonneg (le_of_lt h_nm_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use (b i + 1) * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_add, Int.cast_one]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (a i : ℤ) < k ∧ k < a i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega

end DyadicCube
/-- For any point x in an open set E, there exists a dyadic cube containing x with the cube contained in E. -/
lemma IsOpen.exists_dyadic_cube_subset {d:ℕ} {E : Set (EuclideanSpace' d)} (hE : IsOpen E)
    {x : EuclideanSpace' d} (hx : x ∈ E) :
    ∃ n : ℕ, ∃ a : Fin d → ℤ, x ∈ (DyadicCube (n:ℤ) a).toSet ∧
    (DyadicCube (n:ℤ) a).toSet ⊆ E := by
  -- Since E is open, there exists ε > 0 such that B(x, ε) ⊆ E
  rw [Metric.isOpen_iff] at hE
  obtain ⟨ε, hε_pos, hball⟩ := hE x hx
  -- Choose n large enough that the dyadic cube containing x has diameter < ε
  -- Diameter of dyadic cube at scale n is ≤ √d * 2^(-n)
  -- We need √d * 2^(-n) < ε, i.e., √d / ε < 2^n
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Real.sqrt d / ε) (by norm_num : (1:ℝ) < 2)
  use n
  -- Find the dyadic cube containing x at scale n
  let a : Fin d → ℤ := fun i => ⌊x i * 2^n⌋
  use a
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  constructor
  · -- x ∈ DyadicCube n a
    intro i
    simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
      have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
      simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
      exact h2
    · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
      have h3 := div_lt_div_of_pos_right h2 h2n_pos
      simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h3
      exact h3.le
  · -- DyadicCube n a ⊆ E
    intro y hy
    apply hball
    simp only [Metric.mem_ball]
    -- y is in the dyadic cube containing x, so |y i - x i| ≤ 2^(-n) for all i
    have h2n_inv : (2:ℝ)^(-n:ℤ) = 1 / 2^n := by rw [zpow_neg, zpow_natCast]; ring
    have h_zpow : (2:ℝ) ^ (↑n:ℤ) = 2 ^ n := zpow_natCast 2 n
    have hyi : ∀ i, |y i - x i| ≤ 2^(-n:ℤ) := fun i => by
      have hyi_mem := hy i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc, h_zpow] at hyi_mem
      -- hyi_mem : ⌊x i * 2^n⌋ / 2^n ≤ y i ∧ y i ≤ (⌊x i * 2^n⌋ + 1) / 2^n
      have hxi_floor : (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i := by
        have h1 := Int.floor_le (x i * 2^n)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
        simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
        exact h2
      rw [abs_le, h2n_inv]
      -- We need: -1/2^n ≤ y i - x i ≤ 1/2^n
      have hbound : x i - 1 / 2^n ≤ (⌊x i * 2^n⌋ : ℝ) / 2^n := by
        have h1 := (Int.lt_floor_add_one (x i * 2^n)).le
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
        simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
        have heq : ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n = (⌊x i * 2^n⌋ : ℝ) / 2^n + 1 / 2^n := by ring
        linarith [heq, h2]
      have hwidth : ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n - (⌊x i * 2^n⌋ : ℝ) / 2^n = 1 / 2^n := by ring
      -- Lower bound: floor/2^n ≤ y i and x i - 1/2^n ≤ floor/2^n, so x i - 1/2^n ≤ y i
      refine ⟨?_, ?_⟩
      · linarith [hyi_mem.1, hbound]
      · -- Upper bound: y i ≤ (floor+1)/2^n and floor/2^n ≤ x i
        -- So y i - x i ≤ (floor+1)/2^n - floor/2^n = 1/2^n
        linarith [hyi_mem.2, hxi_floor, hwidth]
    -- dist y x ≤ √d * 2^(-n) < ε
    have hdist : dist y x ≤ Real.sqrt d * (2:ℝ)^(-n:ℤ) := by
      rw [EuclideanSpace.dist_eq]
      have hdist_eq : ∀ i, dist (y i) (x i) = |y i - x i| := fun i => Real.dist_eq (y i) (x i)
      simp_rw [hdist_eq]
      have hsqrt_mul : Real.sqrt d * (2:ℝ)^(-n:ℤ) = Real.sqrt (d * ((2:ℝ)^(-n:ℤ))^2) := by
        rw [Real.sqrt_mul (by positivity : (d:ℝ) ≥ 0), Real.sqrt_sq (by positivity)]
      rw [hsqrt_mul]
      apply Real.sqrt_le_sqrt
      calc ∑ i, |y i - x i|^2
          ≤ ∑ _i : Fin d, ((2:ℝ)^(-n:ℤ))^2 := by
            apply Finset.sum_le_sum
            intro i _
            have h := hyi i
            have h2n_nn : (0:ℝ) ≤ (2:ℝ)^(-n:ℤ) := by positivity
            exact sq_le_sq' (by nlinarith [abs_nonneg (y i - x i)]) h
        _ = d * ((2:ℝ)^(-n:ℤ))^2 := by rw [Finset.sum_const, Finset.card_fin]; ring
    calc dist y x ≤ Real.sqrt d * (2:ℝ)^(-n:ℤ) := hdist
      _ = Real.sqrt d / 2^n := by rw [h2n_inv]; ring
      _ < ε := by
          rw [div_lt_iff₀ h2n_pos]
          calc Real.sqrt d = Real.sqrt d / ε * ε := by field_simp
            _ < ε * 2^n := by nlinarith [hn, hε_pos]

/-- For a point x, the unique dyadic cube at scale n containing x. -/
noncomputable def dyadicCubeContaining {d:ℕ} (n:ℤ) (x : EuclideanSpace' d) : Box d :=
  DyadicCube n (fun i => ⌊x i * 2^n⌋)

/-- The dyadic cube containing x at scale n indeed contains x. -/
lemma dyadicCubeContaining_mem {d:ℕ} (n:ℤ) (x : EuclideanSpace' d) :
    x ∈ (dyadicCubeContaining n x).toSet := by
  intro i
  simp only [dyadicCubeContaining, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
  have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
  constructor
  · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
    calc (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i * 2^n / 2^n := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
      _ = x i := by field_simp
  · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
    have h3 : x i < ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by
      calc x i = x i * 2^n / 2^n := by field_simp
        _ < (⌊x i * 2^n⌋ + 1) / 2^n := div_lt_div_of_pos_right h2 h2n_pos
        _ = ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by ring
    exact h3.le

/-- The interior of a dyadic cube is nonempty. -/
lemma dyadicCubeInteriorNonempty {d:ℕ} (n:ℤ) (a: Fin d → ℤ) :
    (interior (s := (DyadicCube n a).toSet)).Nonempty := by
  rw [Box.interior_toSet]
  exact (Set.univ_pi_nonempty_iff.mpr (fun k => by
    simp only [DyadicCube, BoundedInterval.toSet, interior_Icc]
    exact Set.nonempty_Ioo.mpr (div_lt_div_of_pos_right (by linarith) (zpow_pos (by norm_num) _))
  )).preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).surjective

/-- At the same scale, dyadic cubes with different indices cannot have one contained in the other
    (since containment would imply empty interior for one). -/
lemma dyadicCubeNoProperContainmentSameScale {d:ℕ} {n:ℤ} {a b : Fin d → ℤ}
    (h_sub : (DyadicCube n a).toSet ⊆ (DyadicCube n b).toSet) : a = b := by
  by_contra hne
  have h_ad := DyadicCube.almost_disjoint_same_scale (n := n) (a := a) (b := b) hne
  simp only [AlmostDisjoint] at h_ad
  have h_int_sub : interior (s := (DyadicCube n a).toSet) ⊆ interior (s := (DyadicCube n b).toSet) :=
    interior_mono h_sub
  have h_int_eq : interior (s := (DyadicCube n a).toSet) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hx' := h_int_sub hx
    have hx_both : x ∈ interior (s := (DyadicCube n a).toSet) ∩
        interior (s := (DyadicCube n b).toSet) := ⟨hx, hx'⟩
    rw [h_ad] at hx_both
    exact hx_both
  exact Set.not_nonempty_empty (h_int_eq ▸ dyadicCubeInteriorNonempty n a)

/-- A larger dyadic cube (coarser scale n) cannot be contained in a smaller dyadic cube (finer scale m)
    when d > 0. This is because the sidelength 2^(-n) > 2^(-m) when n < m. -/
lemma dyadicCubeLargerNotInSmaller {d:ℕ} (hd : 0 < d) {n m : ℤ} (hnm : n < m)
    {a b : Fin d → ℤ} : ¬((DyadicCube n a).toSet ⊆ (DyadicCube m b).toSet) := by
  intro h_sub
  -- Pick any coordinate (d > 0 guarantees this exists)
  let i : Fin d := ⟨0, hd⟩
  -- Compare sidelengths: 2^(-n) > 2^(-m) when n < m
  have h_side_ineq : (2:ℝ)^(-m) < (2:ℝ)^(-n) := by
    apply zpow_lt_zpow_right₀ (by norm_num : 1 < (2:ℝ))
    omega
  -- Construct the left endpoint of DyadicCube n a
  let x_left : EuclideanSpace' d := .toLp 2 (fun j => (a j : ℝ) / 2^n)
  -- x_left is in DyadicCube n a (it's the left corner)
  have hx_left : x_left ∈ (DyadicCube n a).toSet := by
    intro j
    simp only [x_left, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · exact le_refl _
    · have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num) n
      apply le_of_lt
      apply div_lt_div_of_pos_right _ h2n_pos
      linarith
  -- Construct the right endpoint of DyadicCube n a
  let x_right : EuclideanSpace' d := .toLp 2 (fun j => ((a j : ℝ) + 1) / 2^n)
  -- x_right is in DyadicCube n a (it's the right corner)
  have hx_right : x_right ∈ (DyadicCube n a).toSet := by
    intro j
    simp only [x_right, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num) n
      apply le_of_lt
      apply div_lt_div_of_pos_right _ h2n_pos
      linarith
    · exact le_refl _
  -- Both endpoints are in DyadicCube m b by h_sub
  have h_left_in := h_sub hx_left i
  have h_right_in := h_sub hx_right i
  simp only [x_left, x_right, DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at h_left_in h_right_in
  -- From h_left_in: (a i)/2^n ≥ (b i)/2^m
  -- From h_right_in: ((a i)+1)/2^n ≤ ((b i)+1)/2^m
  -- So: 2^(-n) = ((a i)+1)/2^n - (a i)/2^n ≤ ((b i)+1)/2^m - (b i)/2^m = 2^(-m)
  have h_len_sub : (2:ℝ)^(-n) ≤ (2:ℝ)^(-m) := by
    have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num) n
    have h2m_pos : (0:ℝ) < 2^m := zpow_pos (by norm_num) m
    calc (2:ℝ)^(-n) = ((a i : ℝ) + 1) / 2^n - (a i : ℝ) / 2^n := by
            simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
      _ ≤ ((b i : ℝ) + 1) / 2^m - (b i : ℝ) / 2^m := by linarith [h_left_in.1, h_right_in.2]
      _ = (2:ℝ)^(-m) := by
            simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  linarith

/-- Lemma 1.2.11: Every open set is a countable union of almost disjoint dyadic cubes.
Note: every dyadic cube is nonempty
    Proof outline:
    1. For each x ∈ E, by exists_dyadic_cube_subset, there exists a dyadic cube containing x ⊆ E
    2. The set of all such dyadic cubes is countable (subset of ℕ × (Fin d → ℤ))
    3. Take maximal cubes (not strictly contained in another cube in the collection)
    4. By DyadicCube.nesting, distinct maximal cubes are almost disjoint
    5. E equals the union of these maximal cubes -/
theorem IsOpen.eq_union_boxes {d:ℕ} (hd : 0 < d) (E: Set (EuclideanSpace' d)) (hE: IsOpen E)
    (hE_nonempty : E.Nonempty) :
    ∃ B: ℕ → Box d, (E = ⋃ n, (B n).toSet) ∧ (∀ n, (B n).IsDyadic) ∧
    Pairwise (Function.onFun AlmostDisjoint B) := by
  classical
  -- Construct maximal dyadic cubes
  obtain ⟨x₀, hx₀⟩ := hE_nonempty
  -- Define the set of all dyadic cubes (at scale n ≥ 0) contained in E
  let Q : Set (ℕ × (Fin d → ℤ)) := { p | (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ E }
  -- Q is countable as a subset of ℕ × (Fin d → ℤ)
  have hQ_countable : Q.Countable := Set.countable_of_injective_of_countable_image
    (f := id) (fun _ _ _ _ h => h) (Set.countable_univ.mono (Set.subset_univ _))
  -- For each x ∈ E, find the minimal scale n such that the dyadic cube at scale n containing x is in Q
  -- Minimal scale corresponds to maximal cube (smaller n = coarser = larger cubes)
  have h_exists_min_scale : ∀ x ∈ E, ∃ n₀ : ℕ, ∃ a : Fin d → ℤ,
      x ∈ (DyadicCube (n₀:ℤ) a).toSet ∧ (DyadicCube (n₀:ℤ) a).toSet ⊆ E ∧
      (∀ m < n₀, ∀ b : Fin d → ℤ, x ∈ (DyadicCube (m:ℤ) b).toSet → ¬(DyadicCube (m:ℤ) b).toSet ⊆ E) := by
    intro x hx
    -- By exists_dyadic_cube_subset, there exists some scale with cube ⊆ E
    obtain ⟨n, a, hxa, hcube⟩ := hE.exists_dyadic_cube_subset hx
    -- Find the minimal such scale using Nat.find
    let P : ℕ → Prop := fun m => ∃ b : Fin d → ℤ, x ∈ (DyadicCube (m:ℤ) b).toSet ∧ (DyadicCube (m:ℤ) b).toSet ⊆ E
    have hP : ∃ m, P m := ⟨n, a, hxa, hcube⟩
    let n₀ := Nat.find hP
    obtain ⟨a₀, ha₀_mem, ha₀_sub⟩ := Nat.find_spec hP
    use n₀, a₀, ha₀_mem, ha₀_sub
    intro m hm b hb_mem hsub
    exact Nat.find_min hP hm ⟨b, hb_mem, hsub⟩
  -- Define maximal cubes: for each x ∈ E, pick the cube at minimal scale
  -- Define the set of maximal cube indices
  let Q_max : Set (ℕ × (Fin d → ℤ)) := { p | (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ E ∧
    ∀ q : ℕ × (Fin d → ℤ), q.1 < p.1 →
      (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ (DyadicCube (q.1 : ℤ) q.2).toSet →
      ¬(DyadicCube (q.1 : ℤ) q.2).toSet ⊆ E }
  -- Q_max is countable
  have hQ_max_countable : Q_max.Countable :=
    Set.countable_of_injective_of_countable_image (f := id) (fun _ _ _ _ h => h)
      (Set.countable_univ.mono (Set.subset_univ _))
  -- Q_max is nonempty (since E is nonempty)
  have hQ_max_nonempty : Q_max.Nonempty := by
    obtain ⟨n₀, a₀, hx₀_mem, hsub, hmin⟩ := h_exists_min_scale x₀ hx₀
    use ⟨n₀, a₀⟩
    simp only [Set.mem_setOf_eq, Q_max]
    constructor
    · exact hsub
    · intro q hq hsub'
      -- If DyadicCube n₀ a₀ ⊆ DyadicCube q.1 q.2 with q.1 < n₀, then q.1 is a smaller scale
      -- containing x₀, contradicting minimality
      have hx₀_in_q : x₀ ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hx₀_mem
      exact hmin q.1 hq q.2 hx₀_in_q
  -- Q_max is infinite: we show this by cases on d
  have hQ_max_infinite : Q_max.Infinite := by
    -- d > 0 by hypothesis hd, so we proceed directly
      -- At scale 0, dyadic cubes are [a₁, a₁+1] × ... × [aₐ, aₐ+1] for a ∈ ℤᵈ
      -- If E = univ, all scale-0 cubes are in Q_max
      -- If E ≠ univ, near the boundary, cubes at arbitrarily fine scales are maximal
      by_cases hE_univ : E = Set.univ
      · -- E = univ: All scale-0 cubes are maximal (no coarser scale exists)
        -- First, show Fin d → ℤ is infinite (since d > 0 and ℤ is infinite)
        haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        haveI : Infinite (Fin d → ℤ) := Function.infinite_of_right
        -- Now inject Fin d → ℤ into Q_max via a ↦ (0, a)
        apply Set.infinite_of_injective_forall_mem
          (f := fun a : Fin d → ℤ => (0, a))
          (fun a b hab => (Prod.mk.inj hab).2)
        intro a
        constructor
        · simp only [hE_univ]; exact Set.subset_univ _
        · intro q hq _; omega
      · -- E ≠ univ: Near boundary, cubes at arbitrarily fine scales are maximal
        -- Key insight: Since E ≠ univ, there exists y ∉ E. For any x ∈ E, the maximal
        -- cube containing x cannot contain y. As we move x closer to y (within E),
        -- the maximal cubes must become smaller, giving arbitrarily fine scales.
        -- We show Q_max is infinite by showing the scales are unbounded.
        by_contra hfin
        rw [Set.not_infinite] at hfin
        -- Q_max is finite, so there's a maximum scale N among all maximal cubes
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ∈ Q_max, p.1 ≤ N := by
          obtain ⟨p, hp⟩ := Set.Finite.exists_maximalFor Prod.fst Q_max hfin hQ_max_nonempty
          use p.1
          intro q hq
          by_contra hlt
          push_neg at hlt
          have hle := hp.le_of_le hq hlt.le
          omega
        -- But there exist points in E whose maximal cube has scale > N
        -- These are points close to the boundary (complement of E)
        -- Since E ≠ univ, ∃ y ∉ E. Take x ∈ E close to y.
        have hEc_nonempty : Eᶜ.Nonempty := by
          rw [Set.nonempty_compl]
          exact hE_univ
        obtain ⟨y, hy⟩ := hEc_nonempty
        -- Proof strategy:
        -- 1. Every x ∈ E has a maximal cube with scale ≤ N, hence sidelength ≥ 2^(-N)
        -- 2. This cube is contained in E and contains an open ball around x
        -- 3. So every x ∈ E has dist(x, Eᶜ) ≥ 2^(-N)·sqrt(d)/2 (roughly)
        -- 4. This means E is closed (closure E = E)
        -- 5. E is open, closed, nonempty → E = univ by connectedness
        -- 6. Contradicts E ≠ univ
        --
        -- Step 1: Show E is closed
        have hE_closed : IsClosed E := by
          -- Strategy: Q_max is finite, so E is a finite union of dyadic cubes
          -- Each dyadic cube is closed (product of closed intervals Icc)
          -- Finite union of closed sets is closed
          -- First, show each dyadic cube toSet is closed
          have h_cube_closed : ∀ p ∈ Q_max, IsClosed (DyadicCube (p.1 : ℤ) p.2).toSet := by
            intro p _
            -- DyadicCube is product of Icc intervals, which are closed
            exact Box.isClosed_toSet_of_Icc _ (fun i => ⟨_, _, rfl⟩)
          -- E equals the union of cubes in Q_max
          have hE_union_Qmax : E = ⋃ p ∈ Q_max, (DyadicCube (p.1 : ℤ) p.2).toSet := by
            ext x
            constructor
            · intro hx
              -- x ∈ E, so x has a maximal cube
              obtain ⟨n₀, a₀, hx_mem, hsub, hmin⟩ := h_exists_min_scale x hx
              -- This cube is in Q_max
              have h_in_Qmax : (n₀, a₀) ∈ Q_max := by
                constructor
                · exact hsub
                · intro q hq hsub'
                  have : x ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hx_mem
                  exact hmin q.1 hq q.2 this
              exact Set.mem_biUnion h_in_Qmax hx_mem
            · intro hx
              simp only [Set.mem_iUnion] at hx
              obtain ⟨p, hp_mem, hx_in_p⟩ := hx
              exact hp_mem.1 hx_in_p
          -- Q_max is finite, so the union is finite
          rw [hE_union_Qmax]
          -- Finite union of closed sets is closed
          exact hfin.isClosed_biUnion h_cube_closed
        -- Step 2: E is clopen (closed and open)
        have hE_clopen : IsClopen E := ⟨hE_closed, hE⟩
        -- Step 3: Use preconnectedness
        -- EuclideanSpace d is preconnected for d > 0
        haveI : PreconnectedSpace (EuclideanSpace' d) := inferInstance
        -- Step 4: Clopen sets in preconnected space are either empty or univ
        rw [isClopen_iff] at hE_clopen
        cases hE_clopen with
        | inl h_empty =>
          -- E = ∅ contradicts E.Nonempty
          have : E.Nonempty := ⟨x₀, hx₀⟩
          rw [h_empty] at this
          exact Set.not_nonempty_empty this
        | inr h_univ =>
          -- E = univ contradicts hE_univ : E ≠ univ
          exact hE_univ h_univ
  -- Enumerate Q_max using the Denumerable structure (since Q_max is infinite and countable)
  obtain ⟨p₀, hp₀⟩ := hQ_max_nonempty
  -- For infinite countable sets, we can get an injective enumeration
  haveI : Infinite Q_max := Set.infinite_coe_iff.mpr hQ_max_infinite
  haveI : Countable Q_max := hQ_max_countable.to_subtype
  haveI : Denumerable Q_max := Denumerable.ofEncodableOfInfinite Q_max
  -- Use the denumerable equiv to get a bijection
  let B_enum : ℕ ≃ Q_max := (Denumerable.eqv Q_max).symm
  let B_idx : ℕ → ℕ × (Fin d → ℤ) := fun n => (B_enum n).val
  have hB_idx_inj : Function.Injective B_idx := by
    intro i j hij
    have : B_enum i = B_enum j := Subtype.ext hij
    exact (Equiv.injective B_enum) this
  let B : ℕ → Box d := fun n => DyadicCube ((B_idx n).1 : ℤ) (B_idx n).2
  use B
  constructor
  · -- E = ⋃ n, (B n).toSet
    ext x
    constructor
    · -- x ∈ E → x ∈ ⋃ n, (B n).toSet
      intro hx
      obtain ⟨n₀, a₀, hxa₀, hsub, hmin⟩ := h_exists_min_scale x hx
      -- (n₀, a₀) ∈ Q_max
      have h_in_Qmax : (⟨n₀, a₀⟩ : ℕ × (Fin d → ℤ)) ∈ Q_max := by
        simp only [Set.mem_setOf_eq, Q_max]
        constructor
        · exact hsub
        · intro q hq hsub'
          have hx_in_q : x ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hxa₀
          exact hmin q.1 hq q.2 hx_in_q
      -- B_enum is a bijection ℕ ≃ Q_max, so (n₀, a₀) ∈ Q_max has a preimage
      rw [Set.mem_iUnion]
      -- h_in_Qmax : (n₀, a₀) ∈ Q_max, and B_enum is surjective
      let elem : Q_max := ⟨(n₀, a₀), h_in_Qmax⟩
      have h_in_range : elem ∈ Set.range B_enum := by
        rw [Equiv.range_eq_univ]
        exact Set.mem_univ _
      obtain ⟨k, hk⟩ := h_in_range
      use k
      show x ∈ (DyadicCube ((B_idx k).1 : ℤ) (B_idx k).2).toSet
      have heq : B_idx k = (n₀, a₀) := by
        simp only [B_idx]
        exact congrArg Subtype.val hk
      rw [heq]
      exact hxa₀
    · -- x ∈ ⋃ n, (B n).toSet → x ∈ E
      intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      have h_Bn_mem : B_idx n ∈ Q_max := (B_enum n).property
      exact h_Bn_mem.1 hn
  constructor
  · -- ∀ n, (B n).IsDyadic
    intro n
    simp only [B, Box.IsDyadic]
    use (B_idx n).1, (B_idx n).2
  · -- Pairwise almost disjoint
    intro i j hij
    simp only [Function.onFun]
    have hi_mem : B_idx i ∈ Q_max := (B_enum i).property
    have hj_mem : B_idx j ∈ Q_max := (B_enum j).property
    -- Two distinct maximal cubes are almost disjoint
    -- By DyadicCube.nesting: either almost disjoint, or one ⊆ other
    rcases DyadicCube.nesting (n := (B_idx i).1) (m := (B_idx j).1)
        (a := (B_idx i).2) (b := (B_idx j).2) with h_ad | h_ij | h_ji
    · exact h_ad
    · -- B i ⊆ B j: analyze by scale comparison
      exfalso
      -- h_ij : (DyadicCube (B_idx i).1 (B_idx i).2).toSet ⊆ (DyadicCube (B_idx j).1 (B_idx j).2).toSet
      -- If B_i ⊆ B_j strictly, then (B_idx j).1 < (B_idx i).1 (j is coarser)
      -- By maximality of B_i, since B_i ⊆ B_j and j.1 < i.1, we have B_j ⊈ E
      -- But B_j ∈ Q_max implies B_j ⊆ E. Contradiction.
      rcases lt_trichotomy (B_idx j).1 (B_idx i).1 with hji_lt | hji_eq | hji_gt
      · -- (B_idx j).1 < (B_idx i).1: j is coarser scale
        -- B_i ⊆ B_j and j.1 < i.1 contradicts maximality of B_i
        exact hi_mem.2 (B_idx j) hji_lt h_ij hj_mem.1
      · -- Same scale: cubes are either equal or disjoint
        -- If B_i ⊆ B_j at same scale, they must be equal
        have h_ij' : (DyadicCube (↑(B_idx i).1) (B_idx i).2).toSet ⊆
            (DyadicCube (↑(B_idx i).1) (B_idx j).2).toSet := by
          convert h_ij using 3; simp only [Nat.cast_inj]; exact hji_eq.symm
        have heq : (B_idx i).2 = (B_idx j).2 := dyadicCubeNoProperContainmentSameScale h_ij'
        -- If scales and indices equal, B_i = B_j, so B_idx i = B_idx j
        have hidx_eq : B_idx i = B_idx j := Prod.ext hji_eq.symm (funext fun x => congrFun heq x)
        -- By injectivity of B_idx (from Denumerable enumeration), i = j
        exact hij (hB_idx_inj hidx_eq)
      · -- (B_idx i).1 < (B_idx j).1: i is coarser scale (larger cube), j is finer (smaller cube)
        -- h_ij says larger cube ⊆ smaller cube, geometrically impossible for d > 0
        have h_scale_lt : (↑(B_idx i).1 : ℤ) < ↑(B_idx j).1 := by exact_mod_cast hji_gt
        exact dyadicCubeLargerNotInSmaller hd h_scale_lt h_ij
    · -- B j ⊆ B i: symmetric case
      exfalso
      rcases lt_trichotomy (B_idx i).1 (B_idx j).1 with hij_lt | hij_eq | hij_gt
      · -- i coarser (larger), j finer (smaller), B_j ⊆ B_i is geometrically valid
        -- This contradicts maximality of B_j: B_j ⊆ B_i ⊆ E, and i is coarser
        exact hj_mem.2 (B_idx i) hij_lt h_ji hi_mem.1
      · -- Same scale: use injectivity as in the symmetric case above
        have h_ji' : (DyadicCube (↑(B_idx j).1) (B_idx j).2).toSet ⊆
            (DyadicCube (↑(B_idx j).1) (B_idx i).2).toSet := by
          convert h_ji using 3; simp only [Nat.cast_inj]; exact hij_eq.symm
        have heq : (B_idx j).2 = (B_idx i).2 := dyadicCubeNoProperContainmentSameScale h_ji'
        have hidx_eq : B_idx j = B_idx i := Prod.ext hij_eq.symm (funext fun x => congrFun heq x)
        exact hij (hB_idx_inj hidx_eq).symm
      · -- j coarser (larger), i finer (smaller), B_j ⊆ B_i means larger inside smaller
        -- Geometric impossibility for d > 0
        have h_scale_lt : (↑(B_idx j).1 : ℤ) < ↑(B_idx i).1 := by exact_mod_cast hij_gt
        exact dyadicCubeLargerNotInSmaller hd h_scale_lt h_ji

theorem Lebesgue_outer_measure.of_open {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsOpen E) : Lebesgue_outer_measure E = Jordan_inner_measure E := by
  by_cases hd : d = 0
  · -- Dimension 0: In dim 0, open sets are either ∅ or Set.univ
    subst hd
    rw [Lebesgue_outer_measure_of_dim_zero]
    by_cases hne : E.Nonempty
    · -- Case: E is nonempty → E = Set.univ in dimension 0
      simp only [hne, ↓reduceIte]
      -- Show Jordan_inner_measure E = 1
      -- E = Set.univ since EuclideanSpace' 0 is singleton and E is nonempty
      have hE_univ : E = Set.univ := by
        ext x
        constructor
        · intro _; exact Set.mem_univ x
        · intro _
          obtain ⟨y, hy⟩ := hne
          have : x = y := by ext i; exact i.elim0
          rw [this]; exact hy
      -- Set.univ is elementary with measure 1 in dimension 0
      let B : Box 0 := ⟨fun i => i.elim0⟩
      have hB_univ : B.toSet = Set.univ := by
        ext x; simp only [Box.toSet, Set.mem_univ, iff_true]; intro i; exact i.elim0
      have hB_vol : |B|ᵥ = 1 := by simp only [Box.volume, Finset.univ_eq_empty, Finset.prod_empty]
      -- Jordan_inner_measure E ≥ measure of B (since B ⊆ E = univ)
      have h_ge : (IsElementary.box B).measure ≤ Jordan_inner_measure E := by
        unfold Jordan_inner_measure
        apply le_csSup
        · use 1
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          -- Any elementary subset of Set.univ in dim 0 has measure ≤ 1
          by_cases hA_ne : A.Nonempty
          · have hA_univ : A = Set.univ := by
              ext x; constructor; intro _; exact Set.mem_univ x
              intro _; obtain ⟨y, hy⟩ := hA_ne; have : x = y := by ext i; exact i.elim0
              rw [this]; exact hy
            have : hA.measure = 1 := by
              have h_eq : hA.measure = (IsElementary.box B).measure := by
                apply IsElementary.measure_eq_of_set_eq; rw [hA_univ, hB_univ]
              rw [h_eq, IsElementary.measure_of_box, hB_vol]
            rw [this]
          · have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA_ne
            have : hA.measure = 0 := by
              have h_eq : hA.measure = (IsElementary.empty 0).measure :=
                IsElementary.measure_eq_of_set_eq hA (IsElementary.empty 0) hA_empty
              rw [h_eq, IsElementary.measure_of_empty]
            rw [this]; norm_num
        · use B.toSet, IsElementary.box B; simp [hE_univ, hB_univ]
      -- Jordan_inner_measure E ≤ 1 (since E ⊆ Set.univ and univ has outer measure 1)
      have h_le : Jordan_inner_measure E ≤ 1 := by
        unfold Jordan_inner_measure
        apply csSup_le
        · use 0, ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
        · intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          by_cases hA_ne : A.Nonempty
          · have hA_univ : A = Set.univ := by
              ext x; constructor; intro _; exact Set.mem_univ x
              intro _; obtain ⟨y, hy⟩ := hA_ne; have : x = y := by ext i; exact i.elim0
              rw [this]; exact hy
            have : hA.measure = 1 := by
              have h_eq : hA.measure = (IsElementary.box B).measure := by
                apply IsElementary.measure_eq_of_set_eq; rw [hA_univ, hB_univ]
              rw [h_eq, IsElementary.measure_of_box, hB_vol]
            rw [this]
          · have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA_ne
            have : hA.measure = 0 := by
              have h_eq : hA.measure = (IsElementary.empty 0).measure :=
                IsElementary.measure_eq_of_set_eq hA (IsElementary.empty 0) hA_empty
              rw [h_eq, IsElementary.measure_of_empty]
            rw [this]; norm_num
      -- Combine h_ge and h_le to get Jordan_inner_measure E = 1
      have h_jordan_eq_1 : Jordan_inner_measure E = 1 := by
        rw [IsElementary.measure_of_box, hB_vol] at h_ge
        exact (h_ge.antisymm h_le).symm
      rw [h_jordan_eq_1]
      norm_num
    · -- Case: E is empty
      have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [hne, if_false]
      subst hE_empty
      -- Show (0 : EReal) = ↑(Jordan_inner_measure ∅)
      -- First prove Jordan_inner_measure ∅ = 0
      have h_jordan_empty : Jordan_inner_measure (∅ : Set (EuclideanSpace' 0)) = 0 := by
        unfold Jordan_inner_measure
        apply le_antisymm
        · apply csSup_le
          · use 0, ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
          · intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty 0)
        · apply le_csSup
          · use 0; intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty 0)
          · use ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
      rw [h_jordan_empty]
      norm_num
  · push_neg at hd
    have hd' : 0 < d := Nat.pos_of_ne_zero hd
    by_cases hE_empty : E = ∅
    · -- Empty set case: use Lebesgue_outer_measure.of_empty and Jordan_inner_measure ∅ = 0
      subst hE_empty
      rw [Lebesgue_outer_measure.of_empty]
      -- Show (0 : EReal) = ↑(Jordan_inner_measure ∅)
      -- First prove Jordan_inner_measure ∅ = 0
      have h_jordan_empty : Jordan_inner_measure (∅ : Set (EuclideanSpace' d)) = 0 := by
        unfold Jordan_inner_measure
        apply le_antisymm
        · apply csSup_le
          · use 0, ∅, IsElementary.empty d; simp [IsElementary.measure_of_empty]
          · intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty d)
        · apply le_csSup
          · use 0; intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty d)
          · use ∅, IsElementary.empty d; simp [IsElementary.measure_of_empty]
      rw [h_jordan_empty]
      norm_num
    · -- Main case: E nonempty open set in dimension > 0
      have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
      -- Decompose E into almost-disjoint dyadic boxes
      obtain ⟨B, hE_eq, hB_dyadic, hB_disj⟩ := IsOpen.eq_union_boxes hd' E hE hE_nonempty
      -- Apply lemma eq_Jordan_inner_of_boxes (Exercise 1.2.5)
      exact Lebesgue_outer_measure.eq_Jordan_inner_of_boxes E B hE_eq hB_disj

/-- Lemma 1.2.12 (Outer regularity). m*(E) = inf{m*(U) : E ⊆ U, U open}. -/
theorem Lebesgue_outer_measure.eq {d:ℕ} (E: Set (EuclideanSpace' d)) : Lebesgue_outer_measure E = sInf { M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by
  let S := { M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U}
  apply le_antisymm
  · -- ≤ direction: m*(E) ≤ sInf S (by monotonicity, m*(E) is a lower bound)
    apply le_csInf
    · -- S is nonempty (Set.univ is open and contains E)
      exact ⟨Lebesgue_outer_measure Set.univ, Set.univ, Set.subset_univ E, isOpen_univ, rfl⟩
    · -- m*(E) is a lower bound for S
      intro M ⟨U, hE_sub_U, _hU_open, hM_eq⟩
      rw [hM_eq]
      exact Lebesgue_outer_measure.mono hE_sub_U
  · -- ≥ direction: sInf S ≤ m*(E) (main work)
    -- Handle dimension 0 separately
    by_cases hd : d = 0
    · -- d = 0: In dimension 0, EuclideanSpace' 0 is a singleton type
      subst hd
      have h_singleton : ∀ (y z : EuclideanSpace' 0), y = z := fun y z =>
        PiLp.ext fun i => Fin.elim0 i
      by_cases hE_empty : E = ∅
      · -- E = ∅: m*(∅) = 0, and sInf S ≥ 0 (all outer measures are ≥ 0)
        -- Actually we need sInf S ≤ m*(E) = 0
        -- Since ∅ is open and contains E = ∅, m*(∅) ∈ S
        rw [hE_empty]
        apply csInf_le_of_le
        · use 0
          intro M ⟨U, _, _, hM⟩
          rw [hM]
          exact Lebesgue_outer_measure.nonneg U
        · exact ⟨∅, Set.Subset.rfl, isOpen_empty, rfl⟩
        · exact le_refl _
      · -- E ≠ ∅: Then E = Set.univ (since every nonempty set in a singleton is univ)
        have hE_univ : E = Set.univ := by
          ext x; constructor
          · intro _; exact Set.mem_univ x
          · intro _
            have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
            obtain ⟨e, he⟩ := hE_nonempty
            rw [h_singleton x e]
            exact he
        rw [hE_univ]
        apply csInf_le_of_le
        · use 0
          intro M ⟨U, _, _, hM⟩
          rw [hM]
          exact Lebesgue_outer_measure.nonneg U
        · exact ⟨Set.univ, Set.subset_univ _, isOpen_univ, rfl⟩
        · exact le_refl _
    -- d > 0: main argument
    push_neg at hd
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    -- Case split on whether m*(E) = ⊤
    by_cases h_top : Lebesgue_outer_measure E = ⊤
    · -- m*(E) = ⊤: trivially sInf S ≤ ⊤
      rw [h_top]
      exact le_top
    -- m*(E) is finite: use ε-argument
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    -- Use ε/2 for the cover and ε/2 for the inflation to get total bound m*(E) + ε
    have hε2_pos : 0 < ε / 2 := by linarith
    -- Get cover close to m*(E): ∃ B₁, B₂,... with ∑|Bₙ| ≤ m*(E) + ε/2
    obtain ⟨B, hB_cover, hB_sum⟩ := exists_cover_close hd_pos E (ε/2) hε2_pos h_top
    -- Inflate each box Bₙ to open box B'ₙ with |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}
    have h_inflate : ∀ n, ∃ B'n : Box d, (B n).toSet ⊆ interior B'n.toSet ∧
        IsOpen (interior B'n.toSet) ∧ |B'n|ᵥ ≤ |(B n)|ᵥ + (ε/2) / 2^(n+1) := by
      intro n
      have h_eps_pos : 0 < (ε/2) / 2^(n+1) := by positivity
      exact Box.inflate (B n) ((ε/2) / 2^(n+1)) h_eps_pos
    choose B' hB'_subset hB'_open hB'_vol using h_inflate
    -- Define the open set U = ⋃ₙ interior B'ₙ
    let U := ⋃ n, interior (B' n).toSet
    -- U is open (union of open sets)
    have hU_open : IsOpen U := isOpen_iUnion (fun n => hB'_open n)
    -- E ⊆ U (since E ⊆ ⋃ₙ Bₙ.toSet ⊆ ⋃ₙ interior B'ₙ.toSet = U)
    have hE_sub_U : E ⊆ U := fun x hx => by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hB_cover hx)
      exact Set.mem_iUnion.mpr ⟨n, hB'_subset n hn⟩
    -- m*(U) ≤ ∑ₙ m*(interior B'ₙ.toSet) ≤ ∑ₙ |B'ₙ|ᵥ (by subadditivity + elementary measure)
    have hU_measure : Lebesgue_outer_measure U ≤ ∑' n, (B' n).volume.toEReal := by
      -- First: m*(U) ≤ ∑' m*(interior B'ₙ) by countable subadditivity
      have h_subadditive := Lebesgue_outer_measure.union_le (fun n => interior (B' n).toSet)
      -- Second: ∀n, m*(interior B'ₙ) ≤ |B'ₙ|ᵥ
      have h_pointwise : ∀ n, Lebesgue_outer_measure (interior (B' n).toSet) ≤ (B' n).volume.toEReal := by
        intro n
        calc Lebesgue_outer_measure (interior (B' n).toSet)
            ≤ Lebesgue_outer_measure (B' n).toSet := Lebesgue_outer_measure.mono interior_subset
          _ = (B' n).volume.toEReal := by
              have h_elem : IsElementary (B' n).toSet := IsElementary.box (B' n)
              rw [Lebesgue_outer_measure.elementary (B' n).toSet h_elem, IsElementary.measure_of_box]
      -- Third: use EReal tsum comparison
      have h_nonneg_f : ∀ n, 0 ≤ Lebesgue_outer_measure (interior (B' n).toSet) :=
        fun n => Lebesgue_outer_measure.nonneg _
      have h_nonneg_g : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
      have h_summable_g : Summable (fun n => (B' n).volume) := by
        -- |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}. Summable because:
        -- 1. Geometric series ∑(ε/2)/2^{n+1} is summable
        -- 2. B-volumes sum to ≤ m*(E) + ε/2 < ⊤, so they are summable in ℝ
        -- 3. By comparison test, B'-volumes are summable
        -- Technical details deferred to summability lemmas
        have h_geom_summable : Summable (fun n : ℕ => ε / 2 / 2 ^ (n + 1)) := by
          -- Use tsum_geometric_eps pattern: ∑ ε/2^{n+1} = ε
          -- So ∑ (ε/2)/2^{n+1} = ε/2, which converges
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => ε / 2 / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_pos : (0 : ℝ) < 2^(n+1) := by positivity
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := h_two_pow_pos.ne'
            field_simp [h_two_pow_ne]
            ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_B_nonneg : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
        have h_B_summable : Summable (fun n => (B n).volume) := by
          -- From hB_sum: ∑' (B n).volume.toEReal ≤ m*(E) + ε/2 < ⊤
          -- Extract a real upper bound from hB_sum
          have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
            EReal.add_ne_top h_top (EReal.coe_ne_top _)
          -- Get a real bound M such that the tsum ≤ M
          have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
            cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
            | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
            | coe r => exact ⟨r, le_refl _⟩
            | top => exact (h_rhs_ne_top h_rhs).elim
          obtain ⟨M, hM_ge⟩ := h_exists_M
          have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
          -- Use summable_of_sum_range_le: need ∀ n, ∑_{i<n} f i ≤ M
          apply summable_of_sum_range_le h_B_nonneg
          intro n
          have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
          have h_chain := le_trans h_partial h_tsum_le_M
          rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
          exact EReal.coe_le_coe_iff.mp h_chain
        exact Summable.of_nonneg_of_le (fun n => Box.volume_nonneg _)
          (fun n => hB'_vol n) (h_B_summable.add h_geom_summable)
      calc Lebesgue_outer_measure U
          ≤ ∑' n, Lebesgue_outer_measure (interior (B' n).toSet) := h_subadditive
        _ ≤ ∑' n, (B' n).volume.toEReal :=
            EReal.tsum_le_coe_tsum_of_forall_le h_nonneg_f h_nonneg_g h_summable_g h_pointwise
    -- ∑ₙ |B'ₙ|ᵥ ≤ ∑ₙ (|Bₙ|ᵥ + (ε/2)/2^{n+1}) = ∑ₙ |Bₙ|ᵥ + ε/2 (since ∑(ε/2)/2^{n+1} = ε/2)
    have hB'_vol_sum : (∑' n, (B' n).volume.toEReal) ≤ (∑' n, (B n).volume.toEReal) + (ε/2 : ℝ) := by
      -- Pointwise: |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}
      -- So ∑|B'ₙ| ≤ ∑|Bₙ| + ∑(ε/2)/2^{n+1} = ∑|Bₙ| + ε/2
      have h_B_nonneg : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
      have h_geom_nonneg : ∀ n, 0 ≤ (ε/2) / 2^(n+1) := fun n => by positivity
      have h_pw : ∀ n, (B n).volume + (ε/2) / 2^(n+1) ≤ (B n).volume + (ε/2) / 2^(n+1) := fun n => le_refl _
      -- Use helper: ∑|B'ₙ| ≤ ∑(|Bₙ| + δₙ) since |B'ₙ| ≤ |Bₙ| + δₙ
      have h_B'_le_sum : ∀ n, (B' n).volume ≤ (B n).volume + (ε/2) / 2^(n+1) := hB'_vol
      have h_B'_nonneg : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
      have h_B'_nonneg_EReal : ∀ n, (0 : EReal) ≤ (B' n).volume.toEReal :=
        fun n => EReal.coe_nonneg.mpr (h_B'_nonneg n)
      -- ∑|B'ₙ| ≤ ∑(|Bₙ| + δₙ) by pointwise bound
      have h_step1 : (∑' n, (B' n).volume.toEReal) ≤ ∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal := by
        apply EReal.tsum_le_coe_tsum_of_forall_le h_B'_nonneg_EReal
          (fun n => add_nonneg (h_B_nonneg n) (h_geom_nonneg n))
        · -- Summability of |Bₙ| + δₙ
          have h_geom_summable : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
            have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
              ext n
              have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
              field_simp [h_two_pow_ne]; ring_nf; simp
            rw [h_eq]
            exact h_summable_base.mul_left (ε / 4)
          have h_B_summable : Summable (fun n => (B n).volume) := by
            have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
              EReal.add_ne_top h_top (EReal.coe_ne_top _)
            have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
              cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
              | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
              | coe r => exact ⟨r, le_refl _⟩
              | top => exact (h_rhs_ne_top h_rhs).elim
            obtain ⟨M, hM_ge⟩ := h_exists_M
            have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
            apply summable_of_sum_range_le h_B_nonneg
            intro n
            have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
            have h_chain := le_trans h_partial h_tsum_le_M
            rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
            exact EReal.coe_le_coe_iff.mp h_chain
          exact h_B_summable.add h_geom_summable
        · exact fun n => EReal.coe_le_coe_iff.mpr (h_B'_le_sum n)
      -- Now split ∑(|Bₙ| + δₙ) = ∑|Bₙ| + ∑δₙ
      have h_step2 : (∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal) =
          (∑' n, (B n).volume.toEReal) + (∑' n, ((ε/2) / 2^(n+1)).toEReal) := by
        -- For Real, we have ∑(f + g) = ∑f + ∑g when summable
        have h_geom_summable : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
            field_simp [h_two_pow_ne]; ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_B_summable : Summable (fun n => (B n).volume) := by
          have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
            EReal.add_ne_top h_top (EReal.coe_ne_top _)
          have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
            cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
            | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
            | coe r => exact ⟨r, le_refl _⟩
            | top => exact (h_rhs_ne_top h_rhs).elim
          obtain ⟨M, hM_ge⟩ := h_exists_M
          have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
          apply summable_of_sum_range_le h_B_nonneg
          intro n
          have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
          have h_chain := le_trans h_partial h_tsum_le_M
          rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
          exact EReal.coe_le_coe_iff.mp h_chain
        -- Use tsum_add for Real
        have h_real_tsum : ∑' n, ((B n).volume + (ε/2) / 2^(n+1)) =
            (∑' n, (B n).volume) + (∑' n, (ε/2) / 2^(n+1)) :=
          h_B_summable.tsum_add h_geom_summable
        -- Convert to EReal
        have h_sum_nonneg : ∀ n, 0 ≤ (B n).volume + (ε/2) / 2^(n+1) :=
          fun n => add_nonneg (h_B_nonneg n) (h_geom_nonneg n)
        -- Use symm to get: ∑' ↑(...) = ↑(∑' ...)
        rw [← EReal.coe_tsum_of_nonneg h_sum_nonneg (h_B_summable.add h_geom_summable)]
        rw [← EReal.coe_tsum_of_nonneg h_B_nonneg h_B_summable]
        rw [← EReal.coe_tsum_of_nonneg h_geom_nonneg h_geom_summable]
        rw [h_real_tsum]
        simp only [EReal.coe_add]
      -- ∑δₙ = ε/2
      have h_geom_sum : (∑' n, ((ε/2) / 2^(n+1)).toEReal) = (ε/2 : EReal) := by
        -- ∑ (ε/2)/2^{n+1} = (ε/2) * ∑ 1/2^{n+1} = (ε/2) * 1 = ε/2
        have h_geom_summable' : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
            field_simp [h_two_pow_ne]; ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_real_sum : ∑' n : ℕ, (ε/2) / 2^(n+1) = ε/2 := by
          have h_eq : (fun n : ℕ => (ε/2) / 2^(n+1)) = (fun n : ℕ => (ε/2) * (1/2)^(n+1)) := by
            ext n; field_simp; simp
          rw [h_eq, tsum_mul_left]
          have h_geom_sum_one : ∑' n : ℕ, (1/2 : ℝ)^(n+1) = 1 := by
            have h_summable : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            have h_formula := h_summable.sum_add_tsum_nat_add 1
            simp only [Finset.range_one, Finset.sum_singleton, pow_zero] at h_formula
            rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)] at h_formula
            linarith
          rw [h_geom_sum_one]; ring
        -- Convert EReal tsum: ∑' n, (ε/2 / 2^(n+1)).toEReal = (ε/2 : EReal)
        rw [← EReal.coe_tsum_of_nonneg h_geom_nonneg h_geom_summable', h_real_sum, EReal.coe_div]
        norm_cast
      calc ∑' n, (B' n).volume.toEReal
          ≤ ∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal := h_step1
        _ = (∑' n, (B n).volume.toEReal) + (∑' n, ((ε/2) / 2^(n+1)).toEReal) := h_step2
        _ = (∑' n, (B n).volume.toEReal) + (ε/2 : EReal) := by rw [h_geom_sum]
    -- Combine: m*(U) ≤ m*(E) + ε
    have hU_bound : Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + ε := by
      calc Lebesgue_outer_measure U
          ≤ ∑' n, (B' n).volume.toEReal := hU_measure
        _ ≤ (∑' n, (B n).volume.toEReal) + (ε/2 : ℝ) := hB'_vol_sum
        _ ≤ (Lebesgue_outer_measure E + (ε/2 : ℝ)) + (ε/2 : ℝ) := by
            apply add_le_add_left hB_sum
        _ = Lebesgue_outer_measure E + ε := by
            rw [add_assoc]
            congr 1
            norm_cast
            ring
    -- sInf S ≤ m*(U) since U ∈ S
    have h_U_in_S : Lebesgue_outer_measure U ∈ S :=
      ⟨U, hE_sub_U, hU_open, rfl⟩
    calc sInf S
        ≤ Lebesgue_outer_measure U := csInf_le ⟨0, fun M ⟨V, _, _, hM⟩ => hM ▸ Lebesgue_outer_measure.nonneg V⟩ h_U_in_S
      _ ≤ Lebesgue_outer_measure E + ε := hU_bound

/-- For any set E and ε > 0, there exists an open U ⊇ E with m*(U) ≤ m*(E) + ε.
    This follows from outer regularity (Lemma 1.2.12). -/
lemma Lebesgue_outer_measure.exists_open_superset_measure_le {d:ℕ} (E: Set (EuclideanSpace' d)) (ε : EReal) (hε : 0 < ε) :
    ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + ε := by
  -- By outer regularity (Lebesgue_outer_measure.eq):
  -- m*(E) = sInf { m*(U) | E ⊆ U ∧ IsOpen U }
  have h_outer_reg := Lebesgue_outer_measure.eq (d := d) E
  let S := {M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U}
  have h_set_nonempty : S.Nonempty := by
    use Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d))
    exact ⟨Set.univ, Set.subset_univ E, isOpen_univ, rfl⟩
  have h_inf : IsGLB S (sInf S) := isGLB_sInf S
  have h_ne_bot : sInf S ≠ ⊥ := by
    intro h_eq
    rw [h_eq] at h_inf
    have h_zero_lb : (0 : EReal) ∈ lowerBounds S := by
      intro v hv
      obtain ⟨U, _, _, rfl⟩ := hv
      exact Lebesgue_outer_measure.nonneg U
    have h_le : (0 : EReal) ≤ ⊥ := h_inf.2 h_zero_lb
    exact not_le.mpr EReal.bot_lt_zero h_le
  by_cases h_top : sInf S = ⊤
  · use Set.univ
    refine ⟨isOpen_univ, Set.subset_univ E, ?_⟩
    rw [h_outer_reg, h_top]
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact le_top
    | coe r => exact le_top
  · have h_lt : sInf S < sInf S + ε := by
      cases ε with
      | bot => exact absurd hε (not_lt.mpr bot_le)
      | top =>
        have h_sum_top : sInf S + ⊤ = ⊤ := by
          cases h : sInf S with
          | bot => exact absurd h h_ne_bot
          | top => exact absurd h h_top
          | coe r => rfl
        rw [h_sum_top]
        exact lt_top_iff_ne_top.mpr h_top
      | coe r =>
        have hr_pos : 0 < r := EReal.coe_pos.mp hε
        exact EReal.lt_add_of_pos_coe hr_pos h_ne_bot h_top
    have h_not_lb : sInf S + ε ∉ lowerBounds S := by
      intro h_is_lb
      have h_le : sInf S + ε ≤ sInf S := h_inf.2 h_is_lb
      exact not_lt.mpr h_le h_lt
    unfold lowerBounds at h_not_lb
    simp only [Set.mem_setOf_eq] at h_not_lb
    push_neg at h_not_lb
    obtain ⟨v, hv_in_S, hv_lt⟩ := h_not_lb
    obtain ⟨U, hE_sub_U, hU_open, hv_eq⟩ := hv_in_S
    use U
    refine ⟨hU_open, hE_sub_U, ?_⟩
    rw [h_outer_reg, ← hv_eq]
    exact le_of_lt hv_lt

/-- Compact sets in Euclidean space have finite Lebesgue outer measure. -/
lemma Lebesgue_outer_measure.finite_of_compact {d : ℕ} {E : Set (EuclideanSpace' d)}
    (hE : IsCompact E) : Lebesgue_outer_measure E ≠ ⊤ := by
  -- Empty case is trivial
  by_cases hE_empty : E = ∅
  · rw [hE_empty, Lebesgue_outer_measure.of_empty]; exact EReal.zero_ne_top
  -- For nonempty E: E compact → E bounded → E ⊆ closedBall x R → E ⊆ box [-M,M]^d
  have ⟨x, hx⟩ : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  have h_bounded : Bornology.IsBounded E := IsCompact.isBounded hE
  have ⟨r, h_sub_ball⟩ : ∃ (r : ℝ), E ⊆ Metric.closedBall x r := by
    rwa [← Metric.isBounded_iff_subset_closedBall x]
  -- Create a large box B that contains the closed ball
  let M := ‖x‖ + |r| + 2
  let B : Box d := { side := fun _ => BoundedInterval.Icc (-M) M }
  have h_E_sub_B : E ⊆ B.toSet := by
    intro y hy
    have h_in_ball : y ∈ Metric.closedBall x r := h_sub_ball hy
    simp only [Box.mem_toSet]
    intro i
    rw [Metric.mem_closedBall] at h_in_ball
    have h_dist : ‖y - x‖ ≤ r := h_in_ball
    have h_coord_diff : |(y - x) i| ≤ ‖y - x‖ := EuclideanSpace'.coord_le_norm (y - x) i
    have h_abs : |y i - x i| ≤ r := le_trans h_coord_diff h_dist
    have h_xi : |x i| ≤ ‖x‖ := EuclideanSpace'.coord_le_norm x i
    show y i ∈ (BoundedInterval.Icc (-M) M : Set ℝ)
    rw [BoundedInterval.set_Icc, Set.mem_Icc]
    rw [abs_le] at h_abs h_xi
    have h_r_bound : r ≤ |r| := le_abs_self r
    constructor <;> linarith
  have : IsElementary B.toSet := IsElementary.box B
  have h_B_finite : Lebesgue_outer_measure B.toSet ≠ ⊤ := by
    rw [Lebesgue_outer_measure.elementary B.toSet this]
    exact EReal.coe_ne_top _
  exact ne_top_of_le_ne_top h_B_finite (Lebesgue_outer_measure.mono h_E_sub_B)

/-- Exercise 1.2.6 -/
example : ∃ (d:ℕ) (E: Set (EuclideanSpace' d)), Lebesgue_outer_measure E ≠ sSup { M | ∃ U, U ⊆ E ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by sorry
