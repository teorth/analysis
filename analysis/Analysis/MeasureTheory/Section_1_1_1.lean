import Analysis.MeasureTheory.Notation
import Analysis.Section_9_1

/-!
# Introduction to Measure Theory, Section 1.1.1: Elementary measure

A companion to Section 1.1.1 of the book "An introduction to Measure Theory".

-/

/- Definition 1.1.1.  (Intervals) We use the same formalization of intervals used in
Chapter 11 of "Analysis I".  Following the usual Lean preference to admit `junk` values,
we allow for the possibility that `b < a`. -/
inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make Finsets of BoundedIntervals work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

/-- Some helpful general lemmas about BoundedInterval -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  cases I with
  | Ioo a b =>
    simp [set_Ioo]
    exact Metric.isBounded_Ioo a b
  | Icc a b =>
    simp [set_Icc]
    exact Metric.isBounded_Icc a b
  | Ioc a b =>
    simp [set_Ioc]
    exact Metric.isBounded_Ioc a b
  | Ico a b =>
    simp [set_Ico]
    exact Metric.isBounded_Ico a b

/-- A witness for lowerBound of upperBounds -/
def witness_lowerBound_upperBounds {X : Set ℝ} (y : ℝ) (hy : y ∈ X)
    : y ∈ lowerBounds (upperBounds X) := by
  intro u hu; simp [upperBounds] at hu; exact hu hy

/-- A witness for upperBound of lowerBounds -/
def witness_upperBound_lowerBounds {X : Set ℝ} (y : ℝ) (hy : y ∈ X)
    : y ∈ upperBounds (lowerBounds X) := by
  intro u hu; simp [lowerBounds] at hu; exact hu hy

/-- If x < sSup X, then there exists z ∈ X with x < z -/
theorem exists_gt_of_lt_csSup {X : Set ℝ} (hBddAbove : BddAbove X) (hNonempty : X.Nonempty)
    (hLowerBound : ∃ y ∈ X, y ∈ lowerBounds (upperBounds X)) (x : ℝ) (hx : x < sSup X) :
    ∃ z ∈ X, x < z := by
  by_contra! h
  have : sSup X ≤ x := by
    rw [← csInf_upperBounds_eq_csSup hBddAbove hNonempty]
    exact csInf_le
      (by obtain ⟨y, hy, _⟩ := hLowerBound; exact ⟨y, witness_lowerBound_upperBounds y hy⟩)
      (fun z hz => h z hz)
  linarith

/-- If sInf X < x, then there exists w ∈ X with w ≤ x -/
theorem exists_le_of_lt_csInf {X : Set ℝ} (hBddBelow : BddBelow X) (hNonempty : X.Nonempty)
    (hUpperBound : ∃ y ∈ X, y ∈ upperBounds (lowerBounds X)) (x : ℝ) (hx : sInf X < x) :
    ∃ w ∈ X, w ≤ x := by
  by_contra! h
  have : x ≤ sInf X := by
    rw [← csSup_lowerBounds_eq_csInf hBddBelow hNonempty]
    exact le_csSup
      (by obtain ⟨y, hy, _⟩ := hUpperBound; exact ⟨y, witness_upperBound_lowerBounds y hy⟩)
      (fun u hu => le_of_lt (h u hu))
  linarith

/-- Show x < b when b = sSup X and b ∉ X -/
theorem lt_sSup_of_ne_sSup {X : Set ℝ} {x b : ℝ} (_hBddAbove : BddAbove X) (_hb : b = sSup X)
    (hb_notin : b ∉ X) (hx : x ∈ X) (hx_le_b : x ≤ b) : x < b := by
  by_contra! h; exact hb_notin (hx_le_b.antisymm h ▸ hx)

/-- Show a < x when a = sInf X and a ∉ X -/
theorem sInf_lt_of_ne_sInf {X : Set ℝ} {a x : ℝ} (_hBddBelow : BddBelow X) (_ha : a = sInf X)
    (ha_notin : a ∉ X) (hx : x ∈ X) (ha_le_x : a ≤ x) : a < x := by
  by_contra! h; exact ha_notin (h.antisymm ha_le_x ▸ hx)

/-- Use order-connectedness to show x ∈ X when x ∈ [w, z] and w, z ∈ X -/
theorem mem_of_mem_Icc_ordConnected {X : Set ℝ}
    (hOrdConn : ∀ ⦃x : ℝ⦄, x ∈ X → ∀ ⦃y : ℝ⦄, y ∈ X → Set.Icc x y ⊆ X)
    {x w z : ℝ} (hw : w ∈ X) (hz : z ∈ X) (hx : x ∈ Set.Icc w z) : x ∈ X :=
  hOrdConn hw hz hx


theorem BoundedInterval.ordConnected_iff (X:Set ℝ) :
    Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  constructor
  · -- Non-trivial direction: if X is bounded and order-connected,
    -- then X = I for some BoundedInterval I
    -- Strategy:
    -- 1. Handle the empty case: If X = ∅, use Ioo 0 0 (the empty interval representation)
    -- 2. For non-empty X:
    --    a. Use boundedness to show X has infimum and supremum (bounded sets in ℝ are bounded above and below)
    --    b. Extract endpoints: a = sInf X, b = sSup X
    --    c. Determine interval type based on endpoint membership:
    --       - If a ∈ X ∧ b ∈ X → use Icc a b
    --       - If a ∈ X ∧ b ∉ X → use Ico a b
    --       - If a ∉ X ∧ b ∈ X → use Ioc a b
    --       - If a ∉ X ∧ b ∉ X → use Ioo a b
    --    d. Show X equals the constructed interval:
    --       - X ⊆ interval: Use that a = sInf X and b = sSup X
    --       - interval ⊆ X: Use order-connectedness (if x, y ∈ X, then [x, y] ⊆ X)
    intro ⟨hBounded, hOrdConn⟩
    by_cases hEmpty : X = ∅
    · -- Step 1: Empty case
      use Ioo 0 0
      simp [set_Ioo]
      exact hEmpty
    · -- Step 2: Non-empty case
      have hNonempty : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      rw [Set.ordConnected_def] at hOrdConn
      -- Step 2a: Get boundedness above and below
      -- Use that bounded sets in ℝ are contained in some Icc, which gives bounds directly
      rw [Chapter9.isBounded_def] at hBounded
      obtain ⟨M, hM_pos, hX_subset⟩ := hBounded
      have hBddBelow : BddBelow X := ⟨-M, fun x hx => (hX_subset hx).1⟩
      have hBddAbove : BddAbove X := ⟨M, fun x hx => (hX_subset hx).2⟩
      -- Step 2b: Extract endpoints
      set a := sInf X
      set b := sSup X
      -- Step 2c: Determine interval type based on endpoint membership
      by_cases ha : a ∈ X
      · by_cases hb : b ∈ X
        · -- Case: a ∈ X ∧ b ∈ X → use Icc a b
          use Icc a b; simp [set_Icc]; ext x; constructor
          · intro hx; simp [Set.mem_Icc]
            exact ⟨csInf_le hBddBelow hx, le_csSup hBddAbove hx⟩
          · intro hx; simp [Set.mem_Icc] at hx; exact (hOrdConn ha hb) hx
        · -- Case: a ∈ X ∧ b ∉ X → use Ico a b
          use Ico a b; simp [set_Ico]; ext x; constructor
          · intro hx; simp [Set.mem_Ico]
            exact ⟨csInf_le hBddBelow hx, lt_sSup_of_ne_sSup hBddAbove rfl hb hx (le_csSup hBddAbove hx)⟩
          · intro hx; simp [Set.mem_Ico] at hx
            have hb_eq : b = sSup X := rfl
            obtain ⟨z, hz, hxz⟩ := exists_gt_of_lt_csSup hBddAbove hNonempty
              ⟨a, ha, witness_lowerBound_upperBounds a ha⟩ x (by rw [←hb_eq]; exact hx.2)
            exact mem_of_mem_Icc_ordConnected hOrdConn ha hz ⟨hx.1, le_of_lt hxz⟩
      · by_cases hb : b ∈ X
        · -- Case: a ∉ X ∧ b ∈ X → use Ioc a b
          use Ioc a b; simp [set_Ioc]; ext x; constructor
          · intro hx; simp [Set.mem_Ioc]
            exact ⟨sInf_lt_of_ne_sInf hBddBelow rfl ha hx (csInf_le hBddBelow hx), le_csSup hBddAbove hx⟩
          · intro hx; simp [Set.mem_Ioc] at hx
            by_cases hx_eq_b : x = b
            · rw [hx_eq_b]; exact hb
            · have ha_eq : a = sInf X := rfl
              obtain ⟨w, hw, hwx⟩ := exists_le_of_lt_csInf hBddBelow hNonempty
                ⟨b, hb, witness_upperBound_lowerBounds b hb⟩ x (by rw [←ha_eq]; exact hx.1)
              exact mem_of_mem_Icc_ordConnected hOrdConn hw hb ⟨hwx, hx.2⟩
        · -- Case: a ∉ X ∧ b ∉ X → use Ioo a b
          use Ioo a b; simp [set_Ioo]; ext x; constructor
          · intro hx; simp [Set.mem_Ioo]
            exact ⟨sInf_lt_of_ne_sInf hBddBelow rfl ha hx (csInf_le hBddBelow hx),
              lt_sSup_of_ne_sSup hBddAbove rfl hb hx (le_csSup hBddAbove hx)⟩
          · intro hx; simp [Set.mem_Ioo] at hx
            have ha_eq : a = sInf X := rfl; have hb_eq : b = sSup X := rfl
            have h_lower : ∃ y ∈ X, y ∈ lowerBounds (upperBounds X) := by
              obtain ⟨y, hy⟩ := hNonempty; exact ⟨y, hy, witness_lowerBound_upperBounds y hy⟩
            have h_upper : ∃ y ∈ X, y ∈ upperBounds (lowerBounds X) := by
              obtain ⟨y, hy⟩ := hNonempty; exact ⟨y, hy, witness_upperBound_lowerBounds y hy⟩
            obtain ⟨z, hz, hxz⟩ := exists_gt_of_lt_csSup hBddAbove hNonempty h_lower x
              (by rw [←hb_eq]; exact hx.2)
            obtain ⟨w, hw, hwx⟩ := exists_le_of_lt_csInf hBddBelow hNonempty h_upper x
              (by rw [←ha_eq]; exact hx.1)
            exact mem_of_mem_Icc_ordConnected hOrdConn hw hz ⟨hwx, le_of_lt hxz⟩
  · -- Trivial direction: if X = I for some BoundedInterval I, then X is bounded and order-connected
    intro ⟨I, hX⟩
    have hX' : X = (I : Set ℝ) := hX
    constructor
    · -- Show X is bounded
      rw [hX']
      exact Bornology.IsBounded.of_boundedInterval I
    · -- Show X is order-connected: by case analysis on the four interval types,
      -- using `Set.ordConnected_def` and proving that for any `x, y` in the interval
      -- and `z` in `[x, y]`, we have `z` in the interval
      rw [hX']
      rw [Set.ordConnected_def]
      intro x hx y hy z hz
      cases I with
      | Ioo a b =>
        simp [set_Ioo, Set.mem_Ioo] at hx hy hz; simp [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
      | Icc a b =>
        simp [set_Icc, Set.mem_Icc] at hx hy hz; simp [Set.mem_Icc]
        exact ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
      | Ioc a b =>
        simp [set_Ioc, Set.mem_Ioc] at hx hy hz; simp [Set.mem_Ioc]
        exact ⟨lt_of_lt_of_le hx.1 hz.1, le_trans hz.2 hy.2⟩
      | Ico a b =>
        simp [set_Ico, Set.mem_Ico] at hx hy hz; simp [Set.mem_Ico]
        exact ⟨le_trans hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩

theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  -- Strategy: Use the characterization theorem `BoundedInterval.ordConnected_iff`
  -- Step 1: Show that (I:Set ℝ) ∩ (J:Set ℝ) is bounded
  -- Step 2: Show that (I:Set ℝ) ∩ (J:Set ℝ) is order-connected
  -- Step 3: Apply the characterization theorem
  have hBounded : Bornology.IsBounded ((I:Set ℝ) ∩ (J:Set ℝ)) := by
    -- The intersection is a subset of I, which is bounded
    exact (Bornology.IsBounded.of_boundedInterval I).subset Set.inter_subset_left
  have hOrdConn : ((I:Set ℝ) ∩ (J:Set ℝ)).OrdConnected := by
    -- Both I and J are order-connected (from ordConnected_iff)
    have hI_ordConn : (I:Set ℝ).OrdConnected := by
      exact (BoundedInterval.ordConnected_iff (I:Set ℝ)).mpr ⟨I, rfl⟩ |>.2
    have hJ_ordConn : (J:Set ℝ).OrdConnected := by
      exact (BoundedInterval.ordConnected_iff (J:Set ℝ)).mpr ⟨J, rfl⟩ |>.2
    -- Intersection of order-connected sets is order-connected
    exact Set.OrdConnected.inter hI_ordConn hJ_ordConn
  exact (BoundedInterval.ordConnected_iff ((I:Set ℝ) ∩ (J:Set ℝ))).mp ⟨hBounded, hOrdConn⟩

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (inter I J).choose_spec.symm

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

@[simp]
theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

@[simp]
theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

/-- Definition 1.1.1 (boxes) -/
abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

@[ext]
structure Box (d:ℕ) where
  side : Fin d → BoundedInterval

@[coe]
abbrev Box.toSet {d:ℕ} (B: Box d) : Set (EuclideanSpace' d) :=
  Set.univ.pi (fun i ↦ ↑(B.side i))

instance Box.inst_coeSet {d:ℕ} : Coe (Box d) (Set (EuclideanSpace' d)) where
  coe := toSet

@[coe]
abbrev BoundedInterval.toBox (I: BoundedInterval) : Box 1 where
  side := fun _ ↦ I

instance BoundedInterval.inst_coeBox : Coe (BoundedInterval) (Box 1) where
  coe := toBox

@[simp]
theorem BoundedInterval.toBox_inj {I J: BoundedInterval} : (I:Box 1) = (J:Box 1) ↔ I = J := by
  refine' ⟨fun h => _, fun h => h ▸ rfl⟩
  have : (I:Box 1).side 0 = (J:Box 1).side 0 := by rw [h]
  exact this

@[simp]
theorem BoundedInterval.coe_of_box (I:BoundedInterval) : (I:Box 1).toSet = Real.equiv_EuclideanSpace' '' I.toSet := by
  ext x
  simp [Box.toSet]; rw [Set.mem_pi]; constructor
  . intro h; use x 0; simp [h 0]
    ext ⟨ i, hi ⟩; have : i=0 := by omega
    subst this; simp
  rintro ⟨ y, hy, rfl ⟩ ⟨ i, hi ⟩ _
  have : i=0 := by omega
  grind

/-- Definition 1.1.1 (boxes)-/
abbrev Box.volume {d:ℕ} (B: Box d) : ℝ := ∏ i, |B.side i|ₗ

/-- Using ||ᵥ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ᵥ" : term => `(Box.volume $a)

/-- Helper lemma: If a box is empty, its volume is zero -/
lemma Box.volume_eq_zero_of_empty {d:ℕ} (B: Box d) (h: B.toSet = ∅) : |B|ᵥ = 0 := by
  -- If B.toSet = ∅, then the box has at least one empty side interval
  have : ∃ i, (B.side i).toSet = ∅ := by
    by_contra! h_all_nonempty
    have h_all_nonempty : ∀ i, (B.side i).toSet.Nonempty := h_all_nonempty
    choose x hx using h_all_nonempty
    have h_nonempty : B.toSet.Nonempty := ⟨fun i ↦ x i, fun i _ ↦ hx i⟩
    rw [h] at h_nonempty
    exact Set.not_nonempty_empty h_nonempty
  obtain ⟨i, hi⟩ := this
  -- Show |B.side i|ₗ = 0, which implies |B|ᵥ = 0
  rw [Box.volume]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  -- If (B.side i).toSet = ∅, then the interval is degenerate (b ≤ a), so length = 0
  have h_le : (B.side i).b ≤ (B.side i).a := by
    match B.side i, hi with
    | Ioo a b, hi => simp [BoundedInterval.set_Ioo] at hi; simp; exact le_of_not_gt (Set.Ioo_eq_empty_iff.1 hi)
    | Icc a b, hi => simp [BoundedInterval.set_Icc] at hi; simp; exact le_of_not_ge (Set.Icc_eq_empty_iff.1 hi)
    | Ioc a b, hi => simp [BoundedInterval.set_Ioc] at hi; simp; exact le_of_not_gt (Set.Ioc_eq_empty_iff.1 hi)
    | Ico a b, hi => simp [BoundedInterval.set_Ico] at hi; simp; exact le_of_not_gt (Set.Ico_eq_empty_iff.1 hi)
  simp [BoundedInterval.length, max_eq_right (sub_nonpos.2 h_le)]

@[simp]
theorem Box.volume_of_interval (I:BoundedInterval) : |(I:Box 1)|ᵥ = |I|ₗ := by
  simp [Box.volume]

abbrev IsElementary {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ S : Finset (Box d), E = ⋃ B ∈ S, ↑B

theorem IsElementary.box {d:ℕ} (B: Box d) : IsElementary B.toSet := by
  use {B}
  simp

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.union {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∪ F) := by
  sorry

lemma IsElementary.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) : IsElementary (⋃ E ∈ S, E) := by sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.inter {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∩ F) := by
  sorry

theorem IsElementary.empty (d:ℕ) : IsElementary (∅: Set (EuclideanSpace' d)) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.sdiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E \ F) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.symmDiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (symmDiff E F) := by
  sorry

open Pointwise

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (x: EuclideanSpace' d) : IsElementary (E + {x}) := by
  sorry

/-- A sublemma for proving Lemma 1.1.2(i).  It is a geometrically obvious fact but surprisingly annoying to prove formally. -/
theorem BoundedInterval.partition (S: Finset BoundedInterval) : ∃ T: Finset BoundedInterval, T.toSet.PairwiseDisjoint BoundedInterval.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  let endpoints : Finset ℝ := S.image BoundedInterval.a ∪ S.image BoundedInterval.b
  have ha_mem {I:BoundedInterval} (hI: I ∈ S) : I.a ∈ endpoints := by grind
  have hb_mem {I:BoundedInterval} (hI: I ∈ S) : I.b ∈ endpoints := by grind
  let k := endpoints.card
  let sorted : Fin k ≃o endpoints := endpoints.orderIsoOfFin (by rfl)
  let a : ℕ → ℝ := fun n ↦ if h:n < k then sorted ⟨n,h⟩ else 0  -- 0 is a junk value
  let T := Finset.univ.image (fun x:endpoints ↦ Icc x x)
    ∪ (Finset.range (k-1)).image (fun n ↦ Ioo (a n) (a (n+1)))
  refine' ⟨T,_,_⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro I hI J hJ hIJ
    have := hIJ.some_mem
    simp_all [T]
    obtain ⟨ x, hx, rfl ⟩ | ⟨ n, hn, rfl ⟩ := hI
      <;> obtain ⟨ y, hy, rfl ⟩ | ⟨ m, hm, rfl ⟩ := hJ
      <;> simp at this
    . rw [show x=y by grind]
    . rw [this.1] at this
      set n := sorted.symm ⟨ x, hx ⟩
      have hax : x = sorted n := by simp [n]
      obtain ⟨ n, hn ⟩ := n
      simp [a, show m < k by omega, show m+1 < k by omega, hax] at this
      omega
    . rw [this.2] at this
      set m := sorted.symm ⟨ y, hy ⟩
      have hay : y = sorted m := by simp [m]
      obtain ⟨ m, hm ⟩ := m
      simp [a, show n < k by omega, show n+1 < k by omega, hay] at this
      omega
    have h1 : a n < a (m+1) := this.1.1.trans this.2.2
    have h2 : a m < a (n+1) := this.2.1.trans this.1.2
    simp [a, show n < k by omega, show n+1 < k by omega,
          show m < k by omega, show m+1 < k by omega] at h1 h2
    rw [show n=m by omega]
  intro I hI
  use {J | J.val ⊆ I }
  ext x; simp; constructor
  . intro hx
    by_cases hend : x ∈ endpoints
    . use Icc x x; simp [T, hx, hend]
    let n := sorted.symm ⟨ I.a, ha_mem hI ⟩
    let m := sorted.symm ⟨ I.b, hb_mem hI ⟩
    have hnI : I.a = sorted n := by simp [n]
    have hmI : I.b = sorted m := by simp [m]
    obtain ⟨ m, hm ⟩ := m; obtain ⟨ n, hn ⟩ := n
    apply I.subset_Icc at hx
    simp [hnI, hmI] at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    have H : ∃ m, x ≤ a m := by use m; grind
    let r := Nat.find H
    have hrm : r ≤ m := by convert Nat.find_min' H _; grind
    have hr : r < k := by linarith
    have hxr : x ≤ sorted ⟨ r, hr ⟩ := by convert Nat.find_spec H; grind
    have hnr : n < r := by
      by_contra!
      replace : (sorted ⟨r, hr⟩).val ≤ (sorted ⟨n, hn⟩).val := by simp [this]
      simp [show x = sorted ⟨ n, hn ⟩ by order] at hend
    refine' ⟨ Ioo (sorted ⟨ r-1, by omega ⟩) (sorted ⟨ r, hr ⟩), _ , _, _ ⟩
    . apply Set.Subset.trans _ I.Ioo_subset
      simp [hnI, hmI]
      apply Set.Ioo_subset_Ioo <;> simp <;> omega
    . simp [T]; refine' ⟨ r-1, by omega, _ ⟩
      simp [a, show r-1 < k by omega, show r < k by omega, show r-1+1=r by omega]
    simp
    have h1 : x ≠ sorted ⟨ r, hr ⟩ := by by_contra!; simp [this] at hend
    have h3 : sorted ⟨ r-1, by omega ⟩ < x := by
      by_contra!
      convert Nat.find_min H (show r-1 < r by omega) _
      simp [a, show r-1 < k by omega, this]
    grind
  grind

/-- Lemma 1.1.2(i) -/
theorem Box.partition {d:ℕ} (S: Finset (Box d)) : ∃ T: Finset (Box d), T.toSet.PairwiseDisjoint Box.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  choose T hTdisj hT using BoundedInterval.partition
  let J : Fin d → Finset BoundedInterval := fun i ↦ T (S.image (fun B ↦ B.side i))
  have hJdisj (i:Fin d) : (J i).toSet.PairwiseDisjoint BoundedInterval.toSet :=
    hTdisj (S.image (fun B ↦ B.side i))
  have hJ (i:Fin d) {B: Box d} (hB: B ∈ S) : ∃ U : Set (J i), B.side i = ⋃ K ∈ U, K.val.toSet := by
    apply hT (S.image (fun B ↦ B.side i)) (B.side i); simp; use B
  classical
  refine' ⟨ (Finset.univ.pi J).image (fun I ↦ ⟨ fun i ↦ I i (by simp) ⟩ ) , _, _ ⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂; simp at hB₁ hB₂
    obtain ⟨ J₁, hJ₁, rfl ⟩ := hB₁
    obtain ⟨ J₂, hJ₂, rfl ⟩ := hB₂
    ext i; simp
    have := hB₁B₂.some_mem
    simp [Box.toSet] at this
    rw [Set.mem_pi, Set.mem_pi] at this
    obtain ⟨ h₁, h₂ ⟩ := this
    specialize hJdisj i; rw [Set.pairwiseDisjoint_iff] at hJdisj
    apply_rules [hJdisj, Set.nonempty_of_mem (x := (hB₁B₂.some i))]
    grind
  intro B hB
  choose U hU using hJ
  use {B' | ∀ i, ∃ hi : B'.val.side i ∈ J i, ⟨ _, hi ⟩ ∈ U i hB}
  ext; simp [Box.toSet]; rw [Set.mem_pi]
  conv => lhs; intro i _; rw [hU i hB]
  conv => rhs; congr; intro a; rhs; rw [Set.mem_pi]
  simp; constructor
  . intro h; choose I hI using h
    refine' ⟨ ⟨ I ⟩, ⟨ ⟨ fun i _ ↦ I i, _⟩, _ ⟩, _ ⟩ <;> grind
  rintro ⟨ B', ⟨ h1, h2 ⟩, h3 ⟩ i; use B'.side i
  aesop

theorem IsElementary.partition {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: IsElementary E) : ∃ T: Finset (Box d), T.toSet.PairwiseDisjoint Box.toSet ∧ E = ⋃ J ∈ T, J.toSet := by
  obtain ⟨ S, rfl ⟩ := hE
  have ⟨ T', hT', hST' ⟩ := Box.partition S
  choose U hU using hST'
  conv => rhs; ext T; rhs; lhs; rhs; ext B; rhs; ext h; rw [hU B h]
  classical
  use T'.filter (fun J ↦ ∃ B, ∃ h:B ∈ S, J ∈ Subtype.val '' (U B h))
  simp; split_ands
  . apply hT'.subset; intro _; simp; tauto
  ext; simp; grind

/-- Helper lemma for Lemma 1.1.2(ii) -/
theorem BoundedInterval.sample_finite (I : BoundedInterval) {N:ℕ} (hN: N ≠ 0):
  Finite ↥(I.toSet ∩ (Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n))) := by
  sorry

/-- Exercise for Lemma 1.1.2(ii) -/
theorem BoundedInterval.length_eq (I : BoundedInterval) :
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)⁻¹ * Nat.card ↥(I.toSet ∩ (Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n))))
  (nhds |I|ₗ) := by
  sorry

def Box.sample_congr {d:ℕ} (B:Box d) (N:ℕ) :
↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))) ≃ ((i : Fin d) → ↑(↑(B.side i) ∩ Set.range fun n:ℤ ↦ (N:ℝ)⁻¹ * ↑n)) := {
    toFun x i := by
      obtain ⟨ x, hx ⟩ := x; refine ⟨ x i, ?_ ⟩
      simp [Box.toSet] at hx; rw [Set.mem_pi] at hx
      grind
    invFun x := by
      refine ⟨ fun i ↦ x i, ?_ ⟩
      simp [Box.toSet]; rw [Set.mem_pi]; split_ands
      . grind
      have h (i:Fin d) : ∃ y:ℤ, (N:ℝ)⁻¹ * y = x i := by
        obtain ⟨ x, hx ⟩ := x i; simp at hx; grind
      choose y hy using h; use y; simp [hy]
    left_inv x := by grind
    right_inv x := by aesop
  }

/-- Helper lemma for Lemma 1.1.2(ii) -/
theorem Box.sample_finite {d:ℕ} (B: Box d) {N:ℕ} (hN: N ≠ 0):
  Finite ↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))) := by
    rw [Equiv.finite_iff (B.sample_congr N)]
    apply @Pi.finite _ _ _ (fun i ↦ (B.side i).sample_finite hN)

/-- Helper lemma for Lemma 1.1.2(ii) -/
theorem Box.vol_eq {d:ℕ} (B: Box d):
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))))
  (nhds |B|ᵥ) := by
  simp [Box.volume]
  have : ∀ i ∈ Finset.univ, Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)⁻¹ * Nat.card ↥((B.side i).toSet ∩ Set.range ((fun n:ℤ ↦ (N:ℝ)⁻¹*n)))) (nhds |B.side i|ₗ) := fun i _ ↦ (B.side i).length_eq
  convert tendsto_finset_prod Finset.univ this with N
  simp [Finset.prod_mul_distrib]; left
  norm_cast; simp_rw [←Nat.card_coe_set_eq, ←Nat.card_pi]
  apply Nat.card_congr (B.sample_congr N)


/-- Lemma 1.1.2(ii), helper lemma -/
theorem Box.sum_vol_eq {d:ℕ} {T: Finset (Box d)}
 (hT: T.toSet.PairwiseDisjoint Box.toSet) :
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥((⋃ B ∈ T, B.toSet) ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))))
  (nhds (∑ B ∈ T, |B|ᵥ)) := by
  apply (tendsto_finset_sum T (fun B _ ↦ B.vol_eq)).congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]; use 1; intro N hN
  symm; convert Finset.mul_sum _ _ _
  convert Nat.cast_sum _ _
  rw [←Finset.sum_coe_sort, ←@Nat.card_sigma _ _ _ ?_]
  . exact Nat.card_congr {
      toFun x := by
        obtain ⟨ x, hx ⟩ := x
        simp at hx
        have hB := hx.1.choose_spec
        refine ⟨ ⟨ hx.1.choose, hB.1 ⟩, ⟨ x, ?_⟩ ⟩
        simp_all
      invFun x := by
        obtain ⟨ ⟨ B, hB ⟩, ⟨ x, hx ⟩ ⟩ := x
        refine ⟨ x, ?_ ⟩
        simp_all; aesop
      left_inv x := by grind
      right_inv x := by
        obtain ⟨ ⟨ B, hB ⟩, ⟨ x, hxB⟩ ⟩ := x
        simp at hxB
        have : ∃ B ∈ T, x ∈ B.toSet := by use B; tauto
        have h : this.choose = B := by
          have h := this.choose_spec
          apply hT.elim h.1 hB
          rw [Set.not_disjoint_iff]; grind
        simp [h, ←eq_cast_iff_heq]
    }
  intro ⟨ B, _ ⟩; convert B.sample_finite ?_
  omega

/-- Lemma 1.1.2(ii) -/
theorem Box.measure_uniq {d:ℕ} {T₁ T₂: Finset (Box d)}
 (hT₁: T₁.toSet.PairwiseDisjoint Box.toSet)
 (hT₂: T₂.toSet.PairwiseDisjoint Box.toSet)
 (heq: ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) :
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
  apply tendsto_nhds_unique _ (Box.sum_vol_eq hT₂)
  rw [←heq]
  exact Box.sum_vol_eq hT₁

noncomputable abbrev IsElementary.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : ℝ
  := ∑ B ∈ hE.partition.choose, |B|ᵥ

theorem IsElementary.measure_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E)
  {T: Finset (Box d)} (hT: T.toSet.PairwiseDisjoint Box.toSet)
  (heq : E = ⋃ B ∈ T, B.toSet):
  hE.measure = ∑ B ∈ T, |B|ᵥ := by
  apply Box.measure_uniq hE.partition.choose_spec.1 hT _
  rw [←heq, ←hE.partition.choose_spec.2]

/-- Exercise 1.1.2: give an alternate proof of this proposition by showing that
the two partitions `T₁`, `T₂` admit a mutual refinement into boxes arising from
taking Cartesian products of elements from finite collections of disjoint intervals. -/
theorem Box.measure_uniq' {d:ℕ} {T₁ T₂: Finset (Box d)}
 (hT₁: T₁.toSet.PairwiseDisjoint Box.toSet)
 (hT₂: T₂.toSet.PairwiseDisjoint Box.toSet)
 (heq: ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) :
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
 sorry

example :
  let E : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' ((Set.Ioo 1 2) ∪ (Set.Icc 3 6))
  ∃ hE : IsElementary E, hE.measure = 4 := by
  extract_lets E
  classical
  let T : Finset (Box 1) := {(BoundedInterval.Ioo 1 2:Box 1), (BoundedInterval.Icc 3 6:Box 1)}
  have hET : E = ⋃ B ∈ T, B.toSet := by
    simp [E, T, Set.image_union]
  let hE : IsElementary E := ⟨ T, hET⟩
  use hE
  rw [hE.measure_eq _ hET]
  . rw [Finset.sum_pair]
    . norm_num
    by_contra!; simp [-Box.mk.injEq] at this
  rw [Set.pairwiseDisjoint_iff]
  simp [T]; split_ands <;> intro ⟨ x, hx ⟩ <;> grind

lemma IsElementary.measure_nonneg {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) :
  0 ≤ hE.measure := by
  -- Strategy:
  -- 1. Unfold measure: hE.measure = ∑ B ∈ partition, |B|ᵥ
  -- 2. Show each |B|ᵥ ≥ 0: volume is product of lengths, each length = max(...) ≥ 0
  -- 3. Apply Finset.sum_nonneg: sum of non-negative terms is non-negative
  -- Step 1: Unfold measure definition
  rw [IsElementary.measure]
  -- Step 2: Show each |B|ᵥ ≥ 0 for B in the partition
  have hvol_nonneg : ∀ B ∈ hE.partition.choose, 0 ≤ |B|ᵥ := by
    intro B hB
    -- Volume is product of lengths
    rw [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    -- Each length = max(...) ≥ 0
    rw [BoundedInterval.length]
    exact le_max_right _ _
  -- Step 3: Apply Finset.sum_nonneg with the fact from step 2
  exact Finset.sum_nonneg hvol_nonneg

lemma IsElementary.measure_of_disjUnion {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F) (hdisj: Disjoint E F):
  (hE.union hF).measure = hE.measure + hF.measure := by
  -- Strategy:
  -- 1. Get partitions: T_E = hE.partition.choose, T_F = hF.partition.choose
  -- 2. Show T_E ∪ T_F is pairwise disjoint
  -- 3. Show E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet using partition properties
  -- 4. Use IsElementary.measure_eq to show (hE.union hF).measure = ∑ B ∈ T_E ∪ T_F, |B|ᵥ
  -- 5. Use Finset.sum_union to split: ∑ B ∈ T_E ∪ T_F, |B|ᵥ = ∑ B ∈ T_E, |B|ᵥ + ∑ B ∈ T_F, |B|ᵥ
  -- 6. Apply IsElementary.measure_eq to show hE.measure = ∑ B ∈ T_E, |B|ᵥ and hF.measure = ∑ B ∈ T_F, |B|ᵥ
  classical -- for axiom of choice
  -- Step 1: Get partitions
  set T_E := hE.partition.choose
  set T_F := hF.partition.choose
  have hT_E_disj : T_E.toSet.PairwiseDisjoint Box.toSet := hE.partition.choose_spec.1
  have hT_F_disj : T_F.toSet.PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
  have hE_eq : E = ⋃ B ∈ T_E, B.toSet := hE.partition.choose_spec.2
  have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
  -- Step 2: Show T_E ∪ T_F is pairwise disjoint
  have hT_union_disj : (T_E ∪ T_F).toSet.PairwiseDisjoint Box.toSet := by
    rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂
    simp at hB₁ hB₂
    -- Helper: boxes from different partitions can't intersect (E and F are disjoint)
    have h_cross_disj : ∀ B_E ∈ T_E, ∀ B_F ∈ T_F, (B_E.toSet ∩ B_F.toSet).Nonempty → False := by
      intro B_E hB_E B_F hB_F h_intersect
      obtain ⟨x, hx₁, hx₂⟩ := h_intersect
      have : x ∈ E ∩ F := by
        constructor
        · rw [hE_eq]
          exact Set.mem_biUnion hB_E hx₁
        · rw [hF_eq]
          exact Set.mem_biUnion hB_F hx₂
      rw [Set.disjoint_iff] at hdisj
      exact Set.notMem_empty x (hdisj this)
    -- Case analysis on which partitions the boxes belong to
    obtain (hB₁_E | hB₁_F) := hB₁ <;> obtain (hB₂_E | hB₂_F) := hB₂
    · -- Both in T_E: use hT_E_disj
      rw [Set.pairwiseDisjoint_iff] at hT_E_disj
      exact hT_E_disj hB₁_E hB₂_E hB₁B₂
    · -- B₁ in T_E, B₂ in T_F: contradiction via h_cross_disj
      exact False.elim (h_cross_disj B₁ hB₁_E B₂ hB₂_F hB₁B₂)
    · -- B₁ in T_F, B₂ in T_E: contradiction via h_cross_disj (symmetric case)
      exact False.elim (h_cross_disj B₂ hB₂_E B₁ hB₁_F (Set.inter_comm B₁.toSet B₂.toSet ▸ hB₁B₂))
    · -- Both in T_F: use hT_F_disj
      rw [Set.pairwiseDisjoint_iff] at hT_F_disj
      exact hT_F_disj hB₁_F hB₂_F hB₁B₂
  -- Step 3: Show E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet
  have h_union_eq : E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet := by
    rw [hE_eq, hF_eq]
    ext x
    simp [Set.mem_union, Finset.mem_union]
    constructor
    · rintro (⟨B, hB, hx⟩ | ⟨B, hB, hx⟩)
      · exact ⟨B, Or.inl hB, hx⟩
      · exact ⟨B, Or.inr hB, hx⟩
    · rintro ⟨B, hB | hB, hx⟩
      · left; exact ⟨B, hB, hx⟩
      · right; exact ⟨B, hB, hx⟩
  -- Step 4: Use IsElementary.measure_eq
  have h_union_measure : (hE.union hF).measure = ∑ B ∈ T_E ∪ T_F, |B|ᵥ :=
    (hE.union hF).measure_eq hT_union_disj h_union_eq
  -- Step 5: Use Finset.sum_union_inter to split the sum
  have h_sum_split : ∑ B ∈ T_E ∪ T_F, |B|ᵥ = ∑ B ∈ T_E, |B|ᵥ + ∑ B ∈ T_F, |B|ᵥ := by
    rw [←Finset.sum_union_inter]
    suffices ∑ B ∈ T_E ∩ T_F, |B|ᵥ = 0 by
      simp [this]
    apply Finset.sum_eq_zero
    intro B hB
    simp [Finset.mem_inter] at hB
    obtain ⟨hB_E, hB_F⟩ := hB
    -- B is in both partitions, so B.toSet ⊆ E ∩ F = ∅
    have hB_subset_empty : B.toSet ⊆ ∅ := by
      have hB_E_subset : B.toSet ⊆ E := by
        rw [hE_eq]
        intro x hx
        exact Set.mem_biUnion hB_E hx
      have hB_F_subset : B.toSet ⊆ F := by
        rw [hF_eq]
        intro x hx
        exact Set.mem_biUnion hB_F hx
      have : B.toSet ⊆ E ∩ F := Set.subset_inter hB_E_subset hB_F_subset
      exact this.trans (Set.disjoint_iff_inter_eq_empty.1 hdisj).subset
    -- Since B.toSet ⊆ ∅, we have B.toSet = ∅, so volume is 0
    have hB_empty : B.toSet = ∅ := Set.subset_empty_iff.1 hB_subset_empty
    exact Box.volume_eq_zero_of_empty B hB_empty
  -- Step 6: Apply IsElementary.measure_eq to individual measures
  have hE_measure : hE.measure = ∑ B ∈ T_E, |B|ᵥ := hE.measure_eq hT_E_disj hE_eq
  have hF_measure : hF.measure = ∑ B ∈ T_F, |B|ᵥ := hF.measure_eq hT_F_disj hF_eq
  -- Combine everything
  rw [h_union_measure, h_sum_split, hE_measure, hF_measure]

-- Helper lemmas for measure_of_disjUnion'

/-- Two different proofs that a set is elementary yield the same measure. -/
lemma IsElementary.measure_irrelevant {d:ℕ} {E: Set (EuclideanSpace' d)}
    (h₁ h₂ : IsElementary E) : h₁.measure = h₂.measure := by
  classical
  -- Use the partition data packaged inside h₂
  obtain ⟨h_pair, h_union⟩ := h₂.partition.choose_spec
  -- Evaluate both measures via the same partition
  have h₁_exp := h₁.measure_eq h_pair h_union
  have h₂_exp := h₂.measure_eq h_pair h_union
  simp [h₂_exp] at h₁_exp
  assumption

/-- If two elementary sets are equal, their measures are equal. -/
lemma IsElementary.measure_eq_of_set_eq {d:ℕ} {E F: Set (EuclideanSpace' d)}
    (hE: IsElementary E) (hF: IsElementary F) (h: E = F) :
    hE.measure = hF.measure := by
  subst h  -- Now both proofs describe the same set
  exact IsElementary.measure_irrelevant hE hF

/-- The union over an empty finset of elementary sets is the empty set. -/
lemma IsElementary.union'_empty_eq {d:ℕ} :
    (⋃ E ∈ (∅ : Finset (Set (EuclideanSpace' d))), E) = ∅ := by
  simp

open Classical in
/-- Measure of a sum over `insert a S'` equals the measure of `a` plus the measure of the sum over `S'`. -/
lemma IsElementary.sum_insert_split {d:ℕ} {a: Set (EuclideanSpace' d)} {S': Finset (Set (EuclideanSpace' d))}
    (ha : a ∉ S')
    (hE: ∀ E ∈ insert a S', IsElementary E) :
    ∑ E:(insert a S' : Finset (Set (EuclideanSpace' d))), (hE E.val E.property).measure =
    (hE a (Finset.mem_insert_self _ _)).measure +
    ∑ E:S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure := by
  induction S' using Finset.induction_on with
  | empty =>
    -- Base case: S' = ∅
    -- LHS: ∑ E:(insert a ∅), ... = sum over {a}
    -- RHS: measure of a + ∑ E:∅, ... = measure of a + 0
    simp [Finset.sum_empty]
  | @insert b S'' hb_notin ih =>
    -- Inductive case: S' = insert b S''
    -- Goal: ∑ E:(insert a (insert b S'')), ... = measure(a) + ∑ E:(insert b S''), ...
    -- Use simp to expand both sides
    simp [hb_notin]
    -- Now split the sum on the LHS using Finset.sum_insert
    -- First split out a
    have ha_ne_b : a ≠ b := by simp_all
    have ha_notin_S'' : a ∉ S'' := by simp_all
    rw [Finset.sum_insert (by simp [ha_ne_b, ha_notin_S''])]
    -- Now split out b from the remaining sum
    rw [Finset.sum_insert (by simp [hb_notin])]
    -- Both sides should now match
    simp

lemma IsElementary.measure_of_disjUnion' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) (hdisj: S.toSet.PairwiseDisjoint id):
  (IsElementary.union' hE).measure = ∑ E:S, (hE E.val E.property).measure := by
  -- Strategy: Induction on S. Base: empty set gives 0 = 0. Step: split S = insert a S',
  -- show union = a ∪ (union S'), prove a disjoint from union S' via pairwise disjointness,
  -- apply two-set additivity, use IH for S', combine.
  classical
  -- Induction on S using Finset.induction_on to reduce to two-set case
  induction S using Finset.induction_on with
  | empty =>
    -- Base case: S = ∅, both sides are 0
    have h_set_eq := IsElementary.union'_empty_eq (d := d)
    have h_measure_eq : (IsElementary.union' hE).measure = (IsElementary.empty d).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (IsElementary.empty d) h_set_eq
    rw [h_measure_eq]
    -- Show (IsElementary.empty d).measure = 0
    have h_empty_measure : (IsElementary.empty d).measure = 0 := by
      have h_empty_eq : (∅ : Set (EuclideanSpace' d)) = ⋃ B ∈ (∅ : Finset (Box d)), B.toSet := by simp
      have h_empty_disj : ((∅ : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by simp
      rw [(IsElementary.empty d).measure_eq h_empty_disj h_empty_eq]
      simp [Finset.sum_empty]
    rw [h_empty_measure]
    simp [Finset.sum_empty]
  | @insert a S' ha_notin ih =>
    -- Extract hypotheses for S' and element a
    have hE_S' : ∀ E ∈ S', IsElementary E := by
      intro E hE_mem
      exact hE E (Finset.mem_insert_of_mem hE_mem)
    have hdisj_S' : S'.toSet.PairwiseDisjoint id := by
      intro E₁ hE₁ E₂ hE₂ hne
      apply hdisj
      · simp [hE₁]
      · simp [hE₂]
      · exact hne
    have hE_a : IsElementary a := hE a (Finset.mem_insert_self _ _)

    -- Show the union over insert a S' equals a ∪ (union over S')
    have h_union_split : ⋃ E ∈ insert a S', E = a ∪ (⋃ E ∈ S', E) := by
      ext x
      simp [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]

    -- Prove a is disjoint from the union over S'
    have h_disj : Disjoint a (⋃ E ∈ S', E) := by
      rw [Set.disjoint_iff]
      intro x ⟨hx_a, hx_rest⟩
      simp [Set.mem_iUnion] at hx_rest
      obtain ⟨E, hE_mem, hx_E⟩ := hx_rest
      -- Use hdisj to show a and E are disjoint
      have h_disj_a_E : Disjoint a E := by
        have ha_mem : a ∈ (insert a S').toSet := by simp
        have hE_mem' : E ∈ (insert a S').toSet := by simp [hE_mem]
        have hne : a ≠ E := by
          intro h; subst h
          exact ha_notin hE_mem
        -- hdisj: (insert a S').toSet.PairwiseDisjoint id means distinct sets are disjoint
        -- Rewrite to extract the disjointness property
        rw [Set.pairwiseDisjoint_iff] at hdisj
        -- After rewriting, hdisj says: for distinct i, j in the set, (id i ∩ id j).Nonempty → i = j
        -- We have x ∈ a and x ∈ E, so (id a ∩ id E).Nonempty, which would give a = E
        -- But we also have hne : a ≠ E, so this is a contradiction
        have h_inter_nonempty : (id a ∩ id E).Nonempty := by
          simp [id]
          exact ⟨x, hx_a, hx_E⟩
        have h_eq := hdisj ha_mem hE_mem' h_inter_nonempty
        -- h_eq says a = E, but we have hne : a ≠ E, contradiction
        exact (hne h_eq).elim
      rw [Set.disjoint_iff] at h_disj_a_E
      exact h_disj_a_E ⟨hx_a, hx_E⟩

    -- Apply the two-set additivity lemma
    let hE_rest : IsElementary (⋃ E ∈ S', E) := IsElementary.union' hE_S'
    have h_two_set : (hE_a.union hE_rest).measure = hE_a.measure + hE_rest.measure :=
      IsElementary.measure_of_disjUnion hE_a hE_rest h_disj

    -- Equate the union witness measure with the two-set union measure
    have h_measure_eq : (IsElementary.union' hE).measure = (hE_a.union hE_rest).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (hE_a.union hE_rest) h_union_split

    -- Split the sum into measure of a plus sum over S'
    have h_sum_split := IsElementary.sum_insert_split ha_notin hE
    -- Apply inductive hypothesis to the union over S', reconciling proof differences
    have h_ih_applied : hE_rest.measure = ∑ E : S', (hE_S' E.val E.property).measure := ih hE_S' hdisj_S'
    -- hE_S' is defined as hE_S' E hE_mem = hE E (Finset.mem_insert_of_mem hE_mem),
    -- so the sums are definitionally equal and we can use h_ih_applied directly
    have h_ih_adjusted : hE_rest.measure = ∑ E : S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure :=
      h_ih_applied

    -- Combine all equalities to finish
    rw [h_measure_eq, h_two_set, h_sum_split]
    congr 1

@[simp]
lemma IsElementary.measure_of_empty (d:ℕ) : (IsElementary.empty d).measure = 0 := by
  -- Strategy: Use empty partition T = ∅, apply measure_eq, simplify with Finset.sum_empty
  classical
  have h_empty_eq : (∅ : Set (EuclideanSpace' d)) = ⋃ B ∈ (∅ : Finset (Box d)), B.toSet := by
    simp
  have h_empty_disj : ((∅ : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by
    simp
  rw [(IsElementary.empty d).measure_eq h_empty_disj h_empty_eq]
  simp [Finset.sum_empty]

@[simp]
lemma IsElementary.measure_of_box {d:ℕ} (B: Box d) : (IsElementary.box B).measure = |B|ᵥ := by
  -- Strategy: Use singleton partition T = {B}, apply measure_eq, simplify with Finset.sum_singleton
  classical
  have h_box_eq : B.toSet = ⋃ B' ∈ ({B} : Finset (Box d)), B'.toSet := by
    simp
  have h_box_disj : (({B} : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by
    rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂
    simp at hB₁ hB₂
    -- For a singleton, B₁ = B₂ = B, so the condition is vacuously satisfied
    rw [hB₁, hB₂]
  rw [(IsElementary.box B).measure_eq h_box_disj h_box_eq]
  simp [Finset.sum_singleton]

lemma IsElementary.measure_mono  {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F) (hcont: E ⊆ F):
  hE.measure ≤ hF.measure := by
  -- Strategy using set difference:
  -- 1. Decompose F = E ∪ (F \ E) (disjoint since E ⊆ F)
  -- 2. Show F \ E is elementary via IsElementary.sdiff
  -- 3. Apply measure_of_disjUnion: hF.measure = hE.measure + (F \ E).measure
  -- 4. Use measure_nonneg: (F \ E).measure ≥ 0, so hE.measure ≤ hF.measure
  -- Step 1: Decompose F = E ∪ (F \ E)
  have hF_decomp : F = E ∪ (F \ E) := by
    ext x
    constructor
    · intro hx; by_cases hx_E : x ∈ E
      · left; exact hx_E
      · right; exact ⟨hx, hx_E⟩
    · intro h; obtain (hx_E | ⟨hx, _⟩) := h
      · exact hcont hx_E
      · exact hx
  -- Step 2: Show F \ E is elementary and disjoint from E
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]; intro x ⟨hx_E, _, hx_not_E⟩; exact hx_not_E hx_E
  -- Step 3: Apply measure_of_disjUnion
  have h_union_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Step 4: Show that (hE.union hF_sdiff_E) and hF represent the same set F
  classical
  set T_F := hF.partition.choose
  have hT_F_disj : T_F.toSet.PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
  have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
  have h_union_eq_partition : E ∪ (F \ E) = ⋃ B ∈ T_F, B.toSet := by rw [← hF_decomp, hF_eq]
  -- Step 5: Use measure_eq to show (hE.union hF_sdiff_E).measure = hF.measure
  have h_union_measure_eq : (hE.union hF_sdiff_E).measure = hF.measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_F_disj h_union_eq_partition, hF.measure_eq hT_F_disj hF_eq]
  -- Step 6: Combine with measure_nonneg
  rw [← h_union_measure_eq, h_union_measure]
  linarith [IsElementary.measure_nonneg hF_sdiff_E]

lemma IsElementary.measure_of_union {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F):
  (hE.union hF).measure ≤ hE.measure + hF.measure := by
  -- Strategy (using Exercise 1.1.1):
  -- 1. Decompose E ∪ F = E ∪ (F \ E) (disjoint union)
  -- 2. Use IsElementary.sdiff (Exercise 1.1.1) to show F \ E is elementary
  -- 3. Apply measure_of_disjUnion: (hE.union hF_sdiff_E).measure = hE.measure + (F \ E).measure
  -- 4. Show (hE.union hF) and (hE.union hF_sdiff_E) represent the same set E ∪ F
  -- 5. Apply measure_mono: (F \ E).measure ≤ hF.measure since F \ E ⊆ F
  -- 6. Combine: (hE.union hF).measure = hE.measure + (F \ E).measure ≤ hE.measure + hF.measure
  -- Step 1: Decompose E ∪ F = E ∪ (F \ E)
  have h_union_decomp : E ∪ F = E ∪ (F \ E) := by
    ext x
    constructor
    · rintro (hx_E | hx_F); exact Or.inl hx_E
      by_cases hx_E : x ∈ E; exact Or.inl hx_E; exact Or.inr ⟨hx_F, hx_E⟩
    · rintro (hx_E | ⟨hx_F, _⟩); exact Or.inl hx_E; exact Or.inr hx_F
  -- Step 2-3: Use IsElementary.sdiff and apply measure_of_disjUnion
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]; intro x ⟨hx_E, _, hx_not_E⟩; exact hx_not_E hx_E
  have h_union_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Step 4: Show both unions represent the same set E ∪ F
  classical
  set T := (hE.union hF).partition.choose
  have hT_disj : T.toSet.PairwiseDisjoint Box.toSet := (hE.union hF).partition.choose_spec.1
  have h_eq : E ∪ F = ⋃ B ∈ T, B.toSet := (hE.union hF).partition.choose_spec.2
  have h_union_measure_eq : (hE.union hF_sdiff_E).measure = (hE.union hF).measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_disj (by rw [← h_union_decomp, h_eq]),
        (hE.union hF).measure_eq hT_disj h_eq]
  -- Step 5-6: Apply measure_mono and combine
  have h_mono : hF_sdiff_E.measure ≤ hF.measure :=
    IsElementary.measure_mono hF_sdiff_E hF (fun _ hx => hx.1)
  rw [← h_union_measure_eq, h_union_measure]
  linarith


lemma IsElementary.measure_of_union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) :
  (IsElementary.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure := by
  sorry

/-- Helper: Translation preserves interval length -/
lemma BoundedInterval.length_of_translate (I: BoundedInterval) (c: ℝ) :
  ∃ I' : BoundedInterval, I'.toSet = I.toSet + {c} ∧ |I'|ₗ = |I|ₗ := by
  cases I with
  | Ioo a b => use Ioo (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Icc a b => use Icc (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Ioc a b => use Ioc (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Ico a b => use Ico (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]

/-- Helper: Translation preserves box volume -/
lemma Box.volume_of_translate {d:ℕ} (B: Box d) (x: EuclideanSpace' d) :
  ∃ B' : Box d, B'.toSet = B.toSet + {x} ∧ |B'|ᵥ = |B|ᵥ := by
  -- Strategy:
  -- 1. For each coordinate i, translate B.side i by x i using length_of_translate
  -- 2. Construct B' with translated intervals: B'.side i = translated interval
  -- 3. Show B'.toSet = B.toSet + {x}: y ∈ B'.toSet ↔ y - x ∈ B.toSet (coordinate-wise)
  -- 4. Show |B'|ᵥ = |B|ᵥ: product of lengths, each length preserved by translation
  -- Step 1: For each coordinate i, get translated interval
  choose I' hI' using fun i ↦ BoundedInterval.length_of_translate (B.side i) (x i)
  -- Step 2: Construct B' with translated intervals
  use ⟨fun i ↦ I' i⟩
  constructor
  -- Step 3: Show B'.toSet = B.toSet + {x}
  · ext y
    simp [Box.toSet, Set.mem_pi]
    constructor
    · intro hy i
      have : y i ∈ (I' i).toSet := hy i (Set.mem_univ i)
      rw [(hI' i).1] at this
      obtain ⟨a, ha, b, rfl, hab⟩ := this
      convert ha using 1; rw [← hab]; ring
    · intro hy i _
      simp; rw [(hI' i).1]
      use y i + -x i, hy i, x i, rfl; ring
  -- Step 4: Show |B'|ᵥ = |B|ᵥ
  · simp [Box.volume]
    congr 1
    ext i
    exact (hI' i).2

/-- Translation is injective on sets: if S₁ + {x} = S₂ + {x}, then S₁ = S₂ -/
lemma Set.translate_inj {d:ℕ} (x: EuclideanSpace' d) (S₁ S₂ : Set (EuclideanSpace' d))
  (h_eq : S₁ + {x} = S₂ + {x}) : S₁ = S₂ := by
  ext y
  constructor
  · intro hy
    have : y + x ∈ S₁ + {x} := Set.mem_add.mpr ⟨y, hy, x, Set.mem_singleton x, rfl⟩
    rw [h_eq] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp this
    rw [Set.mem_singleton_iff.mp hb] at hab
    exact (add_right_cancel hab) ▸ ha
  · intro hy
    have : y + x ∈ S₂ + {x} := Set.mem_add.mpr ⟨y, hy, x, Set.mem_singleton x, rfl⟩
    rw [← h_eq] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp this
    rw [Set.mem_singleton_iff.mp hb] at hab
    exact (add_right_cancel hab) ▸ ha

lemma IsElementary.measure_of_translate {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: IsElementary E) (x: EuclideanSpace' d):
  (hE.translate x).measure = hE.measure := by
  -- Strategy:
  -- 0. Case split: E = ∅ or E ≠ ∅
  --    a. Empty case: E = ∅ → E + {x} = ∅, both measures are 0
  --    b. Nonempty case: E ≠ ∅, proceed with partition translation
  -- 1. Get partition T of E: E = ⋃ B ∈ T, B.toSet (from hE.partition)
  -- 2. For each B ∈ T, use Box.volume_of_translate to get B' with B'.toSet = B.toSet + {x} and |B'|ᵥ = |B|ᵥ
  -- 3. Construct T' = {B' | B ∈ T} (using choose to get the translated boxes)
  -- 4. Show T' is pairwise disjoint (translation preserves disjointness)
  -- 5. Show E + {x} = ⋃ B' ∈ T', B'.toSet (translation distributes over union)
  -- 6. Apply measure_eq: (hE.translate x).measure = ∑ B' ∈ T', |B'|ᵥ = ∑ B ∈ T, |B|ᵥ = hE.measure
  classical
  by_cases h_empty : E = ∅
  · -- Empty case: E = ∅ → E + {x} = ∅, both measures are 0
    subst h_empty
    simp [IsElementary.measure_of_empty]
  · -- Nonempty case: E ≠ ∅
    -- Step 1: Get partition T of E, then filter to nonempty boxes
    set T := hE.partition.choose
    have hT_disj : T.toSet.PairwiseDisjoint Box.toSet := hE.partition.choose_spec.1
    have hE_eq : E = ⋃ B ∈ T, B.toSet := hE.partition.choose_spec.2
    -- Filter to nonempty boxes only (empty boxes contribute 0 to measure anyway)
    set T := T.filter (fun B => B.toSet.Nonempty) with hT_def
    have hT_disj : T.toSet.PairwiseDisjoint Box.toSet := by
      intro B₁ hB₁ B₂ hB₂ hB₁B₂
      simp only [Finset.mem_coe] at hB₁ hB₂
      exact hE.partition.choose_spec.1 (Finset.mem_of_mem_filter B₁ hB₁) (Finset.mem_of_mem_filter B₂ hB₂) hB₁B₂
    have hE_eq : E = ⋃ B ∈ T, B.toSet := by
      rw [hE_eq]
      ext y; simp
      constructor
      · intro ⟨B, hB, hy⟩
        exact ⟨B, Finset.mem_filter.mpr ⟨hB, ⟨y, hy⟩⟩, hy⟩
      · intro ⟨B, hB, hy⟩
        exact ⟨B, Finset.mem_of_mem_filter B hB, hy⟩
    have hT_nonempty : ∀ B ∈ T, B.toSet.Nonempty := by
      intro B hB
      exact (Finset.mem_filter.mp hB).2
    -- Step 2-3: Construct translated partition T'
    choose f hf using fun B : Box d => Box.volume_of_translate B x
    set T' := T.image f
    have hf_spec : ∀ B ∈ T, (f B).toSet = B.toSet + {x} ∧ |f B|ᵥ = |B|ᵥ := fun B hB => hf B
    -- Helper: f is injective on T (all boxes in T are nonempty by construction)
    have hf_inj : ∀ B₁ B₂, B₁ ∈ T → B₂ ∈ T → f B₁ = f B₂ → B₁ = B₂ := by
      intro B₁ B₂ hB₁ hB₂ h_eq
      have h_set_eq' : B₁.toSet = B₂.toSet :=
        Set.translate_inj x _ _ ((hf_spec B₁ hB₁).1.symm.trans ((congr_arg Box.toSet h_eq).trans (hf_spec B₂ hB₂).1))
      -- Since B₁ is in filtered T, it's nonempty, and B₁.toSet = B₂.toSet
      have h_inter_nonempty : (B₁.toSet ∩ B₂.toSet).Nonempty := by
        rw [h_set_eq', Set.inter_self]
        rw [← h_set_eq']
        exact hT_nonempty B₁ hB₁
      rw [Set.pairwiseDisjoint_iff] at hT_disj
      exact hT_disj hB₁ hB₂ h_inter_nonempty
    -- Step 4: Show T' is pairwise disjoint
    have hT'_disj : T'.toSet.PairwiseDisjoint Box.toSet := by
      rw [Set.pairwiseDisjoint_iff]
      intro B₁' hB₁' B₂' hB₂' hB₁'B₂'
      simp [T'] at hB₁' hB₂'
      obtain ⟨B₁, hB₁, rfl⟩ := hB₁'
      obtain ⟨B₂, hB₂, rfl⟩ := hB₂'
      by_cases h_eq : f B₁ = f B₂
      · exact h_eq
      · -- If f B₁ ≠ f B₂ but they intersect, then B₁ = B₂ (contradiction)
        have h_translate_inter : (f B₁).toSet ∩ (f B₂).toSet = (B₁.toSet ∩ B₂.toSet) + {x} := by
          rw [(hf_spec B₁ hB₁).1, (hf_spec B₂ hB₂).1]
          ext y; simp only [Set.mem_inter_iff, Set.mem_add]
          constructor
          · rintro ⟨⟨a₁, ha₁, b₁, hb₁, hab₁⟩, ⟨a₂, ha₂, b₂, hb₂, hab₂⟩⟩
            have hb₁_eq : b₁ = x := Set.mem_singleton_iff.mp hb₁
            have hb₂_eq : b₂ = x := Set.mem_singleton_iff.mp hb₂
            rw [hb₁_eq] at hab₁
            rw [hb₂_eq] at hab₂
            exact ⟨a₁, ⟨ha₁, add_right_cancel (hab₁.trans hab₂.symm) ▸ ha₂⟩, x, Set.mem_singleton x, hab₁⟩
          · rintro ⟨a, ⟨ha₁, ha₂⟩, b, hb, hab⟩
            rw [Set.mem_singleton_iff.mp hb] at hab
            exact ⟨⟨a, ha₁, x, Set.mem_singleton x, hab⟩, ⟨a, ha₂, x, Set.mem_singleton x, hab⟩⟩
        have h_B_nonempty : (B₁.toSet ∩ B₂.toSet).Nonempty := by
          rw [h_translate_inter] at hB₁'B₂'
          obtain ⟨y, hy⟩ := hB₁'B₂'
          obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
          exact ⟨a, ha.1, ha.2⟩
        rw [Set.pairwiseDisjoint_iff] at hT_disj
        exact (h_eq (congr_arg f (hT_disj hB₁ hB₂ h_B_nonempty))).elim
    -- Step 5: Show E + {x} = ⋃ B' ∈ T', B'.toSet
    have h_union_eq : E + {x} = ⋃ B' ∈ T', B'.toSet := by
      rw [hE_eq]
      ext y; simp
      constructor
      · rintro ⟨B, hB, hy⟩
        use f B, Finset.mem_image.mpr ⟨B, hB, rfl⟩
        rw [(hf_spec B hB).1]
        exact ⟨y + -x, hy, x, Set.mem_singleton x, by simp [add_assoc, add_zero]⟩
      · rintro ⟨B', hB', hy⟩
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
        rw [(hf_spec B hB).1] at hy
        obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
        rw [Set.mem_singleton_iff.mp hb] at hab
        exact ⟨B, hB, by rw [← hab]; simp [add_assoc, add_neg_cancel, add_zero]; exact ha⟩
    -- Step 6: Apply measure_eq and show sum equality
    have h_translate_measure : (hE.translate x).measure = ∑ B' ∈ T', |B'|ᵥ :=
      (hE.translate x).measure_eq hT'_disj h_union_eq
    have h_sum_eq : ∑ B' ∈ T', |B'|ᵥ = ∑ B ∈ T, |B|ᵥ := by
      rw [Finset.sum_image (fun B₁ hB₁ B₂ hB₂ h_eq => hf_inj B₁ B₂ hB₁ hB₂ h_eq)]
      exact Finset.sum_congr rfl fun B hB => (hf_spec B hB).2
    rw [h_translate_measure, h_sum_eq, hE.measure_eq hT_disj hE_eq]

/-- Exercise 1.1.3 (uniqueness of elementary measure) -/
theorem IsElementary.measure_uniq {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (IsElementary E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (hF: IsElementary F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE) : ∃ c, c ≥ 0 ∧ ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE = c * hE.measure := by
    sorry

abbrev Box.unit_cube (d:ℕ) : Box d := { side := fun _ ↦ BoundedInterval.Ioc 0 1}

theorem IsElementary.measure_uniq' {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (IsElementary E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (hF: IsElementary F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE)
  (hcube : m' (Box.unit_cube d) (IsElementary.box _) = 1) :
  ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE = hE.measure := by
    sorry

abbrev Box.prod {d₁ d₂:ℕ} (B₁: Box d₁) (B₂: Box d₂) : Box (d₁ + d₂) where
  side i := by
    obtain ⟨ i, hi ⟩ := i
    exact if h : i < d₁ then B₁.side ⟨i, h⟩ else (B₂.side ⟨i - d₁, by omega⟩)

/-- Exercise 1.1.4 -/
theorem IsElementary.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: IsElementary E₁) (hE₂: IsElementary E₂) : IsElementary (EuclideanSpace'.prod E₁ E₂) := by sorry

theorem IsElementary.measure_of_prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: IsElementary E₁) (hE₂: IsElementary E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by sorry
