import Analysis.MeasureTheory.Section_1_1_3
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Countable

/-!
# Introduction to Measure Theory, Section 1.2: Lebesgue measure

A companion to (the introduction to) Section 1.2 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Exercise 1.2.1 -/
-- Jordan measurability is not preserved by countable unions: there exists a sequence of Jordan measurable sets whose union is not Jordan measurable.
example : ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
  (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n)))
  ∧ ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  sorry

/-- Exercise 1.2.1 -/
-- Jordan measurability is not preserved by countable intersections: there exists a sequence of Jordan measurable sets whose intersection is not Jordan measurable.
example : ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
  (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n)))
  ∧ ¬ JordanMeasurable (⋂ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  sorry

/-- Exercise 1.2.2 -/
-- The pointwise limit of uniformly bounded Riemann integrable functions need not be Riemann integrable.
example : ∃ f: ℕ → ℝ → ℝ, ∃ F: ℝ → ℝ, ∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M ∧
    (∀ x ∈ Set.Icc 0 1, Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (F x))) ∧
    (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) ∧
    ¬ RiemannIntegrableOn F (Icc 0 1) := by
  sorry

/-- Exercise 1.2.2 -/
-- Determine whether uniform convergence of uniformly bounded Riemann integrable functions preserves Riemann integrability (true or false).
def Ex_1_2_2b : Decidable ( ∀ f: ℕ → ℝ → ℝ, ∀ F: ℝ → ℝ, (∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M) → (∀ x ∈ Set.Icc 0 1, TendstoUniformly f F Filter.atTop) → (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) → RiemannIntegrableOn F (Icc 0 1) ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`, depending on whether you believe the given statement to be true or false.
  sorry

-- The Jordan outer measure equals the infimum of sums of box volumes over all finite box covers.
theorem Jordan_outer_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_outer_measure E = sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) := by
  -- Strategy: Show equality via two inequalities (le_antisymm)
  apply le_antisymm

  -- Part 1 (≤): Jordan_outer_measure E ≤ sInf of box covers
  · -- For any box cover S, show Jordan_outer_measure E ≤ S.sum volume, then take infimum
    apply le_csInf
    -- Show the set of box cover sums is nonempty
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      use ∑ B ∈ T, |B|ᵥ
      use T
      simp
      intro a ha
      have : a ∈ A := hE_sub_A ha
      rw [hA_eq] at this
      exact this
    -- Show Jordan_outer_measure E is a lower bound for all box cover sums
    · intro m hm
      obtain ⟨S, hS_cover, rfl⟩ := hm
      -- The union ⋃ B ∈ S is elementary
      classical
      -- Map S : Finset (Box d) to a finset of sets
      let S_sets : Finset (Set (EuclideanSpace' d)) := S.image (fun B => B.toSet)
      have hS_elem : ∀ E ∈ S_sets, IsElementary E := by
        intro E hE
        simp [S_sets] at hE
        obtain ⟨B, _, rfl⟩ := hE
        exact IsElementary.box B
      -- Apply IsElementary.union' to show the union is elementary
      have h_union_eq : ⋃ E ∈ S_sets, E = ⋃ B ∈ S, B.toSet := by simp [S_sets]
      have hA_elem : IsElementary (⋃ B ∈ S, B.toSet) := by
        rw [←h_union_eq]
        exact IsElementary.union' hS_elem
      -- E ⊆ ⋃ B ∈ S, so Jordan_outer_measure E ≤ hA_elem.measure
      have h_outer_le : Jordan_outer_measure E ≤ hA_elem.measure := by
        unfold Jordan_outer_measure
        apply csInf_le
        · use 0; intro m' hm'; obtain ⟨_, hB, _, rfl⟩ := hm'; exact IsElementary.measure_nonneg hB
        · use ⋃ B ∈ S, B.toSet, hA_elem, hS_cover
      -- hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ by subadditivity (IsElementary.measure_of_union')
      have h_sub : hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ := by
        -- Apply IsElementary.measure_of_union' to get subadditivity
        have h1 := IsElementary.measure_of_union' hS_elem
        -- Show hA_elem.measure = (IsElementary.union' hS_elem).measure
        have h_eq : hA_elem.measure = (IsElementary.union' hS_elem).measure := by
          apply IsElementary.measure_eq_of_set_eq
          exact h_union_eq.symm
        -- Convert the sum over S_sets to sum over S
        -- Technical lemma: sum reindexing via Finset.sum_attach and Finset.sum_image
        have h2 : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ B ∈ S, |B|ᵥ := by
          -- Define a helper function to detach measure from proof
          let vol (E : Set (EuclideanSpace' d)) := if h : IsElementary E then h.measure else 0

          -- 1. Show RHS equals sum over S'
          let S' := S.filter (fun B => B.toSet.Nonempty)
          have h_rhs : ∑ B ∈ S, |B|ᵥ = ∑ B ∈ S', |B|ᵥ := by
             rw [←Finset.sum_filter_add_sum_filter_not S (fun B => B.toSet.Nonempty) (fun B => |B|ᵥ)]
             suffices ∑ B ∈ S.filter (fun B => ¬B.toSet.Nonempty), |B|ᵥ = 0 by simp [this, S']
             apply Finset.sum_eq_zero
             intro B hB
             rw [Finset.mem_filter] at hB
             exact Box.volume_eq_zero_of_empty B (Set.not_nonempty_iff_eq_empty.mp hB.2)
          rw [h_rhs]

          -- 2. Simplify LHS to use vol and sum over sets
          have h_lhs : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E ∈ S_sets, vol E := by
            -- Congruence to vol
            have h_congr : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E : S_sets, vol E.val := by
              apply Finset.sum_congr rfl
              intro E _
              dsimp [vol]
              rw [dif_pos (hS_elem E.val E.property)]
            rw [h_congr]
            -- Subtype sum to set sum
            change ∑ E ∈ S_sets.attach, vol E.val = ∑ E ∈ S_sets, vol E
            rw [Finset.sum_attach S_sets]
          rw [h_lhs]

          -- 3. Restrict set sum to non-empty sets
          let S_sets' := S'.image Box.toSet
          have h_subset : S_sets' ⊆ S_sets := Finset.image_subset_image (Finset.filter_subset _ _)

          have h_sets_eq : ∑ E ∈ S_sets, vol E = ∑ E ∈ S_sets', vol E := by
             rw [←Finset.sum_sdiff h_subset]
             suffices ∑ E ∈ S_sets \ S_sets', vol E = 0 by simp [this]
             apply Finset.sum_eq_zero
             intro E hE
             rw [Finset.mem_sdiff] at hE
             have hE_empty : E = ∅ := by
               obtain ⟨h_in, h_notin⟩ := hE
               rw [Finset.mem_image] at h_in
               obtain ⟨B, hB, rfl⟩ := h_in
               by_contra h_non
               apply h_notin
               simp [S_sets', S']
               use B
               simp [hB]
               rw [Set.nonempty_iff_ne_empty]
               exact h_non
             dsimp [vol]
             rw [hE_empty]
             rw [dif_pos (IsElementary.empty d)]
             exact IsElementary.measure_of_empty d
          rw [h_sets_eq]

          -- 4. Use sum_image
          rw [Finset.sum_image]
          · -- Match terms
            apply Finset.sum_congr rfl
            intro B hB
            dsimp [vol]
            rw [dif_pos (IsElementary.box B)]
            exact IsElementary.measure_of_box B
          · -- Injectivity
            intro B₁ hB₁ B₂ hB₂ h_eq
            simp [S'] at hB₁ hB₂
            -- Use helper lemma: Box.toSet is injective for non-empty boxes
            exact Box.toSet_injective_of_nonempty hB₁.2 hB₂.2 h_eq
        calc hA_elem.measure
          _ = (IsElementary.union' hS_elem).measure := h_eq
          _ ≤ ∑ E : S_sets, (hS_elem E.val E.property).measure := h1
          _ = ∑ B ∈ S, |B|ᵥ := h2
      linarith

  -- Part 2 (≥): sInf of box covers ≤ Jordan_outer_measure E
  · -- For any elementary A ⊇ E, show sInf(box covers) ≤ hA.measure
    unfold Jordan_outer_measure
    apply le_csInf
    -- Show the set of elementary cover measures is nonempty
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      use hA.measure
      use A, hA, hE_sub_A
    -- Show sInf(box covers) is a lower bound for all elementary cover measures
    · intro m hm
      obtain ⟨A, hA, hE_sub_A, rfl⟩ := hm
      -- Get partition T of A
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      -- T is a box cover: E ⊆ A = ⋃ B ∈ T
      have hT_cover : E ⊆ ⋃ B ∈ T, B.toSet := hA_eq ▸ hE_sub_A
      -- T.sum volume = hA.measure
      have hT_sum : ∑ B ∈ T, |B|ᵥ = hA.measure := by
        symm; exact hA.measure_eq hT_disj hA_eq
      -- sInf(box covers) ≤ ∑ B ∈ T, |B|ᵥ (since T is a box cover)
      have h_inf_le : sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) ≤ ∑ B ∈ T, |B|ᵥ := by
        apply csInf_le
        -- Show box covers set is bounded below
        · use 0
          intro m' hm'
          obtain ⟨S, _, rfl⟩ := hm'
          apply Finset.sum_nonneg
          intro B _
          rw [Box.volume]
          apply Finset.prod_nonneg
          intro i _
          rw [BoundedInterval.length]
          exact le_max_right _ _
        -- ∑ B ∈ T, |B|ᵥ is in the box covers set
        · show ∑ B ∈ T, |B|ᵥ ∈ (fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}
          simp
          exact ⟨T, hT_cover, rfl⟩
      -- Combine: sInf(box covers) ≤ ∑ B ∈ T, |B|ᵥ = hA.measure
      rw [←hT_sum]; exact h_inf_le

/-- This definition deviates from the text by working with countable families of boxes rather than boxes indexed by the natural numbers.  This becomes important in dimension zero, when all boxes are non-empty. -/
noncomputable def Lebesgue_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal :=
  sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }

/-- When d > 0, the Lebesgue outer measure can be computed using ℕ-indexed box sequences,
    which is equivalent to the definition using countable families. This is because we can
    pad any countable family with zero-volume boxes (which exist when d > 0). -/
lemma Lebesgue_outer_measure_eq_nat_indexed {d:ℕ} (hd: 0 < d) (E: Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure E =
    sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }) := by
  unfold Lebesgue_outer_measure
  -- Strategy: Show both ≤ directions
  -- (≤): Any ℕ-indexed cover is a countable cover with X = Set.univ
  -- (≥): For any countable cover (X, S), construct ℕ-indexed S' by:
  --      - Use the equivalence Set.univ ≃ ℕ to reindex
  --      - Show sums are equal via Equiv.tsum_eq
  apply le_antisymm

  -- Part 1 (≤): ℕ-indexed covers ≥ countable covers
  · apply le_sInf
    intro b hb
    obtain ⟨S, hS_cover, rfl⟩ := hb
    -- Show ∑' n, (S n).volume.toEReal is in the countable covers set
    apply sInf_le
    show ∑' n, (S n).volume.toEReal ∈ { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
    -- Convert S : ℕ → Box d to S' : Set.univ → Box d
    let S' : Set.univ → Box d := fun n => S n.val
    use Set.univ, S'
    constructor
    · -- Covering property: E ⊆ ⋃ n : Set.univ, (S' n).toSet
      have : (⋃ n : Set.univ, (S' n).toSet) = (⋃ n, (S n).toSet) := by
        ext x
        simp [S']
      rw [this]
      exact hS_cover
    · -- Sum equality: ∑' (n : Set.univ), (S' n).volume.toEReal = ∑' n, (S n).volume.toEReal
      -- Strategy: Use Equiv.tsum_eq to reindex from Set.univ to ℕ
      simp only [S']
      -- The equivalence Equiv.Set.univ : Set.univ ≃ ℕ allows us to reindex the sum
      -- We want: ∑' (n : Set.univ), f(n.val) = ∑' (n : ℕ), f(n)
      -- Equiv.tsum_eq gives: ∑' (c : Set.univ), f(e c) = ∑' (b : ℕ), f b
      -- We need to apply it backwards (using symm)
      exact ((Equiv.Set.univ ℕ).tsum_eq (fun n => (S n).volume.toEReal)).symm

  -- Part 2 (≥): Countable covers ≥ ℕ-indexed covers
  · apply le_sInf
    intro b hb
    simp only [Set.mem_setOf_eq] at hb
    obtain ⟨X, S, hS_cover, hb_eq⟩ := hb
    open Classical in

    -- Construct zero-volume box (exists when d > 0)
    have ⟨B₀, hB₀⟩ : ∃ B : Box d, B.volume = 0 := by
      -- When d > 0, we can construct a box with empty interval in first dimension
      use ⟨fun i => BoundedInterval.Ioc 0 0⟩
      simp only [Box.volume, BoundedInterval.length]
      -- The product ∏ i : Fin d, max (0 - 0) 0 = ∏ i : Fin d, 0
      conv_lhs => arg 2; ext i; rw [sub_self, max_eq_right (le_refl 0)]
      -- Now we have ∏ i : Fin d, 0 = 0^d (since d > 0, this is 0)
      rw [Finset.prod_const]
      rw [show Finset.univ.card = d from Fintype.card_fin d]
      exact zero_pow (Nat.pos_iff_ne_zero.mp hd)

    -- Extend S : X → Box d to S' : ℕ → Box d by using B₀ for indices not in X
    let S' : ℕ → Box d := fun n => if h : n ∈ X then S ⟨n, h⟩ else B₀

    -- Show S' is a valid cover
    have hS'_cover : E ⊆ ⋃ n, (S' n).toSet := by
      intro x hx
      have := hS_cover hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨⟨n, hn⟩, hxn⟩ := this
      use n
      -- At index n, we have n ∈ X, so S' n = S ⟨n, hn⟩
      have : S' n = S ⟨n, hn⟩ := by simp [S', hn]
      rw [this]
      exact hxn

    -- Show sums are equal
    have h_sum : ∑' n, (S' n).volume.toEReal = ∑' (n : X), (S n).volume.toEReal := by
      -- Strategy: Rewrite S' using if-then-else, then show terms outside X contribute 0
      -- Use tsum_congr to match terms inside X with the subtype sum

      -- Step 1: Express the LHS explicitly showing the if-then-else
      have h_S'_eq : ∀ n, (S' n).volume.toEReal =
          if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else (B₀.volume : EReal) := by
        intro n
        simp only [S']
        split_ifs <;> rfl

      simp_rw [h_S'_eq, hB₀]
      simp only [EReal.coe_zero]

      -- Step 2: The sum ∑' n, (if n ∈ X then f n else 0) = ∑' (n : X), f n
      -- This is the key equality relating the full sum to the subtype sum
      -- Strategy: Show both sums enumerate the same terms via subtype coercion

      -- Both sides sum over the same elements: for each n ∈ X, we add (S n).volume
      -- The LHS uses characteristic function; RHS uses subtype indexing
      -- This is a standard reindexing via the subtype embedding coe : X → ℕ

      -- Show the functions match when properly aligned
      have h_fn_eq : ∀ (x : X), (if h : ↑x ∈ X then (S ⟨↑x, h⟩).volume.toEReal else (0 : EReal)) =
                                 (S x).volume.toEReal := by
        intro ⟨n, hn⟩
        simp only [hn, dite_true]

      -- Now we need: ∑' n : ℕ, (if h : n ∈ X then ... else 0) = ∑' x : X, f x
      -- This is a standard measure theory fact: summing with characteristic function
      -- equals summing over the subtype. Both sums enumerate exactly the same terms

      -- Define g to make the terms clearer
      let g : ℕ → EReal := fun n => if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else 0

      -- 1. Show LHS equals sum of g
      have h1 : (∑' n, if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else 0) = ∑' n, g n := rfl

      -- 2. Use tsum_subtype to relate sum over ℕ to sum over X
      have h2 : ∑' n, g n = ∑' (x : X), g x := by
        -- Use classical logic for if-then-else
        classical
        -- tsum_subtype gives: ∑' x:X, f x = ∑' n, if n ∈ X then f n else 0
        -- We rewrite the RHS (sum over X) to sum over ℕ with if-then-else
        rw [tsum_subtype (f := g)]
        -- Now we match the sums term by term
        apply tsum_congr
        intro n
        -- g n is defined exactly to be 0 outside X, matching the if-then-else
        rw [Set.indicator_apply]
        split_ifs with h
        · rfl
        · simp [g, h]

      -- 3. Show g restricted to X equals the RHS term
      have h3 : ∑' (x : X), g x = ∑' (x : X), (S x).volume.toEReal := by
        apply tsum_congr
        intro x
        -- For x ∈ X, g x simplifies to S x.volume
        simp [g, x.property]

      -- Combine steps
      rw [h1, h2, h3]

    -- Apply sInf_le
    calc sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet })
        ≤ ∑' n, (S' n).volume.toEReal := by
            apply sInf_le
            use S', hS'_cover
        _ = ∑' (n : X), (S n).volume.toEReal := h_sum
        _ = b := hb_eq.symm

open Classical in
/-- Helper lemma: If X is an infinite subset of ℕ, then the sum of its indicator function
    (mapping elements of X to 1 and others to 0) diverges to ⊤ in EReal. -/
lemma hasSum_indicator_top_of_infinite (X : Set ℕ) (hX : ¬X.Finite) :
    HasSum (fun n => if n ∈ X then (1 : EReal) else 0) ⊤ := by
  -- Strategy: Show that finite sums grow unboundedly.
  -- For any n, we can find n elements in X (since X is infinite),
  -- so there exists a finite sum ≥ n. This proves convergence to ⊤.

  unfold HasSum
  rw [EReal.tendsto_nhds_top_iff_real]
  intro r

  -- For any real bound r, we need to show eventually sums exceed r
  -- Choose n > r (using ceiling), then find n elements in X
  obtain ⟨n, hn⟩ := exists_nat_gt r

  -- Since X is infinite, we can extract a finite subset with exactly n elements
  have hX_inf : X.Infinite := hX
  obtain ⟨F, hF_sub, hF_card⟩ := Set.Infinite.exists_subset_card_eq hX_inf n

  -- Show that eventually (in the atTop filter), finite sums are ≥ n
  apply Filter.eventually_atTop.mpr
  use F
  intro s hFs

  -- For any finset s containing F, we have ∑ i ∈ s, (indicator) ≥ n
  calc (r : EReal) < (n : EReal) := EReal.coe_lt_coe_iff.mpr hn
       _ = ↑F.card := by rw [hF_card]
       _ = ∑ i ∈ F, (1 : EReal) := by
           rw [Finset.sum_const, nsmul_one]
       _ = ∑ i ∈ F, if i ∈ X then (1 : EReal) else 0 := by
           apply Finset.sum_congr rfl
           intro i hi
           rw [if_pos]
           exact hF_sub (Finset.mem_coe.mpr hi)
       _ ≤ ∑ i ∈ s, if i ∈ X then (1 : EReal) else 0 := by
           apply Finset.sum_le_sum_of_subset_of_nonneg hFs
           intro i _ _
           split_ifs <;> norm_num

open Classical in
/-- In dimension 0, the Lebesgue outer measure is 1 for non-empty sets and 0 for the empty set.
    This is because all boxes in dimension 0 are singletons with volume 1 (empty product). -/
lemma Lebesgue_outer_measure_of_dim_zero {E: Set (EuclideanSpace' 0)} :
    Lebesgue_outer_measure E = if E.Nonempty then 1 else 0 := by
  unfold Lebesgue_outer_measure

  -- First prove: all boxes in dimension 0 have volume 1 (empty product)
  have h_box_vol : ∀ B : Box 0, B.volume = 1 := by
    intro B
    unfold Box.volume
    -- Fin 0 is empty, so Finset.univ is empty, and empty product = 1
    have : Finset.univ = (∅ : Finset (Fin 0)) := by
      ext i
      exact Fin.elim0 i
    rw [this]
    rfl

  by_cases hE : E.Nonempty

  -- Case 1: E is nonempty → measure = 1
  · simp only [hE, ↓reduceIte]
    apply le_antisymm

    -- Upper bound: show sInf ≤ 1 by exhibiting a cover with sum = 1
    · apply sInf_le
      -- Construct a cover using a singleton set {0}
      let X : Set ℕ := {0}
      let B₀ : Box 0 := ⟨fun i => Fin.elim0 i⟩
      let S : X → Box 0 := fun _ => B₀
      use X, S
      constructor
      · -- Show E ⊆ ⋃ n, (S n).toSet
        intro x _
        simp only [Set.mem_iUnion]
        use ⟨0, Set.mem_singleton 0⟩
        -- All points in EuclideanSpace' 0 are in any box
        unfold Box.toSet
        intro i
        exact Fin.elim0 i
      · -- Show V = ∑' n, (S n).volume.toEReal = 1
        -- S maps every element of X = {0} to B₀, which has volume 1
        have h_vol_eq : ∀ (n : X), (S n).volume.toEReal = (1 : EReal) := by
          intro n
          simp only [S, h_box_vol, EReal.coe_one]
        simp_rw [h_vol_eq]
        -- ∑' (_ : {0}), (1 : EReal) = 1 using tsum over finite type
        rw [tsum_fintype]
        -- Now we have ∑ x ∈ Finset.univ, (1 : EReal) where Finset.univ has card 1
        simp only [Finset.sum_const]
        -- Show Finset.univ.card • 1 = 1 by showing card = 1
        have h_card : Fintype.card X = 1 := Set.card_singleton 0
        simp only [Fintype.card] at h_card
        rw [h_card]
        norm_num

    -- Lower bound: show 1 ≤ sInf (every cover has sum ≥ 1)
    · apply le_sInf
      intro b hb
      simp only [Set.mem_setOf_eq] at hb
      obtain ⟨X, S, hcover, hb_eq⟩ := hb
      -- E is nonempty, so the cover must be nonempty
      have hX_nonempty : X.Nonempty := by
        obtain ⟨x, hx⟩ := hE
        have := hcover hx
        simp only [Set.mem_iUnion] at this
        obtain ⟨⟨n, hn⟩, _⟩ := this
        exact ⟨n, hn⟩
      rw [hb_eq]
      -- Sum of volumes (each = 1) over nonempty set X
      have : ∀ (n : X), (S n).volume.toEReal = (1 : EReal) := by
        intro n
        simp [h_box_vol]
      simp_rw [this]
      -- Need: ∑' (_ : X), (1 : EReal) ≥ 1 when X.Nonempty
      -- Pick an element n₀ from X and show the sum includes at least that term
      obtain ⟨n₀, hn₀⟩ := hX_nonempty
      -- Convert sum over subtype to sum over ℕ with indicator
      classical
      let g : ℕ → EReal := fun n => if h : n ∈ X then (1 : EReal) else (0 : EReal)
      have h1 : ∑' (n : ↑X), (1 : EReal) = ∑' n : ℕ, g n := by
        -- Use tsum_subtype: ∑' (x : X), f x = ∑' n, X.indicator f n
        rw [tsum_subtype (f := fun n => (1 : EReal))]
        apply tsum_congr
        intro n
        -- Show X.indicator (fun n => 1) n = g n
        simp [g, Set.indicator_apply]
      rw [h1]
      -- First show all terms are nonnegative
      have h_nonneg : ∀ n, (0 : EReal) ≤ g n := by
        intro n
        simp [g]
        split_ifs
        · exact EReal.coe_nonneg.mpr (by norm_num)
        · exact EReal.coe_nonneg.mpr (by norm_num)
      -- Show that g n₀ = 1
      have h_gn0 : g n₀ = (1 : EReal) := by
        simp [g, hn₀]
      -- The key: use that for summable nonnegative functions, any term is ≤ the sum
      -- Since g is nonnegative and summable (it's an indicator function with values 0 or 1),
      -- we have g n₀ ≤ ∑' n, g n
      -- For EReal, construct this using HasSum properties
      have h_le : g n₀ ≤ ∑' n : ℕ, g n := by
        -- Use that tsum is the supremum of finite sums
        -- Since {n₀} is a finite subset, ∑ n ∈ {n₀}, g n ≤ ∑' n, g n
        -- And ∑ n ∈ {n₀}, g n = g n₀ = 1
        have h_single : ∑ n ∈ ({n₀} : Finset ℕ), g n = g n₀ := by
          simp [Finset.sum_singleton]
        have : HasSum g (∑' n : ℕ, g n) := by
          by_cases hX : X.Finite
          · -- Case 1: X is finite
            have h_supp : g.support.Finite := by
              dsimp [g, Function.support]
              apply Set.Finite.subset hX
              intro n h
              simp at h
              exact h
            exact (summable_of_finite_support h_supp).hasSum
          · -- Case 2: X is infinite
            -- The sum is Top. We prove HasSum g Top.
            have h_top : HasSum g ⊤ := by
              -- Apply helper lemma: infinite indicator sum diverges to ⊤
              -- g and the lemma function are definitionally equal under classical
              convert hasSum_indicator_top_of_infinite X hX using 2
            exact h_top.tsum_eq.symm ▸ h_top
        -- If HasSum g s, then for any finite set F, ∑ n ∈ F, g n ≤ s
        -- Apply this with F = {n₀}
        have h_fin_le : ∑ n ∈ ({n₀} : Finset ℕ), g n ≤ ∑' n : ℕ, g n := by
          rw [Finset.sum_singleton]
          -- Since g is nonnegative, g n₀ ≤ sum over any superset containing n₀
          -- In particular, g n₀ ≤ ∑' n, g n
          trans (∑ n ∈ Finset.range (n₀ + 1), g n)
          · apply Finset.single_le_sum (fun i _ => h_nonneg i)
            simp
          · -- Now show ∑ n ∈ range (n₀+1), g n ≤ tsum
            apply sum_le_hasSum (Finset.range (n₀ + 1))
            · intro i _; exact h_nonneg i
            · exact this
        rw [h_single] at h_fin_le
        exact h_fin_le
      rw [h_gn0] at h_le
      exact h_le

  -- Case 2: E is empty → measure = 0
  · simp only [hE, ↓reduceIte]
    apply le_antisymm

    -- Upper bound: show sInf ≤ 0 by exhibiting a cover with sum = 0
    · apply sInf_le
      -- Empty cover: X = ∅
      let X : Set ℕ := ∅
      use X
      -- Need to provide S : X → Box 0, but X is empty so use elim
      refine ⟨fun x => absurd x.2 (Set.notMem_empty x.1), ?_, ?_⟩
      · -- Empty set is covered by empty cover
        intro x hx
        simp only [Set.not_nonempty_iff_eq_empty] at hE
        exact absurd hx (hE ▸ Set.notMem_empty x)
      · -- Sum over empty set = 0
        simp

    -- Lower bound: 0 ≤ sInf (all EReal sums are ≥ 0 when summing volumes)
    · apply le_sInf
      intro b hb
      simp only [Set.mem_setOf_eq] at hb
      obtain ⟨X, S, _, hb_eq⟩ := hb
      rw [hb_eq]
      -- Sum of nonnegative volumes is ≥ 0
      apply tsum_nonneg
      intro n
      apply EReal.coe_nonneg.mpr
      -- Box volume is a product of nonnegative lengths
      unfold Box.volume
      apply Finset.prod_nonneg
      intro i _
      unfold BoundedInterval.length
      exact le_max_right _ _

/-- Coercion ℝ → EReal preserves infimums for nonempty bounded-below sets -/
lemma EReal.sInf_image_coe {s : Set ℝ} (hs : s.Nonempty) (h_bdd : BddBelow s) :
    sInf ((fun x : ℝ => (x : EReal)) '' s) = ↑(sInf s) := by
  -- Strategy: Show both ≤ directions using sInf properties
  apply le_antisymm

  -- Part 1: sInf(↑''s) ≤ ↑(sInf s)
  · -- Key: sInf(↑''s) is a lower bound for ↑''s, so sInf(↑''s) ≤ ↑x for all x ∈ s
    -- We want to show this implies sInf(↑''s) ≤ ↑(sInf s)
    -- Case analysis on whether sInf(↑''s) is ⊥ or a real
    by_cases h_bot : sInf ((fun y : ℝ => (y : EReal)) '' s) = ⊥
    · rw [h_bot]; exact bot_le
    · -- sInf(↑''s) is bounded below (since s is), so it's not ⊥ or ⊤
      -- We have: ∀ x ∈ s, sInf(↑''s) ≤ ↑x
      have h_le_all : ∀ x ∈ s, sInf ((fun y : ℝ => (y : EReal)) '' s) ≤ ↑x := by
        intro x hx; apply sInf_le; exact ⟨x, hx, rfl⟩
      -- Since s is bounded below, there exists m such that m ≤ x for all x ∈ s
      -- This means ↑m is a lower bound for ↑''s, so ↑m ≤ sInf(↑''s)
      -- Combined with sInf(↑''s) ≤ ↑x for all x, we get that sInf(↑''s) is in [↑m, ↑x₀]
      -- where x₀ ∈ s, hence sInf(↑''s) must be a casted real
      -- Then we can extract r := (sInf(↑''s)).toReal and show r ≤ sInf s
      obtain ⟨m, hm⟩ := h_bdd
      have h_bdd_below : (m : EReal) ≤ sInf ((fun y : ℝ => (y : EReal)) '' s) := by
        apply le_sInf
        intro b hb
        obtain ⟨x, hx, rfl⟩ := hb
        exact EReal.coe_le_coe_iff.mpr (hm hx)
      -- Now sInf(↑''s) ∈ [↑m, ↑x₀], so it's a casted real
      -- We want: sInf(↑''s) ≤ ↑(sInf s)
      -- Strategy: Show sInf(↑''s) ≤ ↑x for all x ∈ s, then take inf over x
      -- Apply le_csInf: to show a ≤ sInf s, prove a is a lower bound for s
      obtain ⟨x₀, hx₀⟩ := hs
      have h_le_x0 : sInf ((fun y : ℝ => (y : EReal)) '' s) ≤ ↑x₀ := h_le_all x₀ hx₀
      -- sInf(↑''s) is in [↑m, ↑x₀], so it must be a casted real
      have h_exists_r : ∃ r : ℝ, sInf ((fun y : ℝ => (y : EReal)) '' s) = ↑r := by
        -- Use that sInf(↑''s) is bounded: ↑m ≤ sInf(↑''s) ≤ ↑x₀
        -- If sInf(↑''s) = ⊤, then ↑x₀ ≥ ⊤, contradicting that x₀ is real
        by_cases h_top : sInf ((fun y : ℝ => (y : EReal)) '' s) = ⊤
        · -- Get contradiction: ↑x₀ ≥ ⊤
          have : (x₀ : EReal) ≥ ⊤ := by rw [←h_top]; exact h_le_x0
          simp at this
        · -- sInf(↑''s) is not ⊥ (from h_bot) and not ⊤ (from h_top)
          -- So it must be a casted real
          -- Use EReal trichotomy: either ⊥, ⊤, or casted real
          have h_cases := EReal.def (sInf ((fun y : ℝ => (y : EReal)) '' s))
          cases h_cases with
          | inl h => obtain ⟨r, hr⟩ := h; exact ⟨r, hr.symm⟩
          | inr h => cases h with
            | inl h_eq_top => exact absurd h_eq_top h_top
            | inr h_eq_bot => exact absurd h_eq_bot h_bot
      obtain ⟨r, hr⟩ := h_exists_r
      rw [hr]
      -- Now show: ↑r ≤ ↑(sInf s), i.e., r ≤ sInf s
      apply EReal.coe_le_coe_iff.mpr
      -- Show r ≤ sInf s by showing r is a lower bound for s
      have hs' : s.Nonempty := ⟨x₀, hx₀⟩
      apply le_csInf hs'
      intro x hx
      -- Show r ≤ x for all x ∈ s
      -- We have ↑r = sInf(↑''s) ≤ ↑x
      have : (r : EReal) ≤ ↑x := by rw [←hr]; exact h_le_all x hx
      exact EReal.coe_le_coe_iff.mp this

  -- Part 2: ↑(sInf s) ≤ sInf(↑''s)
  -- Show that ↑(sInf s) is a lower bound for ↑''s
  · apply le_sInf
    intro b hb
    obtain ⟨x, hx_in_s, rfl⟩ := hb
    -- Show: ↑(sInf s) ≤ ↑x
    apply EReal.coe_le_coe_iff.mpr
    -- Show: sInf s ≤ x (true since x ∈ s and sInf s is a lower bound)
    exact csInf_le h_bdd hx_in_s

/-- When enumerating a finset to a sequence padded with empty boxes,
    the infinite sum of volumes equals the finite sum -/
lemma tsum_volume_finset_eq {d : ℕ} (hd : 0 < d) (S : Finset (Box d)) :
    let S_list := S.toList
    let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
    let S_seq : ℕ → Box d := fun n =>
      if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box
    ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal := by
  -- Strategy: zero_box has volume 0 (first side is empty), so tsum = sum over finite range
  -- Then relate finite range sum to finset sum via list enumeration
  intro S_list zero_box S_seq

  -- Step 1: Show zero_box has volume 0
  have h_zero_vol : |zero_box|ᵥ = 0 := by
    unfold Box.volume zero_box
    simp only
    -- The first side (index 0) is empty, so product is 0
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d))
    simp only [ite_true]
    simp [BoundedInterval.length]

  -- Step 2: Use tsum_eq_sum to convert infinite sum to finite sum
  have h_tsum_eq : ∑' n, (S_seq n).volume.toEReal = ∑ n ∈ Finset.range S_list.length, (S_seq n).volume.toEReal := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    unfold S_seq
    rw [dif_neg (not_lt_of_ge hn)]
    simp [h_zero_vol]

  -- Step 3: Relate finset.range sum to finset S sum
  rw [h_tsum_eq]
  suffices h : (∑ n ∈ Finset.range S_list.length, (S_seq n).volume) = (∑ B ∈ S, |B|ᵥ) by
    calc ∑ n ∈ Finset.range S_list.length, (S_seq n).volume.toEReal
        = ∑ n ∈ Finset.range S_list.length, ((S_seq n).volume : EReal) := rfl
      _ = (∑ n ∈ Finset.range S_list.length, (S_seq n).volume : ℝ).toEReal := by
        -- Coercion ℝ → EReal commutes with Finset.sum
        -- This follows from EReal.coe_add: (x + y : EReal) = (x : EReal) + (y : EReal)
        -- Prove by induction: empty sum is 0, and for cons, use EReal.coe_add and induction hypothesis
        refine Finset.cons_induction (by simp) ?_ (Finset.range S_list.length)
        intro a s ha ih
        rw [Finset.sum_cons ha]
        conv_rhs => rw [Finset.sum_cons ha, EReal.coe_add]
        -- Now: ↑(S_seq a).volume + ∑ x ∈ s, ↑(S_seq x).volume = ↑(S_seq a).volume + ↑(∑ x ∈ s, (S_seq x).volume)
        -- Use ih: ∑ x ∈ s, ↑(S_seq x).volume = ↑(∑ x ∈ s, (S_seq x).volume)
        rw [ih]
      _ = (∑ B ∈ S, |B|ᵥ).toEReal := by rw [h]

  -- Prove: ∑ n ∈ Finset.range S_list.length, (S_seq n).volume = ∑ B ∈ S, |B|ᵥ
  -- Use Finset.sum_bij to establish bijection between indices and finset elements
  -- sum_bij: (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, g (i a) = f a)
  --          (hg : ∀ b ∈ t, ∃ a ∈ s, i a = b) (hh : ∀ a₁ a₂ ∈ s, i a₁ = i a₂ → a₁ = a₂)
  refine Finset.sum_bij (fun n hn => S_list.get ⟨n, Finset.mem_range.mp hn⟩) ?_ ?_ ?_ ?_
  · -- hi: Image is in S
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    have : S_list.get ⟨n, hn_lt⟩ ∈ S_list := List.get_mem S_list ⟨n, hn_lt⟩
    exact Finset.mem_toList.mp this
  · -- i_inj: Injectivity
    intro n₁ hn₁ n₂ hn₂ heq
    have hn₁_lt := Finset.mem_range.mp hn₁
    have hn₂_lt := Finset.mem_range.mp hn₂
    -- List.get is injective when the list has no duplicates (which holds for Finset.toList)
    -- From heq: S_list[n₁] = S_list[n₂], and S_list.Nodup, deduce n₁ = n₂
    have h_nodup : S_list.Nodup := Finset.nodup_toList S
    -- Simplify heq to get S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩
    have h_get_eq : S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩ := by
      simp at heq
      exact heq
    -- Use nodup to show the indices are equal
    -- List.nodup_iff_injective_get: Nodup l ↔ Function.Injective l.get
    have h_inj : Function.Injective S_list.get := List.nodup_iff_injective_get.mp h_nodup
    -- Apply injectivity: S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩ implies ⟨n₁, hn₁_lt⟩ = ⟨n₂, hn₂_lt⟩
    have h_idx_eq : (⟨n₁, hn₁_lt⟩ : Fin S_list.length) = ⟨n₂, hn₂_lt⟩ := h_inj h_get_eq
    exact congrArg Fin.val h_idx_eq
  · -- i_surj: Surjectivity
    intro b hb
    obtain ⟨i, hi⟩ := List.get_of_mem (Finset.mem_toList.mpr hb)
    -- hi : S.toList.get i = b, and S_list = S.toList, so S_list.get i = b
    -- We need to show (fun n hn ↦ S_list.get ⟨n, ⋯⟩) i.val ... = b
    -- Since i : Fin S_list.length, we have S_list.get ⟨i.val, i.isLt⟩ = S_list.get i = b
    have h_eq : (fun n hn => S_list.get ⟨n, Finset.mem_range.mp hn⟩) i.val (Finset.mem_range.mpr i.isLt) = b := by
      simp
      -- S_list = S.toList, so S_list.get i = S.toList.get i = b
      rw [←hi]
      rfl
    exact ⟨i.val, Finset.mem_range.mpr i.isLt, h_eq⟩
  · -- h: Function preserves summand
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    simp only [S_seq, dif_pos hn_lt]


-- For any bounded set, the Lebesgue outer measure is at most the Jordan outer measure.
theorem Lebesgue_outer_measure_le_Jordan {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Lebesgue_outer_measure E ≤ Jordan_outer_measure E := by
  -- Strategy: Handle d = 0 separately using Lebesgue_outer_measure_of_dim_zero. For d > 0:
  -- Express Jordan outer measure as infimum over finite covers via Jordan_outer_eq.
  -- Show Lebesgue outer measure (infimum over countable covers) ≤ Jordan by proving
  -- Lebesgue ≤ each finite cover sum: convert finite cover S to countable sequence S_seq
  -- (enumerate via toList, pad with zeros), show S_seq is a countable cover with same sum,
  -- then apply infimum properties to conclude Lebesgue ≤ Jordan.

  by_cases hd : d = 0
  · subst hd
    -- Use the characterization of Lebesgue_outer_measure for d = 0
    rw [Lebesgue_outer_measure_of_dim_zero]
    by_cases hE_ne : E.Nonempty
    · -- Case: E is nonempty, so Lebesgue_outer_measure E = 1
      simp only [hE_ne, ↓reduceIte]
      -- Need to show (1 : EReal) ≤ ↑(Jordan_outer_measure E)
      -- Any elementary set containing nonempty E must be nonempty, hence has measure ≥ 1
      have h : (1 : ℝ) ≤ Jordan_outer_measure E := by
        unfold Jordan_outer_measure
        apply le_csInf
        · -- Show the set is nonempty
          obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
          exact ⟨hA.measure, A, hA, hE_sub_A, rfl⟩
        · -- Show 1 is a lower bound for all measures in the set
          intro m hm
          obtain ⟨A, hA, hE_sub_A, rfl⟩ := hm
          -- A contains E, which is nonempty, so A is nonempty
          have hA_ne : A.Nonempty := hE_ne.mono hE_sub_A
          -- In dimension 0, any nonempty elementary set has measure ≥ 1
          -- This is because elementary sets are finite unions of boxes, and each box has volume 1
          obtain ⟨S, hS_disj, hA_eq⟩ := hA.partition
          -- Find a nonempty box in the partition
          have : ∃ B ∈ S, B.toSet.Nonempty := by
            by_contra h
            push_neg at h
            -- h says: ∀ B, B ∈ S → B.toSet = ∅
            have hA_empty : A = ∅ := by
              rw [hA_eq]
              ext x
              simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
              intro ⟨B, hB, hx⟩
              rw [h B hB] at hx
              exact hx
            exact Set.Nonempty.ne_empty hA_ne hA_empty
          obtain ⟨B, hB_in_S, hB_ne⟩ := this
          -- All boxes in dimension 0 have volume 1
          have h_vol : |B|ᵥ = 1 := by
            unfold Box.volume
            have : Finset.univ = (∅ : Finset (Fin 0)) := by ext i; exact Fin.elim0 i
            rw [this]
            rfl
          -- The measure is the sum of volumes, which includes at least one box with volume 1
          have h_measure : hA.measure = ∑ B' ∈ S, |B'|ᵥ := hA.measure_eq hS_disj hA_eq
          -- Each box has volume ≥ 0 (as a product of nonnegative lengths)
          have h_vol_nonneg : ∀ B' : Box 0, 0 ≤ |B'|ᵥ := by
            intro B'
            unfold Box.volume
            apply Finset.prod_nonneg
            intro i _
            unfold BoundedInterval.length
            exact le_max_right _ _
          -- The sum includes B with volume 1, so the total is ≥ 1
          calc hA.measure
            = ∑ B' ∈ S, |B'|ᵥ := h_measure
            _ ≥ |B|ᵥ := by
                classical
                rw [←Finset.sum_erase_add _ _ hB_in_S]
                simp only [le_add_iff_nonneg_left]
                apply Finset.sum_nonneg
                intro B' _
                exact h_vol_nonneg B'
            _ = 1 := h_vol
      exact EReal.coe_le_coe_iff.mpr h
    · -- Case: E is empty, so Lebesgue_outer_measure E = 0
      simp only [hE_ne, ↓reduceIte]
      -- Need to show (0 : EReal) ≤ ↑(Jordan_outer_measure E), which follows from nonnegativity
      exact EReal.coe_nonneg.mpr (Jordan_outer_measure_nonneg E)

  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd

  -- Rewrite Jordan outer measure using Jordan_outer_eq
  rw [Jordan_outer_eq hE]
  unfold Lebesgue_outer_measure

  -- Show sInf (countable covers) ≤ (finite cover sum : EReal) for all finite covers
  -- This implies sInf (countable) ≤ sInf (finite)
  have h_le : ∀ m ∈ (fun S ↦ (∑ B ∈ S, |B|ᵥ : ℝ)) '' {S | E ⊆ ⋃ B ∈ S, B.toSet},
      sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } ≤ (m : EReal) := by
    intro m hm
    obtain ⟨S, hS_cover, rfl⟩ := hm

    -- Convert finite cover S to countable sequence S_seq
    classical
    let S_list := S.toList
    let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
    have h_card_eq : S_list.length = S.card := Finset.length_toList S
    let S_seq : ℕ → Box d := fun n =>
      if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box

    -- Step 1: Covering is preserved
    have h_cover : E ⊆ ⋃ n, (S_seq n).toSet := by
      intro x hx
      -- Need to show: x ∈ ⋃ n, (S_seq n).toSet, i.e., ∃ n, x ∈ (S_seq n).toSet
      simp only [Set.mem_iUnion]
      -- hS_cover : E ⊆ ⋃ B ∈ S, B.toSet, so x is in some box B ∈ S
      have : x ∈ ⋃ B ∈ S, B.toSet := hS_cover hx
      simp only [Set.mem_iUnion] at this
      obtain ⟨B, hB_in_S, hx_in_B⟩ := this
      -- Since B ∈ S, it appears in S_list at some index
      have hB_in_list : B ∈ S_list := Finset.mem_toList.mpr hB_in_S
      -- Get the index i where S_list contains B
      obtain ⟨i, hi_eq⟩ := List.get_of_mem hB_in_list
      -- Provide i.val as the witness
      use i.val
      -- S_seq i.val = S_list.get ⟨i.val, i.isLt⟩ = B by hi_eq
      simp only [S_seq]
      have hi_val_lt : i.val < S_list.length := i.isLt
      rw [dif_pos hi_val_lt]
      -- Show ⟨i.val, hi_val_lt⟩ = i so we can use hi_eq
      have : (⟨i.val, hi_val_lt⟩ : Fin S_list.length) = i := Fin.ext rfl
      rw [this, hi_eq]
      exact hx_in_B

    -- Step 2: Sum equality via tsum_eq_sum
    have h_sum_eq : ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal := by
      exact tsum_volume_finset_eq hd_pos S

    -- Step 3: Apply infimum property
    calc sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
        ≤ ∑' n, (S_seq n).volume.toEReal := by
            apply sInf_le
            show ∑' n, (S_seq n).volume.toEReal ∈ { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
            use Set.univ, fun (n : Set.univ) => S_seq n.val
            constructor
            · -- Show E ⊆ ⋃ n, (S n).toSet
              convert h_cover using 2
              ext x
              simp
            · -- Show V = ∑' n, (S n).volume.toEReal
              exact ((Equiv.Set.univ ℕ).tsum_eq (fun n => (S_seq n).volume.toEReal)).symm
        _ = (∑ B ∈ S, |B|ᵥ).toEReal := h_sum_eq

  -- Use h_le to show sInf (countable) ≤ sInf (finite)
  -- We have: ∀ m ∈ finite_set, Lebesgue_sInf ≤ ↑m
  -- We need to show: Lebesgue_sInf ≤ ↑(sInf finite_set)
  -- Since finite_set is nonempty and sInf finite_set is the greatest lower bound,
  -- it suffices to show Lebesgue_sInf ≤ ↑m for all m in finite_set
  have h_nonempty : ((fun S ↦ (∑ B ∈ S, |B|ᵥ : ℝ)) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}).Nonempty := by
    obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
    obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
    use (∑ B ∈ T, |B|ᵥ : ℝ)
    use T
    simp
    intro a ha
    have : a ∈ A := hE_sub_A ha
    rw [hA_eq] at this
    exact this
  -- The goal is to show: Lebesgue_sInf ≤ ↑(sInf(finite))
  -- We have h_le showing: ∀ m ∈ finite_set, Lebesgue_sInf ≤ ↑m
  -- Key insight: ↑(sInf finite_set) = sInf (↑ '' finite_set) (monotone coercion preserves sInf)
  -- Then use le_sInf: if a ≤ b for all b ∈ s, then a ≤ sInf s

  -- First, show that sInf(countable) ≤ sInf(↑ '' finite_set)
  have h_le_coe : sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
      ≤ sInf ((fun m : ℝ => (m : EReal)) '' ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := by
    apply le_sInf
    intro b hb
    obtain ⟨m, hm_in, rfl⟩ := hb
    exact h_le m hm_in

  -- Now show that sInf(↑ '' finite_set) = ↑(sInf finite_set) and apply h_le_coe
  -- The set of volumes is bounded below by 0
  have h_bdd : BddBelow ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}) := by
    use 0
    intro m hm
    obtain ⟨S, _, rfl⟩ := hm
    apply Finset.sum_nonneg
    intro B _
    -- Box volume is a product of interval lengths, which are nonnegative by definition
    simp only [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    simp [BoundedInterval.length]

  -- Apply transitivity: Lebesgue_sInf ≤ sInf(↑ '' finite) = ↑(sInf finite)
  calc sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
      ≤ sInf ((fun m : ℝ => (m : EReal)) '' ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := h_le_coe
      _ = ↑(sInf ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := by
          -- Use helper lemma: EReal.sInf_image_coe
          exact EReal.sInf_image_coe h_nonempty h_bdd

/-- Example 1.2.1.  With the junk value conventions of this companion, the Jordan outer measure of the rationals is zero rather than infinite (I think). -/
-- The Jordan outer measure of the rationals in a bounded interval equals the interval length.
example {R:ℝ} (hR: 0 < R) : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ)))) = 2*R := by
  sorry

-- Any countable set (in positive dimension) has Lebesgue outer measure zero.
theorem Countable.Lebesgue_measure {d:ℕ} (hd : 0 < d) {E: Set (EuclideanSpace' d)} (hE: E.Countable) : Lebesgue_outer_measure E = 0 := by
  unfold Lebesgue_outer_measure
  -- Strategy: Cover E with singleton boxes, each with volume 0

  -- Get an enumeration: E ⊆ range f for some f : ℕ → EuclideanSpace' d
  haveI : Nonempty (EuclideanSpace' d) := inferInstance
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hE

  -- Construct singleton box for each f(n)
  let singleton_box : ℕ → Box d := fun n => ⟨fun i => BoundedInterval.Icc (f n i) (f n i)⟩

  -- Show E is covered by these boxes
  have h_cover : E ⊆ ⋃ n, (singleton_box n).toSet := by
    calc E ⊆ Set.range f := hf
       _ ⊆ ⋃ n, (singleton_box n).toSet := by
         intro x hx
         obtain ⟨n, rfl⟩ := hx
         simp [Set.mem_iUnion]
         use n
         unfold Box.toSet
         intro i
         simp [BoundedInterval.toSet]
         exact ⟨le_refl _, le_refl _⟩

  -- Each singleton box has volume 0
  have h_vol : ∀ n, (singleton_box n).volume = 0 := by
    intro n
    exact Box.volume_singleton hd (f n)

  -- Sum of volumes is 0
  have h_sum : ∑' n, (singleton_box n).volume.toEReal = 0 := by
    simp only [h_vol]
    simp [EReal.coe_zero, tsum_zero]

  -- Apply this cover to show the infimum is at most 0
  have h_le : sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } ≤ 0 := by
    apply csInf_le
    · -- Show the set is bounded below by 0
      use 0
      intro V ⟨X, S, _, hV⟩
      rw [hV]
      -- Box volumes are non-negative, so their sum is non-negative
      apply tsum_nonneg
      intro n
      exact EReal.coe_nonneg.mpr (by
        unfold Box.volume
        apply Finset.prod_nonneg
        intro i _
        unfold BoundedInterval.length
        exact le_max_right _ _)
    · -- Show 0 is in the set (via our singleton cover)
      use Set.univ
      use fun (n : Set.univ) => singleton_box n.val
      refine ⟨?_, ?_⟩
      · -- E ⊆ ⋃ n : Set.univ, (singleton_box n.val).toSet
        intro x hx
        simp only [Set.mem_iUnion]
        have : x ∈ ⋃ n, (singleton_box n).toSet := h_cover hx
        simp only [Set.mem_iUnion] at this
        obtain ⟨n, hn⟩ := this
        exact ⟨⟨n, Set.mem_univ n⟩, hn⟩
      · -- ∑' n : Set.univ, (singleton_box n.val).volume.toEReal = 0
        simp only [h_vol, EReal.coe_zero, tsum_zero]

  -- Show the infimum is at least 0
  have h_ge : 0 ≤ sInf { V | ∃ (X : Set ℕ) (S: X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } := by
    apply le_csInf
    · -- Show the set is nonempty (we have the singleton cover)
      use 0
      use Set.univ
      use fun (n : Set.univ) => singleton_box n.val
      exact ⟨h_cover.trans (by intro x; simp only [Set.mem_iUnion]; intro ⟨n, hn⟩; exact ⟨⟨n, Set.mem_univ n⟩, hn⟩), by simp only [h_vol, EReal.coe_zero, tsum_zero]⟩
    · -- Show all elements are ≥ 0
      intro V ⟨X, S, _, hV⟩
      rw [hV]
      apply tsum_nonneg
      intro n
      exact EReal.coe_nonneg.mpr (by
        unfold Box.volume
        apply Finset.prod_nonneg
        intro i _
        unfold BoundedInterval.length
        exact le_max_right _ _)

  exact le_antisymm h_le h_ge

-- The Lebesgue outer measure of the rationals in a bounded interval is zero.
example {R:ℝ} : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ)))) = 0 := by
  apply Countable.Lebesgue_measure (by omega : 0 < 1)
  apply Set.Countable.image
  -- The intersection is countable because the right side is countable
  have : (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ))).Countable := by
    apply Set.Countable.mono (Set.inter_subset_right)
    exact Set.countable_range (fun q:ℚ => (q:ℝ))
  exact this

-- The Lebesgue outer measure of all rationals is zero.
example : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (Set.range (fun q:ℚ ↦ (q:ℝ)))) = 0 := by
  apply Countable.Lebesgue_measure (by omega : 0 < 1)
  apply Set.Countable.image
  exact Set.countable_range (fun q:ℚ => (q:ℝ))

-- A set is Lebesgue measurable if it can be approximated arbitrarily well from the outside by open sets.
def LebesgueMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  ∀ ε > 0, ∃ U: Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε

-- The Lebesgue measure of a set (equals its Lebesgue outer measure).
noncomputable def Lebesgue_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal := Lebesgue_outer_measure E
