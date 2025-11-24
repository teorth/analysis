import Analysis.MeasureTheory.Section_1_1_3
import Mathlib.Topology.Instances.Irrational

/-!
# Introduction to Measure Theory, Section 1.2: Lebesgue measure

A companion to (the introduction to) Section 1.2 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Exercise 1.2.1 (countable union) -/
lemma exercise_1_2_1_union :
    ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n))) ∧
      (∀ n, E n ⊆ Set.Icc 0 1) ∧
      ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  -- Strategy: Let E_n = {q_n} where q_n is the nth rational in [0,1]
  -- Each singleton is Jordan measurable with measure 0
  -- But the union is all rationals in [0,1], which is NOT Jordan measurable

  -- Get an enumeration of rationals in [0,1]
  have h_countable : (Set.Icc (0:ℚ) 1).Countable := Set.countable_coe_iff.mp inferInstance
  have h_nonempty : (Set.Icc (0:ℚ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨q, hq_surj⟩ := h_countable.exists_surjective h_nonempty

  -- Define E_n = {q_n} (singleton containing the nth rational)
  let E : ℕ → Set ℝ := fun n => {((q n).val : ℝ)}

  use E

  constructor
  -- Part 1: Each E_n is bounded (singleton sets are trivially bounded)
  · intro n
    apply Set.Finite.isBounded
    exact Set.finite_singleton _

  constructor
  -- Part 2: Each E_n is Jordan measurable (singletons have measure 0)
  · intro n
    -- A singleton {x} in ℝ maps to a degenerate box in EuclideanSpace' 1
    -- Specifically, Real.equiv_EuclideanSpace' '' {x} = Icc x x (as a 1D box)
    -- Boxes are elementary, and elementary sets are Jordan measurable
    let x := ((q n).val : ℝ)
    have h_singleton_eq : Real.equiv_EuclideanSpace' '' {x} = (BoundedInterval.Icc x x : Box 1).toSet := by
      rw [BoundedInterval.coe_of_box]
      simp [BoundedInterval.set_Icc]
    rw [h_singleton_eq]
    exact IsElementary.jordanMeasurable (IsElementary.box _)

  constructor
  -- Part 3: Each E_n is contained in [0,1]
  · intro n x hx
    simp [E] at hx
    rcases hx with rfl
    rcases (q n).property with ⟨hq0, hq1⟩
    exact ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩

  -- Part 4: The union ⋃_n E_n = rationals in [0,1], which is NOT Jordan measurable
  · intro hJM
    -- The union equals the set of all rationals in [0,1]
    have h_union_eq_rats : (⋃ n, E n) = Set.range (fun r : Set.Icc (0:ℚ) 1 => (r.val : ℝ)) := by
      ext x
      simp only [E, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · intro ⟨n, hn⟩
        use q n
        exact hn.symm
      · intro ⟨r, hr⟩
        obtain ⟨n, hn⟩ := hq_surj r
        use n
        rw [hn]
        exact hr.symm

    -- The image of the union under Real.equiv_EuclideanSpace' is the image of rationals
    have hJM' : JordanMeasurable (Real.equiv_EuclideanSpace' '' (⋃ n, E n)) := by
      have : (⋃ n, Real.equiv_EuclideanSpace' '' E n) = Real.equiv_EuclideanSpace' '' (⋃ n, E n) := by
        exact Set.image_iUnion.symm
      rw [← this]
      exact hJM

    -- Let Q = rationals in [0,1]
    let Q := Set.range (fun r : Set.Icc (0:ℚ) 1 => (r.val : ℝ))

    -- Show Q is bounded
    have hQ_bounded : Bornology.IsBounded Q := by
      apply Bornology.IsBounded.subset (Metric.isBounded_Icc (a := 0) (b := 1))
      intro x hx
      obtain ⟨r, hr⟩ := hx
      rw [← hr]
      simp
      have : r.val ∈ Set.Icc (0:ℚ) 1 := r.property
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2

    -- Rewrite hJM' in terms of Q
    rw [h_union_eq_rats] at hJM'

    -- Use Exercise 1.1.18(1): Jordan_outer_measure(closure(Q)) = Jordan_outer_measure(Q)
    have h_outer_eq : Jordan_outer_measure (closure (Real.equiv_EuclideanSpace' '' Q)) =
                      Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) := by
      apply JordanMeasurable.outer_measure_of_closure
      have : Bornology.IsBounded (Real.equiv_EuclideanSpace' '' Q) := by
        -- Q ⊆ [0,1] is bounded, so its image under the homeomorphism is bounded
        -- Use that Q is bounded: ∃ M, ∀ x y ∈ Q, dist x y ≤ M
        obtain ⟨c, hc⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hQ_bounded
        -- Show image is bounded by showing it's in a ball
        rw [Metric.isBounded_iff_subset_ball 0]
        use c
        intro v hv
        obtain ⟨x, hx, rfl⟩ := hv
        -- Show Real.equiv_EuclideanSpace' x ∈ Metric.ball 0 c
        -- Since ‖Real.equiv_EuclideanSpace' x‖ = |x| and x ∈ Metric.ball 0 c
        have hx_ball : x ∈ Metric.ball 0 c := hc hx
        rw [Metric.mem_ball, dist_zero_right] at hx_ball
        rw [Metric.mem_ball, dist_zero_right]
        -- ‖Real.equiv_EuclideanSpace' x‖ = |x|
        have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
          simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
          rw [PiLp.norm_eq_of_L2]
          simp
          exact Real.sqrt_sq_eq_abs x
        rw [h_norm_eq]
        exact hx_ball
      exact this

    -- Closure of rationals in [0,1] is [0,1] (rationals are dense)
    have h_closure_Q : closure Q = Set.Icc 0 1 := by
      -- Rationals are dense in [0,1]
      -- First show Q ⊆ [0,1]
      have hQ_subset : Q ⊆ Set.Icc 0 1 := by
        intro y hy
        simp [Q] at hy
        obtain ⟨r, ⟨h_bounds, h_eq⟩⟩ := hy
        rw [← h_eq]
        constructor
        · exact_mod_cast h_bounds.1
        · exact_mod_cast h_bounds.2
      -- Show closure Q ⊆ [0,1] (since [0,1] is closed)
      have h_closure_subset : closure Q ⊆ Set.Icc 0 1 :=
        closure_minimal hQ_subset isClosed_Icc
      -- Show [0,1] ⊆ closure Q (using density of rationals)
      have h_subset_closure : Set.Icc 0 1 ⊆ closure Q := by
        -- Q is the set of rationals in [0,1]
        -- Since rationals are dense in ℝ, Q is dense in [0,1]
        -- Therefore closure Q ⊇ [0,1]
        intro x hx
        -- Use DenseRange for rationals
        have h_dense : ∀ ε > 0, ∃ q : ℚ, |(q:ℝ) - x| < ε ∧ (q:ℝ) ∈ Set.Icc 0 1 := by
          intro ε hε
          -- Find a rational within ε of x using density
          have := Rat.denseRange_cast.exists_dist_lt x hε
          obtain ⟨q, hq⟩ := this
          -- Check if q ∈ [0,1]
          by_cases hq_in : (q:ℝ) ∈ Set.Icc 0 1
          · use q
            have : |(q:ℝ) - x| < ε := by
              rw [← Real.dist_eq, dist_comm]
              exact hq
            exact ⟨this, hq_in⟩
          · -- If q ∉ [0,1], need to find a rational in [0,1] close to x
            -- Recursively use density in a smaller neighborhood that stays within [0,1]
            -- Define the interval [a, b] = [max(0, x-ε/2), min(1, x+ε/2)] ⊆ [0,1]
            let a := max (0 : ℝ) (x - ε / 2)
            let b := min (1 : ℝ) (x + ε / 2)
            have ha : 0 ≤ a := le_max_left _ _
            have hb : b ≤ 1 := min_le_left _ _
            have hax : a ≤ x := by
              simp only [a]
              exact max_le (hx.1) (by linarith)
            have hxb : x ≤ b := by
              simp only [b]
              exact le_min (hx.2) (by linarith)
            have hab : a < b := by
              simp only [a, b]
              apply max_lt
              · -- 0 < min 1 (x + ε / 2)
                apply lt_min
                · norm_num
                · linarith [hx.1, hε]
              · apply lt_min
                · linarith [hx.2]
                · linarith
            -- Find a rational in the open interval (a, b) using density
            have : ∃ r : ℚ, a < (r : ℝ) ∧ (r : ℝ) < b := by
              apply exists_rat_btwn
              exact hab
            obtain ⟨r, har, hrb⟩ := this
            use r
            constructor
            · -- |r - x| < ε
              have : (r : ℝ) ∈ Set.Ioo a b := ⟨har, hrb⟩
              simp [a, b] at this
              rw [abs_sub_lt_iff]
              constructor <;> linarith
            · -- r ∈ [0, 1]
              rw [Set.mem_Icc]
              constructor <;> linarith [har, ha, hrb, hb]
        -- Use h_dense to show x ∈ closure Q
        apply Metric.mem_closure_iff.mpr
        intro ε hε
        obtain ⟨q, hq_dist, hq_in⟩ := h_dense ε hε
        use (q:ℝ)
        constructor
        · -- Show (q:ℝ) ∈ Q (first subgoal from "use")
          simp only [Q, Set.mem_range]
          have hq_bounds : q ∈ Set.Icc (0:ℚ) 1 := by
            rw [Set.mem_Icc] at hq_in ⊢
            exact ⟨by exact_mod_cast hq_in.1, by exact_mod_cast hq_in.2⟩
          use ⟨q, hq_bounds⟩
        · -- Show dist (q:ℝ) x < ε (second subgoal from "use")
          rw [Real.dist_eq]
          rw [abs_sub_comm] at hq_dist
          exact hq_dist
      exact Set.Subset.antisymm h_closure_subset h_subset_closure

    -- Use Real.equiv_EuclideanSpace' commutes with closure
    have h_image_closure : Real.equiv_EuclideanSpace' '' closure Q =
                           closure (Real.equiv_EuclideanSpace' '' Q) := by
      -- Real.equiv_EuclideanSpace' is a homeomorphism (continuous bijection with continuous inverse)
      -- Homeomorphisms preserve closure: f(closure A) = closure(f(A))
      -- To prove this formally would require:
      -- 1. Showing Real.equiv_EuclideanSpace' is continuous (it's the coordinate embedding x ↦ (fun _ => x))
      -- 2. Showing its inverse is continuous (it's the projection (f : Fin 1 → ℝ) ↦ f 0)
      -- 3. Applying image_closure_subset_closure_image in both directions
      -- These are all true but require detailed work with the topology API
      classical
      -- Continuity of the forward and inverse maps
      have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
        have h : Continuous fun x : ℝ => (fun _ : Fin 1 => x) := by
          refine continuous_pi ?_
          intro _; simpa using (continuous_id : Continuous fun x : ℝ => x)
        simpa [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real] using h
      have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
        have : Continuous fun x : EuclideanSpace' 1 => x ⟨0, by decide⟩ :=
          continuous_apply (⟨0, by decide⟩ : Fin 1)
        simpa [EuclideanSpace'.equiv_Real] using this
      -- Package the equivalence as a homeomorphism to apply the library lemma
      let e : ℝ ≃ₜ EuclideanSpace' 1 :=
        { toEquiv := Real.equiv_EuclideanSpace'
          continuous_toFun := hf_cont
          continuous_invFun := hg_cont }
      simpa using e.image_closure Q

    rw [← h_image_closure] at h_outer_eq
    rw [h_closure_Q] at h_outer_eq

    -- [0,1] is a 1D box with Jordan outer measure 1
    have h_Icc_outer : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Set.Icc 0 1) = 1 := by
      -- [0,1] maps to a 1D box [0,1] which is elementary with measure 1
      -- First show that the image is a box
      have h_eq_box : Real.equiv_EuclideanSpace' '' Set.Icc 0 1 = (BoundedInterval.Icc 0 1 : Box 1).toSet := by
        rw [BoundedInterval.coe_of_box]
        simp [BoundedInterval.set_Icc]
      rw [h_eq_box]
      -- This is an elementary set (a box)
      let B := (BoundedInterval.Icc 0 1 : Box 1)
      have hB_elem : IsElementary B.toSet := IsElementary.box B
      -- For an elementary set, Jordan_outer_measure = its measure
      have h_outer_eq_measure : Jordan_outer_measure B.toSet = hB_elem.measure := by
        -- Jordan_outer_measure B = sInf { m | ∃ A elementary, B ⊆ A ∧ m = hA.measure }
        -- Since B is elementary and B ⊆ B, we have hB_elem.measure in the set
        -- Need to show: sInf of this set = hB_elem.measure
        apply le_antisymm
        · -- Jordan_outer_measure B ≤ hB_elem.measure
          exact Jordan_outer_le hB_elem (Set.Subset.refl B.toSet)
        · -- hB_elem.measure ≤ Jordan_outer_measure B
          -- For any A elementary with B ⊆ A, we have hB_elem.measure ≤ hA.measure
          unfold Jordan_outer_measure
          apply le_csInf
          · -- Show the set is nonempty
            use hB_elem.measure, B.toSet, hB_elem, Set.Subset.refl B.toSet
          · -- Show hB_elem.measure is a lower bound
            intro m hm
            obtain ⟨A, hA, hB_subset_A, rfl⟩ := hm
            exact IsElementary.measure_mono hB_elem hA hB_subset_A
      rw [h_outer_eq_measure]
      -- The measure of the box [0,1] is 1
      have h_measure_eq_volume : hB_elem.measure = |B|ᵥ := IsElementary.measure_of_box B
      rw [h_measure_eq_volume]
      -- Volume of 1D box is the length of its side
      simp [Box.volume, B, BoundedInterval.length]

    -- So Q has outer measure 1
    rw [h_Icc_outer] at h_outer_eq
    have h_Q_outer : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) = 1 := h_outer_eq.symm

    -- Use Exercise 1.1.18(2): Jordan_inner_measure(interior(Q)) = Jordan_inner_measure(Q)
    have h_inner_eq : Jordan_inner_measure (interior (Real.equiv_EuclideanSpace' '' Q)) =
                      Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) := by
      apply JordanMeasurable.inner_measure_of_interior
      have : Bornology.IsBounded (Real.equiv_EuclideanSpace' '' Q) := by
        -- Same proof as for outer measure
        obtain ⟨c, hc⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hQ_bounded
        rw [Metric.isBounded_iff_subset_ball 0]
        use c
        intro v hv
        obtain ⟨x, hx, rfl⟩ := hv
        have hx_ball : x ∈ Metric.ball 0 c := hc hx
        rw [Metric.mem_ball, dist_zero_right] at hx_ball
        rw [Metric.mem_ball, dist_zero_right]
        have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
          simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
          rw [PiLp.norm_eq_of_L2]
          simp
          exact Real.sqrt_sq_eq_abs x
        rw [h_norm_eq]
        exact hx_ball
      exact this

    -- Interior of Q (rationals) is empty (rationals have no interior)
    have h_interior_Q : interior Q = ∅ := by
      -- Rationals have empty interior because irrationals are dense
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      -- x ∈ interior Q means there's an open neighborhood of x contained in Q
      rw [mem_interior_iff_mem_nhds] at hx
      -- This means Q ∈ nhds x, which means there's an open set U with x ∈ U ⊆ Q
      obtain ⟨U, hU_Q, hU_open, hx_U⟩ := mem_nhds_iff.mp hx
      -- Find an open ball around x contained in U
      obtain ⟨ε, hε, hball_subset⟩ := Metric.isOpen_iff.mp hU_open x hx_U
      -- Use density of irrationals to find an irrational in the ball
      have h_ball_nonempty : (Metric.ball x ε).Nonempty := ⟨x, Metric.mem_ball_self hε⟩
      obtain ⟨y, hy_mem⟩ := Dense.inter_open_nonempty dense_irrational (Metric.ball x ε) Metric.isOpen_ball h_ball_nonempty
      rw [Set.mem_inter_iff] at hy_mem
      -- Components: first is y ∈ {x | Irrational x}, second is y ∈ Metric.ball x ε
      -- But Lean gives them in opposite order
      obtain ⟨hy_ball_mem, hy_irrat_mem⟩ := hy_mem
      -- y is in U (since ball ⊆ U)
      have hy_U : y ∈ U := hball_subset hy_ball_mem
      -- So y ∈ Q (since U ⊆ Q)
      have hy_Q : y ∈ Q := hU_Q hy_U
      -- But Q contains only rationals
      simp only [Q, Set.mem_range] at hy_Q
      obtain ⟨r, hr⟩ := hy_Q
      -- So y is rational: hr shows (r.val : ℝ) = y, so r.val is the rational witness
      have hy_rational : ∃ q : ℚ, (q:ℝ) = y := ⟨r.val, hr⟩
      -- But y is irrational: hy_irrat_mem : y ∈ {x | Irrational x}
      -- This means Irrational y, which contradicts hy_rational
      simp only [Set.mem_setOf_eq] at hy_irrat_mem
      exact hy_irrat_mem hy_rational

    -- Real.equiv_EuclideanSpace' commutes with interior
    have h_image_interior : Real.equiv_EuclideanSpace' '' interior Q =
                             interior (Real.equiv_EuclideanSpace' '' Q) := by
      -- This is a standard fact about homeomorphisms: they preserve interior
      -- The proof requires showing that Real.equiv_EuclideanSpace' and its inverse
      -- are both open maps (they map open sets to open sets)
      -- This is true because Real.equiv_EuclideanSpace' is a homeomorphism
      -- between ℝ and EuclideanSpace' 1
      classical
      -- Continuity of the forward and inverse maps
      have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
        have h : Continuous fun x : ℝ => (fun _ : Fin 1 => x) := by
          refine continuous_pi ?_
          intro _; simpa using (continuous_id : Continuous fun x : ℝ => x)
        simpa [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real] using h
      have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
        have : Continuous fun x : EuclideanSpace' 1 => x ⟨0, by decide⟩ :=
          continuous_apply (⟨0, by decide⟩ : Fin 1)
        simpa [EuclideanSpace'.equiv_Real] using this
      -- Package these maps as a homeomorphism and apply the general lemma on interiors
      let e : ℝ ≃ₜ EuclideanSpace' 1 :=
        { toEquiv := Real.equiv_EuclideanSpace'
          continuous_toFun := hf_cont
          continuous_invFun := hg_cont }
      simpa using e.image_interior Q

    rw [← h_image_interior] at h_inner_eq
    rw [h_interior_Q, Set.image_empty] at h_inner_eq

    -- Inner measure of empty set is 0
    have h_empty_inner : Jordan_inner_measure (∅ : Set (EuclideanSpace' 1)) = 0 := by
      -- The only elementary subset of ∅ is ∅, which has measure 0
      unfold Jordan_inner_measure
      -- Jordan_inner_measure ∅ = sSup { m | ∃ A elementary, A ⊆ ∅ ∧ m = hA.measure }
      -- The only A with A ⊆ ∅ is A = ∅, which has measure 0
      -- So the set is (at most) {0}, and sSup {0} = 0
      apply le_antisymm
      · -- sSup ≤ 0: show every element in the set is ≤ 0
        apply csSup_le
        · -- Show the set is nonempty
          use 0, ∅, IsElementary.empty 1
          simp [IsElementary.measure_of_empty]
        · -- Show every element is ≤ 0
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          -- A ⊆ ∅ means A = ∅
          have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
          -- So hA.measure = (IsElementary.empty 1).measure = 0
          subst hA_empty
          exact le_of_eq (IsElementary.measure_of_empty 1)
      · -- 0 ≤ sSup: 0 is in the set
        apply le_csSup
        · -- Show the set is bounded above
          use 0
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
          subst hA_empty
          exact le_of_eq (IsElementary.measure_of_empty 1)
        · -- Show 0 is in the set
          use ∅, IsElementary.empty 1
          simp [IsElementary.measure_of_empty]

    rw [h_empty_inner] at h_inner_eq
    have h_Q_inner : Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) = 0 := h_inner_eq.symm

    -- But Jordan measurable means inner = outer
    have h_eq : Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) =
                Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) := by
      exact hJM'.2

    -- This gives 0 = 1, contradiction
    rw [h_Q_inner, h_Q_outer] at h_eq
    exact absurd h_eq (by norm_num)

/-- Exercise 1.2.1 (countable union) -/
example :
    ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
  (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n)))
      ∧ ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  obtain ⟨E, hB, hJM, -, h_union⟩ := exercise_1_2_1_union
  exact ⟨E, hB, hJM, h_union⟩

/-- Exercise 1.2.1 (countable intersection) -/
example :
    ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n))) ∧
      ¬ JordanMeasurable (⋂ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  classical
  obtain ⟨S, hS_bdd, hS_jm, hS_subset, hS_union_not⟩ := exercise_1_2_1_union
  let I : Set ℝ := Set.Icc 0 1
  let E : ℕ → Set ℝ := fun n => I \ S n
  have hI_image :
      Real.equiv_EuclideanSpace' '' I =
        (BoundedInterval.Icc 0 1 : Box 1).toSet := by
    rw [BoundedInterval.coe_of_box]
    simp [I, BoundedInterval.set_Icc]
  have hI_JM :
      JordanMeasurable (Real.equiv_EuclideanSpace' '' I) := by
    let B : Box 1 := BoundedInterval.Icc 0 1
    simpa [hI_image, B] using
      (IsElementary.jordanMeasurable (IsElementary.box B))
  have h_image_diff :
      ∀ n,
        Real.equiv_EuclideanSpace' '' (E n) =
          (Real.equiv_EuclideanSpace' '' I) \
            (Real.equiv_EuclideanSpace' '' (S n)) := by
    intro n
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨?_, ?_⟩
      · exact Set.mem_image_of_mem _ hx.1
      · intro hyC
        obtain ⟨z, hz, hz_eq⟩ := hyC
        have : z = x := by
          apply Real.equiv_EuclideanSpace'.injective
          simpa using hz_eq
        exact hx.2 (this ▸ hz)
    · intro hy
      rcases hy with ⟨hyA, hy_not⟩
      obtain ⟨x, hxI, rfl⟩ := hyA
      refine ⟨x, ?_, rfl⟩
      constructor
      · exact hxI
      · intro hxS
        exact hy_not ⟨x, hxS, rfl⟩

  refine ⟨E, ?_, ?_, ?_⟩
  · intro n
    apply Bornology.IsBounded.subset (Metric.isBounded_Icc (a := 0) (b := 1))
    exact Set.diff_subset
  ·
    intro n
    have hJ :
        JordanMeasurable
          ((Real.equiv_EuclideanSpace' '' I) \
            (Real.equiv_EuclideanSpace' '' (S n))) :=
      JordanMeasurable.sdiff hI_JM (hS_jm n)
    exact (h_image_diff n).symm ▸ hJ
  ·
    -- De Morgan's law inside the box [0,1]
    let A := Real.equiv_EuclideanSpace' '' I
    let C : ℕ → Set (EuclideanSpace' 1) :=
      fun n => Real.equiv_EuclideanSpace' '' (S n)
    let F : ℕ → Set (EuclideanSpace' 1) :=
      fun n => Real.equiv_EuclideanSpace' '' (E n)
    have hF_eq : ∀ n, F n = A \ C n := by
      intro n
      simpa [F, C, A] using h_image_diff n
    have hC_union_not : ¬ JordanMeasurable (⋃ n, C n) := by
      have h_image_union :
          Real.equiv_EuclideanSpace' '' (⋃ n, S n) =
            ⋃ n, C n := by
        ext y
        constructor
        · intro hy
          obtain ⟨x, hx, rfl⟩ := hy
          obtain ⟨n, hxSn⟩ := Set.mem_iUnion.mp hx
          refine Set.mem_iUnion.mpr ?_
          exact ⟨n, ⟨x, hxSn, rfl⟩⟩
        · intro hy
          obtain ⟨n, hyC⟩ := Set.mem_iUnion.mp hy
          obtain ⟨x, hxSn, rfl⟩ := hyC
          exact Set.mem_image_of_mem _ (Set.mem_iUnion.mpr ⟨n, hxSn⟩)
      simpa [C, h_image_union] using hS_union_not
    have h_inter_eq :
        (⋂ n, F n) = A \ ⋃ n, C n := by
      ext x
      constructor
      · intro hx
        have hx_all : ∀ n, x ∈ A \ C n := by
          have hx_all' := Set.mem_iInter.mp hx
          intro n
          simpa [hF_eq n] using hx_all' n
        have hxA : x ∈ A := (hx_all 0).1
        have hx_not : x ∉ ⋃ n, C n := by
          intro hx_union
          obtain ⟨n, hxC⟩ := Set.mem_iUnion.mp hx_union
          exact (hx_all n).2 hxC
        exact ⟨hxA, hx_not⟩
      · intro hx
        have hxA : x ∈ A := hx.1
        have hx_not : x ∉ ⋃ n, C n := hx.2
        refine Set.mem_iInter.mpr ?_
        intro n
        have : x ∈ A \ C n := by
          refine ⟨hxA, ?_⟩
          intro hxC
          exact hx_not (Set.mem_iUnion.mpr ⟨n, hxC⟩)
        simpa [hF_eq n] using this
    intro hJM_inter
    have hC_subset : ∀ n, C n ⊆ A := by
      intro n x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Set.mem_image_of_mem _ (hS_subset n hy)
    have h_union_subset : (⋃ n, C n) ⊆ A := by
      intro x hx
      obtain ⟨n, hxC⟩ := Set.mem_iUnion.mp hx
      exact hC_subset n hxC
    have h_union_JM : JordanMeasurable (⋃ n, C n) := by
      have h_diff :
          JordanMeasurable (A \ (⋂ n, F n)) :=
        JordanMeasurable.sdiff
          (by simpa [A] using hI_JM) hJM_inter
      classical
      have h_congr := congrArg (fun s => A \ s) h_inter_eq
      have h_step :
          A \ (A \ ⋃ n, C n) = A ∩ ⋃ n, C n := by
        ext x
        constructor
        · intro hx
          have hx_union : x ∈ ⋃ n, C n := by
            by_contra hx_not
            exact hx.2 ⟨hx.1, hx_not⟩
          exact ⟨hx.1, hx_union⟩
        · intro hx
          refine ⟨hx.1, ?_⟩
          intro hx_diff
          exact hx_diff.2 hx.2
      have h_eq :
          (A \ (⋂ n, F n)) = A ∩ ⋃ n, C n :=
        h_congr.trans h_step
      have h_eq' : A ∩ ⋃ n, C n = ⋃ n, C n := by
        apply Set.Subset.antisymm
        · intro x hx
          exact hx.2
        · intro x hx
          exact ⟨h_union_subset hx, hx⟩
      have h_target : JordanMeasurable (A ∩ ⋃ n, C n) :=
        by simpa [h_eq] using h_diff
      simpa [h_eq'] using h_target
    exact hC_union_not h_union_JM


/-- Exercise 1.2.2 -/
example : ∃ f: ℕ → ℝ → ℝ, ∃ F: ℝ → ℝ, ∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M ∧
    Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (F x)) ∧
      ¬ (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ Set.Icc 0 1, |f n x - F x| < ε) := by
  sorry

/-! ### Section 1.2: Lebesgue Measure (continued) -/

/-- Auxiliary definition for Lebesgue measure (Definition 1.2.1) -/
noncomputable abbrev Lebesgue_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sInf { m:ℝ | ∃ (A: ℕ → Set (EuclideanSpace' d)) (hA: ∀ n, IsElementary (A n)), E ⊆ ⋃ n, A n ∧ m = ∑' n, (hA n).measure }

/-- Definition 1.2.1 (Lebesgue measurable sets) -/
noncomputable abbrev LebesgueMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  ∀ F: Set (EuclideanSpace' d), Bornology.IsBounded F →
    Lebesgue_outer_measure (F ∩ E) + Lebesgue_outer_measure (F \ E) = Lebesgue_outer_measure F

-- Alternative definition using outer approximation
abbrev IsNull {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  Lebesgue_outer_measure E = 0

-- Definition 1.2.2 (Lebesgue measure)
noncomputable abbrev Lebesgue_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  Lebesgue_outer_measure E

-- Lebesgue Outer Measure Properties
section LebesgueOuterMeasure

theorem Lebesgue_outer_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Lebesgue_outer_measure E := by
  sorry

theorem Lebesgue_outer_measure_empty {d:ℕ} : Lebesgue_outer_measure (∅: Set (EuclideanSpace' d)) = 0 := by
  sorry

theorem Lebesgue_outer_measure_mono {d:ℕ} {E F: Set (EuclideanSpace' d)} (h: E ⊆ F) :
  Lebesgue_outer_measure E ≤ Lebesgue_outer_measure F := by
  sorry

-- Part 2 (≥): sInf of box covers ≥ Jordan_outer_measure E
/-- For any E ⊆ ℝᵈ, Lebesgue outer measure ≥ Jordan outer measure -/
theorem Lebesgue_outer_ge_Jordan_outer {d:ℕ} (E: Set (EuclideanSpace' d)) :
  Jordan_outer_measure E ≤ Lebesgue_outer_measure E := by
  -- Strategy:
  -- 1. Unfold Jordan_outer_measure: sInf { A.measure | A elementary, E ⊆ A }
  -- 2. Unfold Lebesgue_outer_measure: sInf { ∑ A_n.measure | E ⊆ ⋃_n A_n, each A_n elementary }
  -- 3. Show Jordan_outer_measure is a lower bound for Lebesgue set:
  --    For any sequence (A_n) covering E, ⋃_n A_n is elementary (if finite union), so its measure ≤ ∑ A_n.measure
  -- 4. Use csInf_le_csInf
  sorry

end LebesgueOuterMeasure
