import Mathlib.Tactic

/-!
# General utilities for Real, EReal, and ENNReal

This file contains general-purpose lemmas about Real, EReal, and ENNReal
that are not specific to measure theory but are used throughout the formalization.
-/

-- =============================================================================
-- Real number utilities
-- =============================================================================

/-- max distributes over division by 2 -/
lemma max_div_two (x : ℝ) : max x 0 / 2 = max (x / 2) 0 := by
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx, max_eq_left (div_nonneg hx (by norm_num : (0:ℝ) < 2).le)]
  · push_neg at hx
    simp [max_eq_right (le_of_lt hx), max_eq_right (by linarith : x / 2 ≤ 0)]

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

-- =============================================================================
-- EReal utilities
-- =============================================================================

/-- For EReal, adding a positive real value to a value that is neither ⊥ nor ⊤ gives a strictly greater result. -/
lemma EReal.lt_add_of_pos_coe {x : EReal} {ε : ℝ} (hε : 0 < ε) (h_ne_bot : x ≠ ⊥) (h_ne_top : x ≠ ⊤) :
    x < x + ↑ε := by
  have h_eps : (0 : EReal) < (ε : EReal) := EReal.coe_pos.mpr hε
  have : 0 + x < ↑ε + x := EReal.add_lt_add_of_lt_of_le h_eps (le_refl x) h_ne_bot h_ne_top
  simpa [add_comm] using this

/-- EReal epsilon argument: if for all positive ε, a ≤ b + ε, then a ≤ b.
    This holds when b ≠ ⊤ (if b = ⊤, the implication is trivially true). -/
lemma EReal.le_of_forall_pos_le_add' {a b : EReal}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) : a ≤ b := by
  by_cases hb : b = ⊤
  · simp [hb]
  · by_contra ha_gt
    push_neg at ha_gt
    -- a > b and b ≠ ⊤
    induction a using EReal.rec with
    | bot => simp at ha_gt
    | top =>
      -- a = ⊤, b ≠ ⊤ means ⊤ ≤ b + 1 must hold by h, but b + 1 < ⊤
      specialize h 1 (by norm_num : (0:ℝ) < 1)
      have hb1 : b + (1 : ℝ) < ⊤ := by
        cases b with
        | bot => simp
        | top => exact (hb rfl).elim
        | coe b' =>
          have : (b' : EReal) + (1:ℝ) = ((b' + 1) : ℝ) := by norm_cast
          rw [this]; exact EReal.coe_lt_top _
      exact not_le.mpr hb1 h
    | coe a' =>
      induction b using EReal.rec with
      | bot =>
        -- b = ⊥, so a' > ⊥ always. But ⊥ + ε = ⊥, so h gives a' ≤ ⊥, contradiction
        specialize h 1 (by norm_num : (0:ℝ) < 1)
        simp at h
      | top => exact hb rfl
      | coe b' =>
        -- Both finite: a' > b', pick ε = (a' - b') / 2
        have hab : b' < a' := EReal.coe_lt_coe_iff.mp ha_gt
        specialize h ((a' - b') / 2) (by linarith)
        rw [show (b' : EReal) + ((a' - b') / 2 : ℝ) = ((b' + (a' - b') / 2) : ℝ) by norm_cast] at h
        have h_ineq : b' + (a' - b') / 2 < a' := by linarith
        exact not_le.mpr (EReal.coe_lt_coe_iff.mpr h_ineq) h

/-- For non-negative reals, toEReal commutes with finite sums.
    Uses induction on the finset with EReal.coe_add. -/
lemma EReal.coe_finset_sum {α : Type*} {s : Finset α} {f : α → ℝ}
    (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∑ a ∈ s, f a).toEReal = ∑ a ∈ s, (f a).toEReal := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s' ha ih =>
    rw [Finset.sum_cons ha, Finset.sum_cons ha]
    have hf_s' : ∀ x ∈ s', 0 ≤ f x := fun x hx => hf x (Finset.mem_cons_of_mem hx)
    rw [EReal.coe_add, ih hf_s']

-- =============================================================================
-- ENNReal/EReal tsum utilities
-- =============================================================================

/-- Helper: Coercion from ENNReal to EReal preserves summability.
    All ENNReal sequences are summable, and their coercions to EReal are also summable. -/
lemma Summable.coe_ennreal {α : Type*} {f : α → ENNReal} :
    Summable (fun x => ↑(f x) : α → EReal) := by
  -- All ENNReal sequences are summable
  have h_sum : Summable f := ENNReal.summable
  -- Get the HasSum for the original sequence
  have h_has_sum : HasSum f (∑' x, f x) := h_sum.hasSum
  -- The coercion preserves addition: ↑(x + y) = ↑x + ↑y
  have h_add : ∀ x y : ENNReal, (↑(x + y) : EReal) = (↑x : EReal) + (↑y : EReal) := EReal.coe_ennreal_add
  -- Construct an AddMonoidHom from the coercion
  -- Note: We need to show the coercion is an additive monoid homomorphism
  let φ : ENNReal →+ EReal := {
    toFun := fun x => (↑x : EReal)
    map_zero' := by simp
    map_add' := h_add
  }
  -- Coercion is continuous
  have h_cont : Continuous φ := continuous_coe_ennreal_ereal
  -- Apply HasSum.map to show the coerced sequence has a sum
  have h_has_sum_coe : HasSum (fun x => ↑(f x) : α → EReal) ↑(∑' x, f x) :=
    h_has_sum.map φ h_cont
  -- Summable follows from HasSum
  exact h_has_sum_coe.summable

/-- Helper: Addition of tsums of ENNReal values coerced to EReal.
    (∑' n, ↑(a n) : EReal) + (∑' n, ↑(b n) : EReal) = (∑' n, ↑(a n + b n) : EReal)

    This follows from ENNReal.tsum_add and the fact that coercion commutes with addition. -/
lemma EReal.tsum_add_coe_ennreal {α : Type*} {a b : α → ENNReal} :
    (∑' n, ↑(a n) : EReal) + (∑' n, ↑(b n) : EReal) = (∑' n, ↑(a n + b n) : EReal) := by
  -- Use ENNReal.tsum_add: ∑' n, (a n + b n) = ∑' n, a n + ∑' n, b n
  have h_tsum_add : (∑' n, (a n + b n) : ENNReal) = (∑' n, a n : ENNReal) + (∑' n, b n : ENNReal) := by
    rw [ENNReal.tsum_add]
  -- Coerce both sides: ↑(∑' n, a n + b n) = ↑(∑' n, a n) + ↑(∑' n, b n)
  -- Use Summable.map_tsum: continuous additive maps commute with tsum
  -- All ENNReal sequences are summable
  have h_sum_a : Summable a := ENNReal.summable
  have h_sum_b : Summable b := ENNReal.summable
  have h_sum_ab : Summable (fun n => a n + b n) := ENNReal.summable
  -- Construct the AddMonoidHom from ENNReal to EReal (same as in Summable.coe_ennreal)
  have h_add : ∀ x y : ENNReal, (↑(x + y) : EReal) = (↑x : EReal) + (↑y : EReal) := EReal.coe_ennreal_add
  let φ : ENNReal →+ EReal := {
    toFun := fun x => (↑x : EReal)
    map_zero' := by simp
    map_add' := h_add
  }
  have h_cont : Continuous φ := continuous_coe_ennreal_ereal
  -- Apply Summable.map_tsum to show coercion commutes with tsum
  have h_coe_tsum_a : (∑' n, ↑(a n) : EReal) = ↑(∑' n, a n : ENNReal) := by
    exact (Summable.map_tsum h_sum_a φ h_cont).symm
  have h_coe_tsum_b : (∑' n, ↑(b n) : EReal) = ↑(∑' n, b n : ENNReal) := by
    exact (Summable.map_tsum h_sum_b φ h_cont).symm
  have h_coe_tsum_sum : (∑' n, ↑(a n + b n) : EReal) = ↑(∑' n, (a n + b n) : ENNReal) := by
    exact (Summable.map_tsum h_sum_ab φ h_cont).symm
  rw [h_coe_tsum_a, h_coe_tsum_b, h_coe_tsum_sum]
  rw [← EReal.coe_ennreal_add]
  congr 1
  exact h_tsum_add.symm

/-- ENNReal coercion to EReal commutes with finite sums -/
lemma EReal.coe_ennreal_finset_sum {α : Type*} {s : Finset α} {f : α → ENNReal} :
    (∑ a ∈ s, f a : ENNReal).toEReal = ∑ a ∈ s, (f a).toEReal := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => simp only [Finset.sum_cons ha, EReal.coe_ennreal_add, ih]

/-- Finite sum embedded in EReal is bounded by tsum.
    For nonnegative reals, finite partial sums are always ≤ the infinite sum.
    Strategy: Convert to ENNReal where sum_le_tsum holds, then transfer via coercion. -/
lemma EReal.finset_sum_le_tsum {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (t : Finset ℕ) :
    (∑ n ∈ t, f n : EReal) ≤ ∑' n, (f n).toEReal := by
  -- Convert LHS to EReal via coe_finset_sum
  have hf_t : ∀ a ∈ t, 0 ≤ f a := fun a _ => hf a
  rw [← EReal.coe_finset_sum hf_t]
  -- Define the ENNReal version of f
  let g : ℕ → ENNReal := fun n => ENNReal.ofReal (f n)
  -- Key fact: ENNReal.sum_le_tsum always holds
  have h_enn : ∑ n ∈ t, g n ≤ ∑' n, g n := ENNReal.sum_le_tsum t
  -- Show each term equality: (f n).toEReal = (g n).toEReal for nonneg f n
  have h_term : ∀ n, (f n).toEReal = (g n).toEReal := fun n => by
    simp only [g, EReal.coe_ennreal_ofReal, max_eq_left (hf n)]
  -- Show finite sum equality
  have h_fin : (∑ n ∈ t, f n : ℝ).toEReal = (∑ n ∈ t, g n : ENNReal).toEReal := by
    rw [EReal.coe_finset_sum hf_t, EReal.coe_ennreal_finset_sum]
    exact Finset.sum_congr rfl (fun n _ => h_term n)
  -- Show tsum equality
  have h_inf : ∑' n, (f n).toEReal = (∑' n, g n : ENNReal).toEReal := by
    have h_sum : Summable g := ENNReal.summable
    -- Use that continuous additive maps commute with tsum
    have h_coe_tsum : (∑' n, g n : ENNReal).toEReal = ∑' n, (g n).toEReal := by
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := by simp
        map_add' := EReal.coe_ennreal_add
      }
      exact Summable.map_tsum h_sum φ continuous_coe_ennreal_ereal
    rw [h_coe_tsum]
    exact tsum_congr (fun n => h_term n)
  -- Transfer inequality via monotone coercion
  rw [h_fin, h_inf]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_enn

/-- Helper: For non-negative real sequences, tsum addition inequality in EReal.
    If f n + g n ≤ h n pointwise, then ∑' f.toEReal + ∑' g.toEReal ≤ ∑' h.toEReal. -/
lemma EReal.tsum_add_le_of_nonneg_pointwise {f g h : ℕ → ℝ}
    (hf_nn : ∀ n, 0 ≤ f n) (hg_nn : ∀ n, 0 ≤ g n)
    (h_pw : ∀ n, f n + g n ≤ h n) :
    (∑' n, (f n).toEReal) + (∑' n, (g n).toEReal) ≤ ∑' n, (h n).toEReal := by
  -- Convert to ENNReal where we have better tsum properties
  -- For non-negative reals, x.toEReal = (ENNReal.ofReal x : EReal)
  have hf_eq : ∀ n, (f n).toEReal = (ENNReal.ofReal (f n) : EReal) := by
    intro n; simp [EReal.coe_ennreal_ofReal, max_eq_left (hf_nn n)]
  have hg_eq : ∀ n, (g n).toEReal = (ENNReal.ofReal (g n) : EReal) := by
    intro n; simp [EReal.coe_ennreal_ofReal, max_eq_left (hg_nn n)]
  have hh_eq : ∀ n, (h n).toEReal = (ENNReal.ofReal (h n) : EReal) := by
    intro n; simp [EReal.coe_ennreal_ofReal, max_eq_left (le_trans (add_nonneg (hf_nn n) (hg_nn n)) (h_pw n))]

  -- Rewrite using these equalities
  simp_rw [hf_eq, hg_eq, hh_eq]

  -- Need to show: (∑' n, ↑(ENNReal.ofReal (f n)) : EReal) + (∑' n, ↑(ENNReal.ofReal (g n)) : EReal)
  --            ≤ (∑' n, ↑(ENNReal.ofReal (h n)) : EReal)
  -- Use helper lemma to combine sums
  let a : ℕ → ENNReal := fun n => ENNReal.ofReal (f n)
  let b : ℕ → ENNReal := fun n => ENNReal.ofReal (g n)
  let c : ℕ → ENNReal := fun n => ENNReal.ofReal (h n)

  -- Combine the sums on LHS using helper lemma
  have h_combine : (∑' n, ↑(a n) : EReal) + (∑' n, ↑(b n) : EReal) = (∑' n, ↑(a n + b n) : EReal) := by
    exact EReal.tsum_add_coe_ennreal
  -- Expand a and b in the goal to match h_combine
  simp only [a, b] at *
  -- Rewrite LHS to combined form
  rw [h_combine]

  -- Now need: (∑' n, ↑(ENNReal.ofReal (f n) + ENNReal.ofReal (g n)) : EReal)
  --         ≤ (∑' n, ↑(ENNReal.ofReal (h n)) : EReal)
  have h_sum_lhs : Summable (fun n => ↑(ENNReal.ofReal (f n) + ENNReal.ofReal (g n)) : ℕ → EReal) :=
    Summable.coe_ennreal
  have h_sum_rhs : Summable (fun n => ↑(ENNReal.ofReal (h n)) : ℕ → EReal) :=
    Summable.coe_ennreal
  refine Summable.tsum_le_tsum (fun n => ?_) h_sum_lhs h_sum_rhs
  -- Pointwise inequality: ↑(ofReal (f n) + ofReal (g n)) ≤ ↑(ofReal (h n))
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  have h_add_eq : ENNReal.ofReal (f n) + ENNReal.ofReal (g n) = ENNReal.ofReal (f n + g n) := by
    rw [ENNReal.ofReal_add (hf_nn n) (hg_nn n)]
  rw [h_add_eq]
  exact ENNReal.ofReal_le_ofReal (h_pw n)
