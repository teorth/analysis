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
              exact add_le_add_right ih _

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
  · subst hb; exact le_top
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
        | bot => exact bot_lt_top
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

/-- Multiplication distributes over finite sums for EReal when all summands are non-negative.
    This is needed because EReal lacks a general `LeftDistribClass` instance. -/
lemma EReal.mul_finset_sum_of_nonneg (n : ℕ) (c : EReal) (f : Fin n → EReal) (hf : ∀ i, 0 ≤ f i) :
    c * (∑ i, f i) = ∑ i, c * f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, f i.castSucc := Finset.sum_nonneg (fun i _ => hf _)
    have hlast_nonneg : 0 ≤ f (Fin.last n) := hf _
    rw [EReal.left_distrib_of_nonneg hsum_nonneg hlast_nonneg]
    congr 1
    exact ih (fun i => f i.castSucc) (fun i => hf _)

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

/-- Pointwise EReal ≤ nonneg Real implies tsum inequality.
    If 0 ≤ f n ≤ ↑(g n) for all n, where g n ≥ 0 and g summable, then ∑' f ≤ ↑(∑' g).
    Routes through ENNReal where tsum comparison is unconditional. -/
lemma EReal.tsum_le_coe_tsum_of_forall_le {f : ℕ → EReal} {g : ℕ → ℝ}
    (hf_nn : ∀ n, 0 ≤ f n) (hg_nn : ∀ n, 0 ≤ g n) (hg_sum : Summable g)
    (h_le : ∀ n, f n ≤ (g n : EReal)) :
    ∑' n, f n ≤ (∑' n, g n : EReal) := by
  -- Define ENNReal version of g
  let g' : ℕ → ENNReal := fun n => ENNReal.ofReal (g n)
  -- Key: (g n : EReal) = (g' n : EReal) for nonneg g
  have hg_eq : ∀ n, (g n : EReal) = (g' n : EReal) := fun n => by
    simp only [g', EReal.coe_ennreal_ofReal, max_eq_left (hg_nn n)]
  -- Define f truncated to ENNReal: since 0 ≤ f n, use EReal.toENNReal
  let f' : ℕ → ENNReal := fun n => (f n).toENNReal
  -- For 0 ≤ f n, we have (f' n : EReal) = f n
  have hf_eq : ∀ n, f n = (f' n : EReal) := fun n => by
    simp only [f']
    exact (EReal.coe_toENNReal (hf_nn n)).symm
  -- f' n ≤ g' n follows from h_le and the equality
  have hf'_le : ∀ n, f' n ≤ g' n := by
    intro n
    simp only [f', g']
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal (hf_nn n)]
    calc f n ≤ (g n : EReal) := h_le n
      _ = ↑(ENNReal.ofReal (g n)) := hg_eq n
  -- Use ENNReal.tsum_le_tsum
  have h_enn : ∑' n, f' n ≤ ∑' n, g' n := ENNReal.tsum_le_tsum hf'_le
  -- Coercion commutes with tsum for ENNReal sequences
  let φ : ENNReal →+ EReal := {
    toFun := (↑·)
    map_zero' := by simp
    map_add' := EReal.coe_ennreal_add
  }
  have h_cont : Continuous φ := continuous_coe_ennreal_ereal
  have h_comm_f : ∑' n, (f' n : EReal) = (∑' n, f' n : ENNReal).toEReal :=
    (Summable.map_tsum (f := f') ENNReal.summable φ h_cont).symm
  have h_comm_g : ∑' n, (g' n : EReal) = (∑' n, g' n : ENNReal).toEReal :=
    (Summable.map_tsum (f := g') ENNReal.summable φ h_cont).symm
  -- Rewrite RHS using hg_eq and h_comm_g
  have h_rhs : (∑' n, g n : EReal) = (∑' n, g' n : ENNReal).toEReal := by
    calc (∑' n, g n : EReal) = ∑' n, (g' n : EReal) := tsum_congr (fun n => hg_eq n)
      _ = (∑' n, g' n : ENNReal).toEReal := h_comm_g
  -- Chain the equalities and inequality
  rw [h_rhs]
  simp_rw [hf_eq, h_comm_f]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_enn

/-- Coercion from ℝ to EReal commutes with tsum for nonneg summable sequences.
    For nonneg g with Summable g: ↑(∑' n, g n : ℝ) = ∑' n, ↑(g n) : EReal -/
lemma EReal.coe_tsum_of_nonneg {g : ℕ → ℝ} (hg_nn : ∀ n, 0 ≤ g n) (hg_sum : Summable g) :
    (↑(∑' n, g n) : EReal) = ∑' n, (g n : EReal) := by
  -- Route through ENNReal using ofReal_tsum_of_nonneg
  let g' : ℕ → ENNReal := fun n => ENNReal.ofReal (g n)
  -- Key: (g n : EReal) = (g' n : EReal) for nonneg g
  have hg_eq : ∀ n, (g n : EReal) = (g' n : EReal) := fun n => by
    simp only [g', EReal.coe_ennreal_ofReal, max_eq_left (hg_nn n)]
  -- ENNReal.ofReal (∑' g) = ∑' g' by mathlib's ofReal_tsum_of_nonneg
  have h_ennreal : ENNReal.ofReal (∑' n, g n) = ∑' n, g' n :=
    ENNReal.ofReal_tsum_of_nonneg hg_nn hg_sum
  -- ↑(∑' g n : ℝ) = ↑(ENNReal.ofReal (∑' g n)) = ↑(∑' g' n)
  have h_lhs : (↑(∑' n, g n) : EReal) = ↑(∑' n, g' n : ENNReal) := by
    rw [← h_ennreal]
    simp only [EReal.coe_ennreal_ofReal, max_eq_left (tsum_nonneg hg_nn)]
  -- ∑' (g n : EReal) = ∑' (g' n : EReal) = ↑(∑' g' n : ENNReal)
  have h_rhs : ∑' n, (g n : EReal) = ↑(∑' n, g' n : ENNReal) := by
    calc ∑' n, (g n : EReal) = ∑' n, (g' n : EReal) := tsum_congr (fun n => hg_eq n)
      _ = ↑(∑' n, g' n : ENNReal) := by
        let φ : ENNReal →+ EReal := {
          toFun := (↑·)
          map_zero' := by simp
          map_add' := EReal.coe_ennreal_add
        }
        exact (Summable.map_tsum (f := g') ENNReal.summable φ continuous_coe_ennreal_ereal).symm
  rw [h_lhs, h_rhs]

/-- If all partial sums of a nonnegative EReal sequence are bounded by M, then the tsum is bounded by M.
    This is a generalization of `ENNReal.tsum_le_of_sum_range_le` to EReal. -/
lemma EReal.tsum_le_of_sum_range_le_of_nonneg {f : ℕ → EReal} {M : EReal}
    (h_nn : ∀ n, 0 ≤ f n) (h : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n ≤ M) :
    ∑' n, f n ≤ M := by
  -- Convert to ENNReal where tsum_le_of_sum_range_le is available
  let g : ℕ → ENNReal := fun n => (f n).toENNReal
  -- Show f n = (g n : EReal) for nonneg f n
  have hf_eq : ∀ n, f n = (g n : EReal) := fun n => by
    simp only [g]
    exact (EReal.coe_toENNReal (h_nn n)).symm
  -- Rewrite tsum using term equality
  have h_tsum_eq : ∑' n, f n = (∑' n, g n : ENNReal).toEReal := by
    have h1 : ∑' n, f n = ∑' n, (g n : EReal) := tsum_congr hf_eq
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
  -- If M = ⊤, trivially true
  by_cases hM : M = ⊤
  · rw [hM]; exact le_top
  -- M ≥ 0 since it bounds nonneg partial sums
  have hM_nn : 0 ≤ M := by
    have h0 : (∑ i ∈ Finset.range 0, f i) ≤ M := h 0
    simp at h0; exact h0
  -- Get partial sum bounds in ENNReal
  have h_enn : ∀ N, ∑ i ∈ Finset.range N, g i ≤ M.toENNReal := by
    intro N
    have h_sum_eq : (∑ i ∈ Finset.range N, g i : ENNReal).toEReal = (∑ i ∈ Finset.range N, f i) := by
      rw [EReal.coe_ennreal_finset_sum]
      exact Finset.sum_congr rfl (fun n _ => (hf_eq n).symm)
    have h_le : (∑ i ∈ Finset.range N, g i : ENNReal).toEReal ≤ M := by rw [h_sum_eq]; exact h N
    rw [← EReal.coe_toENNReal hM_nn] at h_le
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h_le
  have h_tsum_enn : ∑' n, g n ≤ M.toENNReal := ENNReal.tsum_le_of_sum_range_le h_enn
  -- Convert back: ↑(∑' g) ≤ ↑(M.toENNReal) and M.toENNReal.toEReal = M (when 0 ≤ M)
  have h_coe_le : (∑' n, g n : ENNReal).toEReal ≤ (M.toENNReal).toEReal :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_tsum_enn
  calc (∑' n, g n : ENNReal).toEReal ≤ (M.toENNReal).toEReal := h_coe_le
    _ = M := EReal.coe_toENNReal hM_nn

/-- If tsum in ENNReal equals ⊤, then tsum of coerced values in EReal equals ⊤.
    Uses that ENNReal → EReal coercion is continuous and additive. -/
lemma EReal.tsum_coe_ennreal_eq_top_of_tsum_eq_top {α : Type*} {f : α → ENNReal}
    (h : ∑' i, f i = ⊤) : ∑' i, (f i : EReal) = ⊤ := by
  let φ : ENNReal →+ EReal := {
    toFun := (↑·)
    map_zero' := by simp
    map_add' := EReal.coe_ennreal_add
  }
  have h_map : φ (∑' i, f i) = ∑' i, φ (f i) :=
    Summable.map_tsum (f := f) ENNReal.summable φ continuous_coe_ennreal_ereal
  simp only [h] at h_map
  exact h_map.symm

/-- Tsum of a positive constant over an infinite type is ⊤ in EReal -/
lemma EReal.tsum_const_eq_top_of_pos {α : Type*} [Infinite α] {c : EReal} (hc : 0 < c) :
    ∑' (_ : α), c = ⊤ := by
  by_cases h_top : c = ⊤
  · -- c = ⊤: convert through ENNReal
    rw [h_top, ← EReal.coe_ennreal_top]
    apply EReal.tsum_coe_ennreal_eq_top_of_tsum_eq_top
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by simp : (⊤ : ENNReal) ≠ 0)
  · -- c is finite and positive
    have hc_nn : 0 ≤ c := le_of_lt hc
    have c_eq : c = ↑(c.toENNReal) := (EReal.coe_toENNReal hc_nn).symm
    rw [c_eq]
    have hc_ne_zero : c.toENNReal ≠ 0 := by
      intro h_eq
      rw [h_eq] at c_eq
      norm_num [ENNReal.coe_zero] at c_eq
      rw [c_eq] at hc
      norm_num at hc
    apply EReal.tsum_coe_ennreal_eq_top_of_tsum_eq_top
    exact ENNReal.tsum_const_eq_top_of_ne_zero hc_ne_zero
