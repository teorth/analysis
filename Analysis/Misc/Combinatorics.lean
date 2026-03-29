import Mathlib.Tactic

/-!
# Combinatorics utilities

General combinatorics lemmas about Fin, Finset, and boolean choices.
-/

/-- Distributive law: product of sums over Fin d equals sum over boolean choices of products.
    This is the key identity: ∏ᵢ (aᵢ + bᵢ) = ∑\_\{c : Fin d → Bool\} ∏ᵢ (if cᵢ then bᵢ else aᵢ) -/
lemma Fin.prod_add_eq_sum_prod_choice (d : ℕ) (a b : Fin d → ℝ) :
    ∏ i, (a i + b i) = ∑ c : Fin d → Bool, ∏ i, (if c i then b i else a i) := by
  induction d with
  | zero =>
    -- Empty product = 1, and there's exactly one function Fin 0 → Bool
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    have h_card : (Finset.univ : Finset (Fin 0 → Bool)).card = 1 := by simp
    rw [Finset.card_eq_one] at h_card
    obtain ⟨f, hf⟩ := h_card
    simp only [hf, Finset.sum_singleton]
  | succ d ih =>
    -- Split off first coordinate: ∏_{i:Fin(d+1)} = (first term) * ∏_{i:Fin d}
    rw [Fin.prod_univ_succ]
    -- Apply IH to the tail
    let a' : Fin d → ℝ := fun i => a i.succ
    let b' : Fin d → ℝ := fun i => b i.succ
    have h_tail : ∏ i : Fin d, (a i.succ + b i.succ) = ∏ i, (a' i + b' i) := rfl
    rw [h_tail, ih a' b']
    -- Distribute: (a 0 + b 0) * (∑ c', ...) = b 0 * (∑ c', ...) + a 0 * (∑ c', ...)
    rw [add_comm (a 0) (b 0), add_mul, Finset.mul_sum, Finset.mul_sum]
    -- Split RHS sum by first bit: ∑_c = ∑_{c 0 = true} + ∑_{c 0 = false}
    symm
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : Fin (d+1) → Bool => c 0)]
    -- Now: (∑_{c 0 = true} ...) + (∑_{c 0 = false} ...) = b 0 * (...) + a 0 * (...)
    congr 1
    · -- c 0 = true case
      have h_factor : ∀ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => c 0) Finset.univ,
          ∏ i, (if c i then b i else a i) =
          b 0 * ∏ i : Fin d, (if c i.succ then b' i else a' i) := by
        intro c hc
        rw [Fin.prod_univ_succ]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp only [hc, ↓reduceIte, a', b']
      rw [Finset.sum_congr rfl h_factor, ← Finset.mul_sum]
      -- Now goal is: b 0 * (∑ c ∈ filter, ∏...) = b 0 * (∑ c' ∈ univ, ∏...)
      -- Need to show the sums are equal, then multiply by b 0
      have h_sum_eq : ∑ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => c 0) Finset.univ,
          ∏ i : Fin d, (if c i.succ then b' i else a' i) =
          ∑ c' : Fin d → Bool, ∏ i, (if c' i then b' i else a' i) := by
        symm
        refine Finset.sum_bij (fun (c' : Fin d → Bool) _ => Fin.cons true c') ?_ ?_ ?_ ?_
        · intro c' _
          simp only [Finset.mem_filter, Finset.mem_univ, Fin.cons_zero, true_and]
        · intro c₁ _ c₂ _ heq
          simp only at heq
          funext i
          have h : (Fin.cons true c₁ : Fin (d+1) → Bool) i.succ =
                   (Fin.cons true c₂ : Fin (d+1) → Bool) i.succ := by rw [heq]
          simp only [Fin.cons_succ] at h
          exact h
        · intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          refine ⟨fun i => c i.succ, Finset.mem_univ _, ?_⟩
          funext i; cases' i using Fin.cases with i
          · simp only [Fin.cons_zero]; exact hc.symm
          · simp only [Fin.cons_succ]
        · intro c' _
          apply Finset.prod_congr rfl; intro i _
          simp only [Fin.cons_succ]
      rw [h_sum_eq, Finset.mul_sum]
    · -- c 0 = false case
      have h_factor : ∀ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => ¬c 0) Finset.univ,
          ∏ i, (if c i then b i else a i) =
          a 0 * ∏ i : Fin d, (if c i.succ then b' i else a' i) := by
        intro c hc
        rw [Fin.prod_univ_succ]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte, a', b']
      rw [Finset.sum_congr rfl h_factor, ← Finset.mul_sum]
      have h_sum_eq : ∑ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => ¬c 0) Finset.univ,
          ∏ i : Fin d, (if c i.succ then b' i else a' i) =
          ∑ c' : Fin d → Bool, ∏ i, (if c' i then b' i else a' i) := by
        symm
        refine Finset.sum_bij (fun (c' : Fin d → Bool) _ => Fin.cons false c') ?_ ?_ ?_ ?_
        · intro c' _
          simp only [Finset.mem_filter, Finset.mem_univ, Fin.cons_zero]
          trivial
        · intro c₁ _ c₂ _ heq
          simp only at heq
          funext i
          have h : (Fin.cons false c₁ : Fin (d+1) → Bool) i.succ =
                   (Fin.cons false c₂ : Fin (d+1) → Bool) i.succ := by rw [heq]
          simp only [Fin.cons_succ] at h
          exact h
        · intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          refine ⟨fun i => c i.succ, Finset.mem_univ _, ?_⟩
          funext i; cases' i using Fin.cases with i
          · simp only [Fin.cons_zero]; exact (Bool.eq_false_iff.mpr hc).symm
          · simp only [Fin.cons_succ]
        · intro c' _
          apply Finset.prod_congr rfl; intro i _
          simp only [Fin.cons_succ]
      rw [h_sum_eq, Finset.mul_sum]
