import Mathlib

/-! A solution to Erdos problem \#987.  It is convenient to rephrase things using
elements $$z_j = e(x_j)$$ on the unit circle, and to index the sequence starting from 0
rather than 1, for greater compatibility with Mathlib.

The proof follows the second proof given in https://www.erdosproblems.com/987
 -/

open Filter Complex Finset

theorem Erdos_987 (z: ℕ → Circle) :
  atTop.limsup (fun k:ℕ ↦ atTop.limsup (fun n:ℕ ↦ (‖∑ j ∈ range n, ((z j)^k:ℂ)‖:EReal) )) = ⊤ := by
  generalize hC : atTop.limsup (fun k:ℕ ↦ atTop.limsup (fun n:ℕ ↦ (‖∑ j ∈ range n, ((z j)^k:ℂ)‖:EReal) )) = C
  by_contra! h
  have : 0 ≤ C := by
    subst hC
    apply_rules [le_limsup_of_frequently_le', Frequently.of_forall]; intro k
    apply_rules [le_limsup_of_frequently_le', Frequently.of_forall]; intro n
    positivity
  replace : C ≠ ⊥ := by contrapose! this; simp_all
  lift C to ℝ using (by tauto)
  have hC' : (C:EReal) < (C+1:ℝ) := by norm_cast; linarith
  rw [←hC] at hC'; clear hC h this
  replace hC' := eventually_lt_of_limsup_lt hC'; rw [eventually_atTop] at hC'
  choose k₀ hk₀ using hC'
  replace hk₀ : ∀ k ≥ k₀, ∃ N, ∀ n ≥ N, ‖∑ j ∈ range n, ((z j)^k:ℂ)‖ < C+1 := by
    peel hk₀ with k _ hk₀
    replace hk₀ := eventually_lt_of_limsup_lt hk₀; rw [eventually_atTop] at hk₀
    peel hk₀ with N _ n hn; norm_cast at hn
  choose N hN using hk₀
  replace hN (K:ℕ) : ∃ w : ℕ → Circle, ∀ n, ∀ k ≤ K, k ≥ k₀ → ‖∑ j ∈ range n, ((w j)^k:ℂ)‖ < 2*(C+1) := by
    let N₀ := ∑ k ≤ K, if h:k ≥ k₀ then N k h else 0
    use (fun j ↦ z (N₀+j)); simp; intro n k hk hk₀
    have hN₀ : N k hk₀ ≤ N₀ := by
      convert single_le_sum (a:=k) _ _ <;> try simp [hk, hk₀]
      infer_instance
    calc
      _ = ‖∑ j ∈ range (N₀+n), ((z j)^k:ℂ) - ∑ j ∈ range N₀, ((z j)^k:ℂ)‖ := by
        rw [sum_range_add_sub_sum_range]
      _ ≤ ‖∑ j ∈ range (N₀+n), ((z j)^k:ℂ)‖ + ‖∑ j ∈ range N₀, ((z j)^k:ℂ)‖ := norm_sub_le _ _
      _ < (C+1) + (C+1) := by gcongr <;> apply hN <;> linarith
      _ = _ := by ring
  generalize hC : 2*(C+1) = C'; rw [hC] at hN; clear N z hC C
  have (n K:ℕ) : n*K^2 ≤ K^2 * (C')^2 + K*((2*k₀)*n^2) := by
    specialize hN K; choose w hw using hN
    calc
    _ = ∑ x ∈ range n, (K:ℝ)^2 := by simp
    _ = ∑ j ∈ range n, ∑ j' ∈ range n, (if j = j' then (K:ℝ)^2 else 0) := by
      apply sum_congr rfl; aesop
    _ ≤ ∑ j ∈ range n, ∑ j' ∈ range n, ‖∑ k ∈ range K, (((w j)^k:ℂ) / ((w j')^k:ℂ))‖^2 := by
      apply sum_le_sum; intro j _; apply sum_le_sum; intro j' _
      split_ifs with h <;> simp [h]
    _ = ∑ k ∈ range K, ∑ k' ∈ range K, ‖∑ j ∈ range n, (((w j)^k:ℂ) / ((w j)^(k'):ℂ) )‖^2 := by
      simp_rw [←normSq_eq_norm_sq, ←ofReal_inj, ofReal_sum, normSq_eq_conj_mul_self, map_sum, sum_mul_sum, sum_comm (s := range n) (t := range K)]
      apply sum_congr rfl; intro k _; apply sum_congr rfl; intro k' _
      apply sum_congr rfl; intro j _; apply sum_congr rfl; intro j' _
      simp only [map_pow, map_mul, map_div₀]
      field_simp
      ring_nf
      simp [← Circle.coe_inv_eq_conj]
    _ ≤ ∑ k ∈ range K, ∑ k' ∈ range K, ((C')^2 + (if k < k' + k₀ ∧ k' < k + k₀ then n^2 else 0)) := by
      apply sum_le_sum; intro k hk; apply sum_le_sum; intro k' hk'; simp at hk hk'
      split_ifs with h
      . calc
          _ ≤ (n:ℝ)^2 := by apply pow_le_pow_left₀ (by positivity); convert norm_sum_le _ _; simp
          _ ≤ _ := by simp; nlinarith
      simp; apply pow_le_pow_left₀ (by positivity)
      replace h : (∃ l ≥ k₀, k = k' + l) ∨ (∃ l ≥ k₀, k' = k + l) := by
        have : k' + k₀ ≤ k ∨ k + k₀ ≤ k' := by omega
        rcases this with _ | _
        . left; use k-k'; omega
        right; use k'-k; omega
      rcases h with ⟨ l, hl, rfl ⟩ | ⟨ l, hl, rfl ⟩
      . convert le_of_lt (hw n l ?_ hl) with j hj; field_simp; grind; omega
      rw [←norm_conj, map_sum]
      convert le_of_lt (hw n l ?_ hl) with j hj
      simp [←Circle.coe_inv_eq_conj]; field_simp; grind; omega
    _ ≤ _ := by
      simp [sum_add_distrib]; gcongr 1
      . grind
      calc
        _ ≤ ∑ k ∈ range K, ((2*k₀)*n^2:ℝ) := by
          apply sum_le_sum; intro k hk
          simp [←sum_filter]; gcongr; norm_cast
          convert card_le_card_of_injOn (t := range (2*k₀)) (fun a ↦ a+k₀-k) _ _
          . simp
          . intro a; grind
          intro a b _; grind
        _ = _ := by simp
  clear hN; obtain ⟨ n, hn ⟩ := exists_nat_gt ((C')^2 + 1)
  let K := 2*k₀*n^2 + 1; specialize this n K
  have : n * K ^ 2 > K ^ 2 * C' ^ 2 + K * ((2 * k₀) * n ^ 2) := calc
    _ > ((C')^2 + 1) * K ^ 2 := by gcongr
    _ = K^2 * C'^2 + K * K := by ring
    _ ≥ _ := by gcongr; simp [K]
  order
