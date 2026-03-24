import Mathlib.Data.Nat.BitIndices
import Mathlib.Combinatorics.Colex

/-!
# Additional lemmas for natural number bit operations

This file contains general-purpose lemmas about `Nat.testBit`, `Nat.bitIndices`,
and sums of powers of 2 that are used throughout the formalization.

## Main results

* `Nat.testBit_iff_mem_bitIndices`: `n.testBit i = true ↔ i ∈ n.bitIndices`
* `Nat.testBit_finset_sum_pow_two`: For a finset `s` of natural numbers,
  `(∑ i ∈ s, 2^i).testBit j ↔ j ∈ s`
* `Nat.testBit_sum_pow_two_fin`: Same for `Finset (Fin k)`

These lemmas connect the bit representation of natural numbers with finset membership,
which is fundamental for binary encoding arguments.
-/

namespace Nat

/-- `n.testBit i = true` if and only if `i` appears in `n.bitIndices`.
    This connects the pointwise bit test with the list of set bit positions. -/
lemma testBit_iff_mem_bitIndices (n i : ℕ) :
    n.testBit i = true ↔ i ∈ n.bitIndices := by
  constructor
  · intro h
    induction n using Nat.binaryRec generalizing i with
    | zero => simp at h
    | bit b n ih =>
      cases b
      · simp only [Nat.bit_false, Nat.bitIndices_two_mul, List.mem_map]
        rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hpos
        · simp at h
        · have hi_succ : i = (i - 1) + 1 := (Nat.sub_add_cancel hpos).symm
          rw [hi_succ, Nat.testBit_bit_succ] at h
          exact ⟨i - 1, ih _ h, hi_succ.symm⟩
      · simp only [Nat.bit_true, Nat.bitIndices_two_mul_add_one, List.mem_cons, List.mem_map]
        rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hpos
        · left; rfl
        · right
          have hi_succ : i = (i - 1) + 1 := (Nat.sub_add_cancel hpos).symm
          rw [hi_succ, Nat.testBit_bit_succ] at h
          exact ⟨i - 1, ih _ h, hi_succ.symm⟩
  · intro h
    induction n using Nat.binaryRec generalizing i with
    | zero => simp at h
    | bit b n ih =>
      cases b
      · simp only [Nat.bit_false, Nat.bitIndices_two_mul, List.mem_map] at h
        obtain ⟨j, hj, rfl⟩ := h
        rw [Nat.testBit_bit_succ]
        exact ih _ hj
      · simp only [Nat.bit_true, Nat.bitIndices_two_mul_add_one, List.mem_cons, List.mem_map] at h
        rcases h with rfl | ⟨j, hj, rfl⟩
        · simp
        · rw [Nat.testBit_bit_succ]
          exact ih _ hj

/-- `testBit` of a sum of distinct powers of 2 equals membership in the index set.
    For a finset `s` of natural numbers, `(∑ i ∈ s, 2^i).testBit j = true ↔ j ∈ s`. -/
lemma testBit_finset_sum_pow_two {s : Finset ℕ} {i : ℕ} :
    (s.sum (2^·)).testBit i = true ↔ i ∈ s := by
  rw [testBit_iff_mem_bitIndices]
  constructor
  · intro h
    have : i ∈ (s.sum (2^·)).bitIndices.toFinset := List.mem_toFinset.mpr h
    rw [Finset.toFinset_bitIndices_twoPowSum] at this
    exact this
  · intro h
    have : i ∈ (s.sum (2^·)).bitIndices.toFinset := by
      rw [Finset.toFinset_bitIndices_twoPowSum]
      exact h
    exact List.mem_toFinset.mp this

/-- `testBit` of a sum of `2^j` over `Finset (Fin k)` equals membership.
    This is the `Fin`-indexed version of `testBit_finset_sum_pow_two`. -/
lemma testBit_sum_pow_two_fin {k : ℕ} {s : Finset (Fin k)} (j : Fin k) :
    (s.sum fun i => (2:ℕ)^i.val).testBit j.val ↔ j ∈ s := by
  have h : s.sum (fun i => (2:ℕ)^i.val) = (s.image (·.val)).sum (2^·) := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact Fin.val_injective hxy
  rw [h, testBit_finset_sum_pow_two]
  simp only [Finset.mem_image]
  constructor
  · intro ⟨x, hx, hxj⟩
    rw [← Fin.val_injective hxj]
    exact hx
  · intro hj
    exact ⟨j, hj, rfl⟩

end Nat
