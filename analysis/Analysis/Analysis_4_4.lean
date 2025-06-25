import Mathlib.Tactic

/-!
# Analysis I, Section 4.4

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.
-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/

theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  sorry

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  sorry

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find quicker proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h
    positivity
  constructor
  . replace h' := add_lt_add_right h' (x/2)
    convert h' using 1
    all_goals ring
  replace h' := add_lt_add_right h' (y/2)
  convert h' using 1
  all_goals ring

/-- Exercise 4.4.2 -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a n < a (n+1) := by
  sorry

def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a n < a (n+1)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  sorry

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  obtain ⟨ x, hx ⟩ := h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . have hneg : -x > 0 := by
      contrapose! hpos; contrapose! hnon; linarith
    specialize this (-x) (by simp [hx]) (by simp [hnon]) hneg
    assumption
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    have hnum_pos : x.num > 0 := num_pos.mpr hpos
    have hden_pos : x.den > 0 := den_pos x
    refine ⟨ ?_, hden_pos, ?_ ⟩
    . simp [hpos]
    rw [←num_div_den x] at hx
    field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx
    norm_cast at hx
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by
    obtain ⟨ p, q, hp, hq, hpq ⟩ := hrep
    use p
    refine ⟨ hp, q, hq, hpq ⟩
  have hiter (p:ℕ) : P p → ∃ q, q < p ∧ P q := by
    rcases p.even_or_odd'' with hp | hp
    . sorry
    sorry
  sorry





end Chapter4
