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
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  sorry

def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  sorry

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  sorry

#check Nat.rec
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
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    rcases p.even_or_odd'' with hp | hp
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      obtain ⟨ q, hpos, hq ⟩ := hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q
      constructor
      . sorry
      refine ⟨ hpos, k, ?_, this ⟩
      . linarith [hPp.1]
    have h1 : Odd (p^2) := by
      sorry
    have h2 : Even (p^2) := by
      obtain ⟨ q, hpos, hq ⟩ := hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    have h3 := Nat.not_even_and_odd (p^2)
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : f p < p := by
    simp [f, hPp]
    exact (hiter p hPp).choose_spec.1
  have hf2 (p:ℕ) (pPp: P p) : P (f p) := by
    simp [f, pPp]
    exact (hiter p pPp).choose_spec.2
  obtain ⟨ p, hP ⟩ := hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact hf2 _ ih
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := Nat.rec_add_one p (fun n p ↦ f p) n
    rw [this]
    exact hf _ (ha n)
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn
    . simp
    specialize h (n*ε) (by sorry) hn
    simp [add_mul]
    apply lt_of_le_of_ne h
    have := not_exist_sqrt_two
    simp at this ⊢
    exact this _
  obtain ⟨ n, hn ⟩ := Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀' (by positivity), mul_comm,
      ←sq_lt_sq₀ (by norm_num) (by positivity)] at hn
  specialize this n
  linarith

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by
  norm_num
