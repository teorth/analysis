import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

#check Nat.mod_add_div
#check Int.ediv

example :  ∀ (m k : ℤ), m % k + k * (m / k) = m := by
  exact fun m k ↦ Int.emod_add_ediv m k

lemma Nat.exists_div_mod'' (n q : ℕ) (hq: 0 < q) :
    ∃ m r, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  use n / q, n % q
  and_intros
  grind
  exact mod_lt n hq
  rw [div_add_mod']

lemma Nat.exists_div_mod''' (n q : ℕ) (hq: 0 < q) :
    ∃! m, n = m * q + (n % q) := by
  sorry


lemma Nat.exists_div_mod (n q : ℕ) (hq: 0 < q) :
    ∃ (mr: Nat × Nat), 0 ≤ mr.2 ∧ mr.2 < q ∧ n = mr.1 * q + mr.2 := by
  use (n / q, n % q)
  and_intros
  grind
  exact mod_lt n hq
  rw [div_add_mod']

lemma Nat.exists_div_mod' (n q : ℕ) (hq: 0 < q) :
    ∃! (mr: Nat × Nat), 0 ≤ mr.2 ∧ mr.2 < q ∧ n = mr.1 * q + mr.2 := by
  use (n / q, n % q)
  and_intros
  grind
  exact mod_lt n hq
  rw [div_add_mod']

  rintro ⟨ m, r ⟩ ⟨ _, h2, h3 ⟩
  simp at h2 h3

  obtain rfl := show  m = n / q by
    have : ¬(m < n/q) := by grind [Nat.lt_div_iff_mul_lt]
    have : ¬(n/q < m) := by grind [Nat.div_lt_iff_lt_mul]
    grind

  ext <;> simp
  rw [h3]
  simp
  grind [mod_eq_of_lt]

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  by_cases h : 0 < x
  have : ∃ p q : ℕ, x = p / q ∧ q ≠ 0 := by
    use x.num.toNat, x.den
    have : (x.num.toNat : ℚ) = x.num := by
      norm_cast
      exact (Int.eq_natCast_toNat.mpr (by positivity)).symm
    rw [this]
    constructor
    exact Eq.symm (num_div_den x)
    exact x.den_nz
  obtain ⟨ p, q, h1, h2 ⟩ := this
  have := Nat.exists_div_mod' p q (by positivity)
  obtain ⟨ ⟨ m, r ⟩, ⟨  h3, h4, h5 ⟩, h6 ⟩  := this
  use m
  simp at *
  and_intros
  norm_cast
  rw [h1, h5]
  push_cast
  rw [show ((m:ℚ) * q + r) / q = ((m:ℚ) * q) / q + r / q by ring]
  rw [show ((m:ℚ) * q) / q = m by field_simp]
  simp
  positivity
  rw [h1, h5]
  push_cast
  rw [show ((m:ℚ) * q + r) / q = ((m:ℚ) * q) / q + r / q by ring]
  rw [show ((m:ℚ) * q) / q = m by field_simp]
  simp
  rw [div_lt_one_iff]
  left
  and_intros
  norm_cast
  grind
  norm_cast

  by_contra nu
  simp at nu
  obtain ⟨ n, hn1, hn2, hn3 ⟩ := nu
  repeat sorry



theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  have := Rat.between_int x
  obtain ⟨ n, ⟨ h1, h2 ⟩, h3 ⟩ := this
  by_cases h : 0 < x
  · have : 0 < (n:ℚ) + 1 := by linarith
    norm_cast at this
    lift n to ℕ using (by omega)
    norm_cast at *
    use (n + 1)

  · use 1
    norm_cast
    linarith

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  constructor <;> linarith

/-- Exercise 4.4.2 -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  sorry

def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  apply isTrue
  use fun n => -n
  intro n
  dsimp
  linarith

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  exact even_or_odd n

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  by_contra h
  obtain ⟨ ⟨x, h1⟩ , ⟨ y, h2 ⟩ ⟩ := h
  rw [h1] at h2
  clear h1
  clear n
  omega

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . have hneg : -x > 0 := by simp; order
    apply this _ _ _ hneg <;> simp [hx,hnon]
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . sorry
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      sorry
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    simp [this, hf _ (ha n)]
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  linarith [this n]

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
