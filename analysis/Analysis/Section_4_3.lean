import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers `ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  rw [abs_of_neg hlt, _root_.abs_of_neg hlt]
  rw [heq, abs_zero]
  simp
  rw [abs_of_pos hgt, _root_.abs_of_pos hgt]

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by 
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  rw [← abs_eq_abs, abs_of_neg hlt]
  linarith
  rw [heq, ← abs_eq_abs, abs_of_zero]
  rw [← abs_eq_abs, abs_of_pos hgt]
  linarith

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by 
  constructor
  intro h
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  rw [← abs_eq_abs, abs_of_neg hlt] at h
  linarith
  exact heq
  rw [← abs_eq_abs, abs_of_pos hgt] at h
  linarith
  intro h
  rw [h, ← abs_eq_abs, abs_of_zero]

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by 
  · -- Cas x < 0
    rw[← abs_eq_abs, ← abs_eq_abs, abs_of_neg hlt, ← abs_eq_abs]
    rcases lt_trichotomy y 0 with hlt' | heq' | hgt'
    · -- Cas y < 0
      rw [abs_of_neg (add_neg hlt hlt'), abs_of_neg hlt']
      linarith
    · -- Cas y = 0
      rw [heq', abs_of_zero,add_zero,abs_of_neg hlt]
      linarith
    · -- Cas y > 0
      rw [abs_of_pos hgt']
      by_cases hsum_neg : x + y < 0
      · -- Cas x + y < 0
        rw[abs_of_neg hsum_neg]
        linarith
      · -- Cas x + y ≥ 0
        simp at hsum_neg
        by_cases hsum_zero : x + y = 0
        · -- Cas x + y = 0
          rw [hsum_zero, abs_of_zero]
          linarith
        · -- Cas x + y > 0
          rw [← ne_eq] at hsum_zero; symm at hsum_zero
          rw [abs_of_pos (lt_of_le_of_ne hsum_neg hsum_zero)]
          linarith
        
  · -- Cas x = 0
    rw [heq, ← abs_eq_abs, zero_add, ← abs_eq_abs, abs_of_zero, abs_eq_abs, zero_add]
    
  · -- Cas x > 0
    rw [← abs_eq_abs, ← abs_eq_abs, abs_of_pos hgt, ← abs_eq_abs]
    rcases lt_trichotomy y 0 with hlt' | heq' | hgt'
    · -- Cas y < 0
      by_cases hsum_neg : x + y < 0
      · -- Cas x + y < 0
        rw [abs_of_neg hlt', abs_of_neg hsum_neg]
        linarith
      · -- Cas x + y ≥ 0
        simp at hsum_neg
        by_cases hsum_zero : x + y = 0
        · -- Cas x + y = 0
          rw [hsum_zero, abs_of_zero, abs_of_neg hlt']
          linarith
        · -- Cas x + y > 0
          rw [← ne_eq] at hsum_zero; symm at hsum_zero
          rw [abs_of_pos (lt_of_le_of_ne hsum_neg hsum_zero), abs_of_neg hlt']
          linarith
    · -- Cas y = 0
      rw [heq', abs_of_zero,add_zero,abs_of_pos hgt]
    · -- Cas y > 0
      rw [abs_of_pos (add_pos hgt hgt'), abs_of_pos hgt']

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by 
  constructor
  intro ⟨h1, h2⟩
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · -- Cas x < 0
    rw [← abs_eq_abs, abs_of_neg hlt]
    linarith
  · -- Cas x = 0
    rw [heq, ← abs_eq_abs, abs_of_zero]
    linarith
  · -- Cas x > 0
    rw [← abs_eq_abs, abs_of_pos hgt]
    linarith
  intro h
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · -- Cas x < 0
    rw [← abs_eq_abs, abs_of_neg hlt] at h
    constructor
    linarith
    linarith
  · -- Cas x = 0
    rw [heq, ← abs_eq_abs, abs_of_zero] at h
    constructor
    linarith
    linarith
  · -- Cas x > 0
    rw [← abs_eq_abs, abs_of_pos hgt] at h
    constructor
    linarith
    linarith

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by 
  constructor
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · -- Cas x < 0
    rw [← abs_eq_abs, abs_of_neg hlt]
    linarith
  · -- Cas x = 0
    rw [heq, ← abs_eq_abs, abs_of_zero]
    linarith
  · -- Cas x > 0
    rw [← abs_eq_abs, abs_of_pos hgt]
    linarith
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · -- Cas x < 0
    rw [← abs_eq_abs, abs_of_neg hlt]
    linarith
  · -- Cas x = 0
    rw [heq, ← abs_eq_abs, abs_of_zero]
  · -- Cas x > 0
    rw [← abs_eq_abs, abs_of_pos hgt]

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by 
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- Cas x < 0
    rw[← abs_eq_abs, ← abs_eq_abs,← abs_eq_abs, abs_of_neg hx]
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · -- Cas y < 0 
      rw [abs_of_neg hy, abs_of_pos (mul_pos_of_neg_of_neg hx hy)]
      linarith
    · -- Cas y = 0
      simp
    · -- Cas y > 0 
      rw [abs_of_pos hy, abs_of_neg (mul_neg_of_neg_of_pos hx hy)]
      linarith
  · -- Cas x = 0
    simp
  · -- Cas x > 0
    rw [← abs_eq_abs,← abs_eq_abs,← abs_eq_abs,abs_of_pos hx]
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · -- Cas y < 0
      rw [abs_of_neg hy, abs_of_neg (mul_neg_of_pos_of_neg hx hy)]
      linarith
    · -- Cas y = 0
      simp
    · -- Cas y > 0 
      rw [abs_of_pos hy, abs_of_pos (mul_pos hx hy)]

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by 
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · -- Cas x < 0
    have hneg_pos : -x > 0 := by linarith
    rw [← abs_eq_abs, ← abs_eq_abs, abs_of_pos hneg_pos, abs_of_neg hlt]
  · -- Cas x = 0
    simp
  · -- Cas x > 0
    have hneg_neg : -x < 0 := by linarith
    rw [← abs_eq_abs,← abs_eq_abs, abs_of_neg hneg_neg, abs_of_pos hgt]
    linarith

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by 
  rw[dist_eq]
  exact abs_nonneg (x-y)

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw[dist_eq, abs_eq_zero_iff]
  exact sub_eq_zero

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by 
  rw[dist_eq,dist_eq]
  rw[Eq.symm (neg_sub y x)]
  exact abs_neg (y-x)

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by 
  rw[dist_eq, dist_eq, dist_eq]
  calc
    |x - z| = |x - y + (-( z - y))| := by simp
          _ ≤ |x - y| + |-( z - y)| := by exact abs_add (x-y) (-(z-y))
          _ = |x - y| + |y - z| := by simp only [abs_neg (z-y),dist_symm]
          _ = dist x y + dist y z:= by rw[← dist_eq]

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by 
  rw[close_iff]
  calc
     |(0.99 : ℚ) - (1.01 : ℚ)| ≤  |(0.1 : ℚ)| := by 
         norm_num; 
         rw[← abs_eq_abs, ← abs_eq_abs, abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
         norm_num
                             _ = 0.1 := by rw[← abs_eq_abs, abs_of_pos (by norm_num)]

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by 
  rw[close_iff]
  by_contra h
  have hh :  |(0.99 : ℚ) - (1.01 : ℚ)| > (0.01:ℚ) := by
      calc
       |(0.99 : ℚ) - (1.01 : ℚ)| =   |(0.02 : ℚ)| := by norm_num; 
                               _ = (0.02 : ℚ) := by  rw[← abs_eq_abs, abs_of_pos (by norm_num)]
                               _ > (0.01:ℚ)  := by norm_num
  linarith

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by 
  rw[close_iff]
  simp
  exact le_of_lt hε

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by 
   rw[close_iff]
   simp

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by 
   constructor
   intro h
   intro ε hε
   rw[close_iff,h]
   simp
   exact le_of_lt hε
   intro h
   by_contra hn
   have hh : (1/2)* |x - y| > 0 := by 
      simp
      exact sub_ne_zero_of_ne hn
   specialize h ((1/2)*|x - y|) hh
   rw[close_iff] at h
   have hc : (1/2)*|x - y| <  |x - y| := by 
     refine mul_lt_of_lt_one_left ?_ ?_
     simp
     linarith
     norm_num
   linarith

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by 
  constructor
  intro h
  rw[close_iff, ← dist_eq] at *
  rw[dist_symm]
  exact h
  intro h
  rw[close_iff, ← dist_eq] at *
  rw[dist_symm]
  exact h

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by 
    rw[close_iff] at *
    rw[← dist_eq] at *
    calc
       dist x z ≤ dist x y + dist y z := by exact dist_le x y z
              _ ≤ ε + δ := by linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by 
    rw[close_iff] at *
    calc
       |x + z - (y + w)| = |(x - y) + (z - w)| := by congr; linarith
                       _ ≤ |x - y| + |z - w| := by exact abs_add (x-y) (z-w)
                       _ ≤ ε + δ := by linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by 
   rw[close_iff] at *
   calc
       |x - z - (y - w)| = |(x - y) + (- (z - w))| := by congr; linarith
                       _ ≤ |x - y| + |-(z - w)| := by exact abs_add (x-y) (-(z - w))
                       _ = |x - y| + |z - w| := by simp only[abs_neg]
                       _ ≤ ε + δ := by linarith

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by 
  rw[close_iff] at *
  linarith

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by 
  rw [close_iff] at *
  rw [abs_le] at *
  rcases hbetween with ⟨hyw, hwz⟩ | ⟨hzw, hwy⟩
  constructor
  linarith
  linarith
  constructor
  linarith
  linarith

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by 
   rw [close_iff] at *
   calc
      |x * z - y * z| = |(x - y) * z| := by ring_nf
                    _ = |x - y| * |z| := by exact abs_mul (x-y) z
                    _ ≤ ε * |z| := by apply mul_le_mul_of_nonneg hxy ?_ ?_ ?_; linarith; exact abs_nonneg (x-y); exact abs_nonneg z

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
   rw [close_iff] at *
   calc 
       |x * z - y * w| = |(x - y) * z + (z - w) * y| := by ring_nf
                     _ ≤ |(x - y) * z| + |(z - w) * y| := by exact abs_add ((x - y) * z) ((z - w) * y)
                     _ = |x - y| * |z| + |z - w| * |y| := by simp only[abs_mul]
                     _ ≤ ε * |z| + δ * |y| := by gcongr

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := rfl

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by 
  induction n with
  | zero =>
    rw [pow_zero, one_mul, zero_add]
  | succ k ih =>
    rw [pow_succ, mul_assoc, mul_comm, mul_assoc, mul_comm (x ^ m) (x ^ k),ih ,mul_comm, ← pow_succ, add_assoc, add_comm m 1, ← add_assoc]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by 
   induction m with
   | zero =>
    rw [pow_zero, mul_zero, pow_zero]
   | succ k ih =>
     rw[pow_succ, ih, pow_add]
     nth_rewrite 2[← mul_one n]
     rw[← mul_add]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by 
   induction n with
   | zero =>
    rw[pow_zero, pow_zero, pow_zero, mul_one]
   | succ k ih =>
      rw[pow_succ, ih, mul_assoc, mul_comm x y, ← mul_assoc (y ^ k) y x, ← pow_succ, mul_comm (y ^ (k + 1)) x, ← mul_assoc, ← pow_succ]

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by sorry

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by 
   induction n with
   | zero =>
    rw[pow_zero]
    norm_num
   | succ k ih =>
    rw[pow_succ]
    exact Rat.mul_nonneg ih hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by 
   induction n with
   | zero =>
    rw[pow_zero]
    norm_num
   | succ k ih =>
    rw[pow_succ]
    exact Left.mul_pos ih hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by 
   induction n with
   | zero =>
    rw[pow_zero, pow_zero]
   | succ k ih =>
    rw[pow_succ,pow_succ]
    refine mul_le_mul_of_nonneg ih hxy ?_ ?_
    exact pow_nonneg k hy
    linarith

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by sorry

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by 
   induction n with
   | zero =>
    rw[pow_zero, pow_zero, ← abs_eq_abs, abs_of_pos (by norm_num)]
   | succ k ih =>
    rw[pow_succ, ih, ← abs_mul, ← pow_succ]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by sorry

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by sorry

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by sorry

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by sorry

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by sorry

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  sorry

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  sorry

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := by sorry

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by 
  induction N with
  | zero =>
    rw [pow_zero]
    norm_num
  | succ k ih =>
    rw [pow_succ]
    have h_split :  2^k * (2 : ℚ) = 2^k + 2^k := by ring
    rw [h_split]
    have h_one : (2 : ℚ)^k ≥ 1 := by
      cases k with
      | zero =>
        rw [pow_zero]
      | succ k' =>
        apply le_trans _ ih 
        norm_num    
    norm_cast at *
    linarith
