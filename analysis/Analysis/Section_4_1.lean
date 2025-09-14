import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by
      intro ⟨a, b⟩
      rw [Nat.add_left_cancel_iff]
    symm := by
      intro ⟨a, b⟩ ⟨c, d⟩ h
      linarith
    trans := by
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2
      simp at h1 h2 ⊢
      have h3 := congrArg₂ (· + ·) h1 h2
      simp at h3
      omega
    }

@[simp]
theorem PreInt.equiv (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

/--
(a+b) —— (b+c) ≃ (a+d) —— (d+c)
-/
example (a b c d: ℕ) : (⟨ a + b, b + c ⟩ : PreInt) ≈ (⟨ a + d, d + c ⟩ : PreInt) := by
  rw [PreInt.equiv]
  omega

example : 3 + 5 = 5 + 3 := rfl

def five_minus_three : PreInt := ⟨ 5, 3 ⟩
def six_minus_four : PreInt := ⟨ 6, 4 ⟩
def six_minus_three : PreInt := ⟨ 6, 3 ⟩
example : five_minus_three ≈ six_minus_four := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ) : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
@[simp high, grind]
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp at *
    omega
)

/-- Note: the operator precedence is parsed as (a —— b) + (c —— d)  -/
@[simp, grind]
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

theorem Int.add_comm : ∀ a b: Int, a + b = b + a := by
    intro a b
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    simp
    omega

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at h ⊢
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at h ⊢
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
@[simp, grind]
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) :=
  Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp high]
theorem Int.natCast_inj (n m:ℕ) :
    (n : Int) = (m : Int) ↔ n = m := by
      simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
@[grind]
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  exact ofNat_inj n 0


/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro a b h
    dsimp
    rw [Int.eq]
    whnf at h
    linarith
  )

@[simp]
theorem Int.neg_eq (a b:ℕ) : -(a——b) = b——a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, hn, hn' ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, hn, hn' ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn'
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, hn, rfl ⟩, ⟨ m, hm, hm' ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm'
  linarith

@[simp]
theorem Int.eq_0' (a b : ℕ) : a ——b = 0 ↔ a = b := by
  rw [show (0 : Int) = 0 —— 0 by rfl]
  grind

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
AddGroup.ofLeftAxioms (by
  intro a b c
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
  obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
  grind
) (by
  intro a
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [show (0 : Int) = 0 —— 0 by rfl]
  simp
) (by
  intro a
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  simp only [neg_eq, add_eq, eq_0']
  omega
)

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := add_comm

@[grind]
lemma Int.mul_comm (x y : Int) : x * y = y * x := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, rfl ⟩ := eq_diff y
  grind

lemma Int.one_mul (x : Int) : 1 * x = x := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  rw [show (1 : Int) = 1 —— 0 by rfl]
  simp

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := mul_comm
  mul_assoc := by
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp only [mul_eq, eq]
    grind
  one_mul := by
    intro a
    exact one_mul a
  mul_one := by
    intro a
    have := one_mul a
    grind

lemma Int.zero_mul (x : Int) : 0 * x = 0 := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  rw [show (0 : Int) = 0 —— 0 by rfl]
  simp

@[grind]
lemma Int.left_distrib (x y z : Int) : x * (y + z) = x * y + x * z := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, rfl ⟩ := eq_diff z
  simp only [mul_eq, add_eq, eq]
  ring

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := left_distrib
  right_distrib x y z:= by
    grind
  zero_mul := zero_mul
  mul_zero := by
    intro a
    have := zero_mul a
    grind

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  obtain ⟨ x, y, h1 ⟩ := eq_diff a
  obtain ⟨ p, q, h2 ⟩ := eq_diff b
  rw [h1, h2, sub_eq, neg_eq, add_eq, eq]
  rw [natCast_eq, eq] at h1 h2
  omega

-- a rearrangement-type inequality on ℕ
lemma test (x y p q : ℕ)
(h : x * p + y * q = x * q + y * p) : x = y ∨ p = q := by
  by_cases h2 : p ≤ q
  · have h3 : q = p + (q - p) := by grind
    have eq3 : y * (q - p) = x * (q - p) := by grind
    grind [mul_left_inj']
  · have h5 : p = q + (p - q) := by grind
    have eq3 : x * (p - q) = y * (p - q) := by grind
    grind [mul_left_inj']

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨ x, y, h1 ⟩ := eq_diff a
  obtain ⟨ p, q, h2 ⟩ := eq_diff b
  rw [show (0 : Int) = 0 —— 0 by rfl] at h
  grind [eq_0', test]


/- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have : a * c - b * c = b * c - b * c := by congr
  simp at this
  have : (a - b) * c = 0 := by
    ring_nf
    exact this
  have := mul_eq_zero this
  rcases this with h | h
  have : (a - b) + b = 0 + b := by congr
  ring_nf at this
  exact this
  trivial

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  constructor
  · intro h
    rw [lt_iff] at h
    rcases h.1 with ⟨ c, hc ⟩
    use c
    constructor
    · rintro rfl
      grind [Nat.cast_zero, add_zero]
    · exact hc
  rintro ⟨ n, ⟨h1, h2⟩  ⟩
  rw [lt_iff]
  constructor
  · use n
  · grind [left_eq_add, natCast_eq]

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [lt_iff] at *
  rcases h with ⟨ ⟨ n, h3 ⟩, h2⟩
  constructor
  use n
  all_goals grind

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff_exists_positive_difference] at *
  rcases hab with ⟨ n, ⟨hn1, hn2⟩⟩
  rcases hc with ⟨ m, ⟨hm1, hm2⟩⟩
  use n * m
  constructor
  · positivity
  · grind [zero_add, Nat.cast_mul]

theorem Int.mul_le_mul_of_nonneg_right {a b c:Int} (hab : a ≤ b) (hc: 0 ≤ c) : a*c ≤ b*c := by
  rw [le_iff] at *
  rcases hab with ⟨ w, hw ⟩
  rcases hc with ⟨ d, hd ⟩
  use w*d
  rw [hw, hd]
  ring_nf
  norm_cast

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [lt_iff_exists_positive_difference] at h
  rcases h with ⟨ n, ⟨hn1, hn2⟩⟩
  rw [lt_iff]
  constructor
  · use n
    grind
  · rw [hn2]
    intro h
    ring_nf at h
    have h' : (-b - ↑n) + b = -b + b := by
      rw [h]
    rw [show  -(b : Int) + b = 0 by ring] at h'
    rw [show -(b : Int) - n + b = -n by ring] at h'
    grind [natCast_eq]

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  rcases h with ⟨ n, h ⟩
  use n
  rw [h]
  ring

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff_exists_positive_difference] at *
  rcases hab with ⟨ n, ⟨hn1, hn2⟩⟩
  rcases hbc with ⟨ m, ⟨hm1, hm2⟩⟩
  use n + m
  grind [Nat.cast_add]

lemma Int.lt_iff_gt_0 { a b : Int } : a < b ↔ 0 < (b - a) := by
  constructor
  intro h
  have := add_lt_add_right (-a) h
  ring_nf at this
  rw [show -a + b = b - a by ring] at this
  exact this

  intro h
  have := add_lt_add_right a h
  ring_nf at this
  exact this

lemma Int.lt_iff_lt_0 { a b : Int } : a < b ↔ a - b < 0 := by
  constructor
  intro h
  have := add_lt_add_right (-b) h
  ring_nf at this
  grind

  intro h
  have := add_lt_add_right b h
  ring_nf at this
  exact this

lemma Int.pos_iff_gt_0 {a : Int} : a.IsPos ↔ 0 < a := by
  constructor
  · intro h
    rcases h with ⟨ w, hw ⟩
    constructor
    · use w
      grind
    · by_contra h
      have := cast_eq_0_iff_eq_0
      grind

  · intro h
    rw [lt_iff] at h
    obtain ⟨ w, hw ⟩ := h.1
    use w
    constructor
    · simp at hw
      have := cast_eq_0_iff_eq_0
      grind
    · grind

lemma Int.neg_iff_lt_0 {a : Int} : a.IsNeg ↔ a < 0 := by
  constructor
  intro h
  rcases h with ⟨ w, hw ⟩
  constructor
  · use w
    grind
  · by_contra h
    have := cast_eq_0_iff_eq_0
    grind

  intro h
  rw [lt_iff] at h
  obtain ⟨ w, hw ⟩ := h.1
  use w
  constructor
  · have := cast_eq_0_iff_eq_0
    grind
  · grind

lemma Int.trichotomous0 (a :Int) : a = 0 ∨ 0 < a ∨ a < 0 := by
  have := trichotomous a
  rwa [pos_iff_gt_0, neg_iff_lt_0] at this

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  rw [lt_iff_gt_0]
  rw [show a > b ↔ b < a by rfl, lt_iff_gt_0]
  have := trichotomous0 (a - b)
  obtain h | h | h := this
  · grind
  · grind
  · right
    left
    rw [← lt_iff_gt_0]
    -- grind [lt_iff_lt_0] why no work
    rwa [← lt_iff_lt_0] at h

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  intro h
  apply not_pos_neg (b - a)
  rw [pos_iff_gt_0, neg_iff_lt_0, ← lt_iff_gt_0, ← lt_iff_lt_0]
  tauto

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  rintro h
  apply not_pos_zero (b - a)
  rw [pos_iff_gt_0, ← lt_iff_gt_0]
  grind

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  rintro h
  apply not_neg_zero (a - b)
  rw [neg_iff_lt_0, ← lt_iff_lt_0]
  grind

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (a b : Int) : (a = a + b) ↔ b = 0 := by
  constructor
  intro h
  rw (occs := .pos [1]) [show a = a + 0 by exact Eq.symm (add_zero a)] at h
  simpa using h
  intro h
  simp [h]

/-- Order is anti-symmetric  -/
theorem Int.le_antisymm {a b : Int} (hab: a ≤ b) (hba: b ≤ a) : a = b := by
  rw [le_iff] at hab
  rcases hab with ⟨d, hd⟩
  rcases hba with ⟨e, he⟩
  rw [hd] at he
  rw [add_assoc] at he
  rw [is_additive_identity_iff_eq_0] at he
  norm_cast at he
  rw [cast_eq_0_iff_eq_0] at he
  rw [Nat.add_eq_zero] at he
  rcases he with ⟨rw1, rw2⟩
  rw [rw1] at hd
  simp at hd
  exact Eq.symm hd

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        let n := b + c - (a + d)
        use n
        rw [natCast_eq, add_eq, eq, show n = (b + c - (a + d)) by rfl]
        grind
      | isFalse h =>
        apply isFalse
        by_contra h2
        obtain ⟨ m, hm ⟩ := h2
        rw [natCast_eq, add_eq, eq] at hm
        grind
  exact Quotient.recOnSubsingleton₂ n m this

theorem Int.lt_of_le_of_lt {a b c : Int} (hab: a ≤ b) (hbc: b < c) : a < c := by
  rw [lt_iff_exists_positive_difference] at *
  rcases hab with ⟨d, hd⟩
  rcases hbc with ⟨e, he1, he2⟩
  use d + e
  constructor
  . omega
  . push_cast
    rw [he2, hd, add_assoc]

theorem Int.ne_of_lt (a b:Int) : a < b → a ≠ b := by
  intro h; exact h.2

@[grind]
lemma Int.le_of_lt {n m:Int} (hnm: n < m) : n ≤ m := by
  rw [lt_iff_exists_positive_difference] at hnm
  rcases hnm with ⟨ d, ⟨hd1, hd2⟩⟩
  use d

/-- If a > b and a < b then contradiction -/
@[grind]
theorem Int.not_lt_of_gt (a b:Int) : a < b ∧ a > b → False := by
  intro h
  have h1 := h.1
  have h2 := h.2
  have h2 : b < a := by exact h2
  have h1' := Int.le_of_lt h1
  have h2' := Int.le_of_lt h2
  grind [Int.ne_of_lt, le_antisymm]

theorem Int.not_lt_self {a: Int} (h : a < a) : False := by
  grind

lemma Int.le_iff_lt_or_eq {a b: Int} : a ≤ b ↔ a < b ∨ a = b := by
  constructor
  · intro h
    obtain ⟨ t, ht ⟩ := h
    by_cases h : t = 0
    right
    rw [h] at ht
    grind [Nat.cast_zero, add_zero]
    left
    constructor
    exact ⟨ t, ht ⟩
    rintro rfl
    simp at ht
    rw [cast_eq_0_iff_eq_0] at ht
    exact h ht
  · intro h
    obtain h | rfl := h
    exact le_of_lt h
    use 0
    simp


/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by
    intro a
    use 0
    simp
  le_trans := by
    intro a b c hab hbc
    rcases hab with ⟨ n, ⟨hn1, hn2⟩⟩
    rcases hbc with ⟨ m, ⟨hm1, hm2⟩⟩
    use n + m
    grind [Nat.cast_add]
  lt_iff_le_not_ge a b := by
    rw [lt_iff, ← le_iff]
    constructor
    · intro h
      constructor
      · exact h.1
      · by_contra h2
        exact not_lt_self (lt_of_le_of_lt h2 h)
    · rintro ⟨ h1, h2 ⟩
      grind
  le_antisymm := fun _ _ h1 h2 ↦ le_antisymm h1 h2
  le_total a b := by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
    grind [trichotomous']
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  rw [show (-1 : Int) = 0 - 1 by rfl]
  simp

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, P 0 ∧ ∀ n, P n → P (n+1) ∧ ¬ ∀ n, P n := by
  use fun n => 0 ≤ n
  constructor
  norm_num
  intro n hn
  constructor
  · rw [le_iff] at *
    obtain ⟨ w, hw ⟩ := hn
    use w + 1
    simp [hw]
  · by_contra h
    have := le_antisymm (h (-1)) (by decide)
    simp_all


/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
@[grind]
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  rw [show 0 = 0 * n by simp]
  exact mul_le_mul_of_nonneg_right h h

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  obtain h1 | h2 := Int.trichotomous' n 0
  · exact Int.sq_nonneg_of_pos _ (by grind)
  · cases' h2 with h2 h3
    · have h3 : 0 < -n := neg_gt_neg h2
      have h4 : 0 ≤ -n := by grind
      have h5 : 0 ≤ (-n) * (-n) := by
        have := sq_nonneg_of_pos (-n) h4
        grind
      grind [neg_mul, neg_neg]
    grind [mul_zero, le_refl]

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have := sq_nonneg n
  rw [le_iff] at this
  rcases this with ⟨ m, hm ⟩
  use m
  grind

/--
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro a b h
    suffices : (a.minuend : ℤ) + b.subtrahend = b.minuend + a.subtrahend
    · grind
    · norm_cast
    )
  invFun n := if n < 0 then 0 —— (n.natAbs) else n.natAbs —— 0
  left_inv n := by
    obtain ⟨ a, b, rfl ⟩ := eq_diff n
    by_cases h : a < b <;> { simp [h]; grind }
  right_inv n := by
    by_cases h : n < 0
    simp only [h, ↓reduceIte, Quotient.lift_mk, CharP.cast_eq_zero, zero_sub]
    grind
    simp [h]
    grind

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' x y := by
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    rw [add_eq]
    simp
    grind
  map_mul' x y := by
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    rw [mul_eq]
    simp
    grind
  map_le_map_iff' := by
    intro x y
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    rw [le_iff]
    simp only [Quotient.lift_mk]
    constructor
    intro h
    use ((c:ℤ) - d + b - a).natAbs
    rw [natCast_eq]
    simp
    zify
    rw [abs_of_nonneg (by linarith)]
    ring

    intro h
    obtain ⟨ t, ht ⟩ := h
    rw [natCast_eq] at ht
    simp at ht
    grind


end Section_4_1
