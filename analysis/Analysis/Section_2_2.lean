import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2: Addition

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`.
- Establishment of basic properties of addition and order.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the `+` notation to be used for natural number addition. -/
instance Nat.instAdd : Add Nat where
  add := add

/-- Compare with Mathlib's `Nat.zero_add`. -/
@[simp, grind]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's `Nat.succ_add`. -/
@[grind]
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's `Nat.one_add`. -/
@[grind]
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl]
  grind

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl]
  grind

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- The sum of two natural numbers is again a natural number.
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n). Compare with Mathlib's `Nat.add_zero`. -/
@[simp, grind]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- This proof is written to follow the structure of the original text.
  revert n; apply induction <;> grind

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). Compare with Mathlib's `Nat.add_succ`. -/
@[grind _=_]
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction <;> grind

/-- n++ = n + 1 (Why?). Compare with Mathlib's `Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  revert n
  apply induction
  decide
  grind

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's `Nat.add_comm` -/
@[grind]
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction <;> grind

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's `Nat.add_assoc`. -/
@[grind]
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert a; apply induction <;> grind

/-- Proposition 2.2.6 (Cancellation law).
    Compare with Mathlib's `Nat.add_left_cancel`. -/
@[grind]
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  revert a; apply induction <;> grind

/-- (Not from textbook)

Nat can be given the structure of a commutative additive monoid.

This permits tactics such as `abel` to apply to the Chapter 2 natural numbers. `abel` proves any equalities (aka identities) that hold in a commutative additive monoid.
-/
instance Nat.instAddCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- This illustration of the `abel` tactic is not from the
    textbook. -/
example (a b c d:Nat) : (a+b)+(c+0+d) = (b+c)+(d+a) := by abel

-- This is the instance we just defined.
#synth AddCommMonoid Nat

-- Lean knows that every `AddCommMonoid` is also an `AddCommSemigroup`.
#synth AddCommSemigroup Nat

/-- Because of the instances we have defined, Mathlib knows the definition of and even natural number and relevant theorems for `Nat`. -/
example : Even (6:Nat) := by use 3; rfl
example (a b : Nat) (h1 : Even a) (h2 : Even b) : Even (a + b) := Even.add h1 h2

/- (More notes on algebraic type classes)

In Section 2.3, we will define multiplication, prove that `Nat` is in fact a commutative semiring (`CommSemiRing`), and describe the corresponding `ring` tactic; since all semirings are additive monoids, `abel` is a weaker tactic and you will see `ring` used in contexts where `abel` is actually sufficient.

The study of these algebraic structures and their relations is not a focus of the textbook; however, Mathlib uses them extensively for stating theorems, notation, and tactics, so it is useful to know the important structures.
-/

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

@[grind]
theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's `Nat.add_pos_left`. -/
@[grind]
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- This proof is written to follow the structure of the original text.
  revert b; apply induction <;> grind

/-- Compare with Mathlib's `Nat.add_pos_right`.

This theorem is a consequence of the previous theorem and `add_comm`, and `grind` can automatically discover such proofs.
-/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  grind

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's `Nat.add_eq_zero`. -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  grind

/-
The API in `Tools/ExistsUnique.Lean`, and the method `existsUnique_of_exists_of_unique` in
particular, may be useful for the next problem.  Also, the `obtain` tactic is
useful for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.IsPos) : ∃! b, b++ = a := by
  revert a; apply induction
  · grind
  · intro a IH h
    use a
    grind

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `≤` notation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's `ge_iff_le`. -/
@[symm]
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's `gt_iff_lt`. -/
@[symm]
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's `Nat.le_of_lt`. -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's `Nat.le_iff_lt_or_eq`. -/
@[grind]
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    grind
  grind

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

/-- Compare with Mathlib's `Nat.lt_succ_self`. -/
@[grind]
theorem Nat.self_ne_succ (n:Nat) : n ≠ n++ := by
  revert n; apply induction <;> grind

/-- Compare with Mathlib's `Nat.lt_succ_self`-/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  · use 1
    grind
  · grind

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's `Nat.le_refl`.-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  use 0
  grind

@[refl]
theorem Nat.le_refl (a:Nat) : a ≤ a := a.ge_refl

/-- The refl tag allows for the `rfl` tactic to work for inequalities. -/
example (a b:Nat): a+b ≥ a+b := by rfl

/-- (b) (Order is transitive).  The `obtain` tactic will be useful here.
    Compare with Mathlib's `Nat.le_trans`. -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  obtain ⟨d, hd⟩ := hab
  obtain ⟨e, he⟩ := hbc
  use d + e
  grind

theorem Nat.eq_0_of_idempotent_add (a b : Nat) (h : a = a + b) : b = 0 := by
  have : a = a + 0 := by grind
  grind

theorem Nat.le_trans {a b c:Nat} (hab: a ≤ b) (hbc: b ≤ c) : a ≤ c := Nat.ge_trans hbc hab

/-- (c) (Order is anti-symmetric). Compare with Mathlib's `Nat.le_antisymm`. -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  rcases hab with ⟨d, hd⟩
  rcases hba with ⟨e, he⟩
  rw [hd] at he
  rw [add_assoc] at he
  have := add_eq_zero d e (Nat.eq_0_of_idempotent_add _ _ he)
  grind

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`. -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  intro h
  rcases h with ⟨d, hd⟩
  use d
  grind

  intro h
  rcases h with ⟨d, hd⟩
  rw [add_comm b, add_assoc] at hd
  rw [add_comm a] at hd
  have hd := add_left_cancel _ _ _ hd
  use d

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`.  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`.  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`.  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's `Nat.succ_le_iff`. -/
@[grind]
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  constructor
  . rintro ⟨⟨ d, h1 ⟩, h2⟩

    have : d ≠ 0 := by
      intro d_eq_0
      rw [d_eq_0, add_zero] at h1
      exact h2 (Eq.symm h1)

    obtain ⟨p, h3, h4⟩ := uniq_succ_eq d this
    use p
    rw [h1, succ_add, add_comm a p, ← succ_add, h3, add_comm]

  . rintro ⟨d, h⟩
    constructor
    . use d.succ
      simp_all [succ_add, add_succ]

    . by_contra a_eq_b
      rw [← a_eq_b] at h
      exact self_ne_succ a (ge_antisymm (by use d) (by use 1; exact succ_eq_add_one a))

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.IsPos ∧ b = a + d := by
  constructor
  · intro h
    rcases h with ⟨⟨d, h1⟩, h2⟩
    use d
    constructor
    · unfold Nat.IsPos
      by_contra h3
      grind
    grind

  intro h
  rcases h with ⟨d, h1, h2⟩
  constructor
  use d
  by_contra a_eq_b
  rw [← a_eq_b] at h2
  have d_eq_0 := eq_0_of_idempotent_add _ _ h2
  exact h1 d_eq_0

lemma Nat.isPos_iff_lt (n:Nat) : n.IsPos ↔ 0 < n := by
  rw [lt_iff_add_pos]
  constructor
  intro h
  use n
  constructor
  exact h
  rw [zero_add]

  intro h
  obtain ⟨d, h1, h2⟩ := h
  rw [zero_add] at h2
  simp_all

/-- If a < b then a ̸= b,-/
@[grind]
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (le_of_lt h.1) (le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction

theorem Nat.not_lt_self {a: Nat} (h : a < a) : False := by
  apply not_lt_of_gt a a
  simp [h]

@[grind]
theorem Nat.lt_of_le_of_lt {a b c : Nat} (hab: a ≤ b) (hbc: b < c) : a < c := by
  rw [lt_iff_add_pos] at *
  choose d hd using hab
  choose e he1 he2 using hbc
  use d + e; split_ands
  . exact add_pos_right d he1
  . rw [he2, hd, add_assoc]

/-- This lemma was a `why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
@[grind]
theorem Nat.zero_le (a:Nat) : 0 ≤ a := by use a; simp

/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's `trichotomous`.  Parts of this theorem have been placed
    in the preceding Lean theorems. -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . observe : 0 ≤ b
    grind
  intro a ih
  obtain case1 | case2 | case3 := ih
  · grind
  · have := succ_gt_self b
    grind
  have why : a++ > b := by
    rw [Nat.gt_iff_lt] at *
    rw [lt_iff_add_pos] at *
    rcases case3 with ⟨d, h1, h2⟩
    use d.succ
    constructor
    unfold Nat.IsPos
    exact succ_ne d
    rw [add_succ, ← h2]
  grind

def Nat.IsLe (a b: Nat) : Bool :=
  match a, b with
  | 0, _ => true
  | a++, b => match (Nat.IsLe a b) with
    | true => true
    | false => false

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers.  One could also have established this result by the `classical` tactic
  followed by `exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's `Nat.decLe`.
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    exact zero_le b
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        intro h'
        have : b < b := by grind
        grind
      | isFalse h' =>
        apply isTrue
        grind
    | isFalse h =>
      apply isFalse
      intro h'
      rw [← lt_iff_succ_le] at h'
      apply h
      exact le_of_lt h'

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

example : Nat.zero++++++ ≤ Nat.zero++++++++ := by decide

/-- (Not from textbook) Nat has the structure of a linear ordering. This allows for tactics
such as `order` and `calc` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_ge := by
    intro a b
    constructor
    intro h
    constructor
    . exact le_of_lt h
    · by_contra h'
      have : b < b := by grind
      grind

    rintro ⟨ h1, h2 ⟩
    rw [lt_iff, ← le_iff]
    constructor
    exact h1
    by_contra h
    rw [h] at h2
    apply h2
    exact ge_refl b
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := by
    intro a b
    obtain h | h | h := trichotomous a b
    . left; exact le_of_lt h
    . simp [h, ge_refl]
    . right; exact le_of_lt h

  toDecidableLE := decidableRel

/-- This illustration of the `order` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

/-- An illustration of the `calc` tactic with `≤/<`. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hcd: c ≤ d)
        (hde: d ≤ e) : a + 0 < e := by
  calc
    a + 0 = a := by simp
        _ ≤ b := hab
        _ < c := hbc
        _ ≤ d := hcd
        _ ≤ e := hde

/-- (Not from textbook) Nat has the structure of an ordered monoid. This allows for tactics
such as `gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left a b hab c := (add_le_add_left a b c).mp hab


/--
This illustration of the `gcongr` tactic is not from the textbook.

`congr` operates on equalities; it will decompose a goal of the form `f a = f b` into `a = b`, and a goal of the form `a + b = c + d` into `a = c` and `b = d`.

`gcongr` generalizes `congr` to the case of any congruence, where a congruence is a relation that is "similar" to equality. Examples include `≤`, `<` and equality in modular arithmetic.
-/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hde: d < e) :
  a + d ≤ c + e := by
  gcongr
  order

/-- A common trick is to rewrite an expression in a creative way, and then use `gcongr`. -/
example (a b c:Nat) (h2: a ≤ b) :
  a ≤ b + c := by
  rw [show a = a + 0 by abel]
  gcongr
  exact Nat.zero_le c

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's `Nat.strong_induction_on`.
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  have Q (n : Nat): ∀ m : Nat, m₀ ≤ m → m ≤ n → P m := by
    apply induction
    intro h1 h2
    apply hind
    exact h1
    rintro m' ⟨h3, h4⟩
    exfalso
    sorry
    sorry
  sorry

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's `Nat.decreasingInduction`. -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  sorry

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's `Nat.le_induction`. -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  sorry
  -- intro h m
  -- apply induction




end Chapter2
