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

- Definition of addition and order for the "Chapter 2" natural numbers, {name}`Chapter2.Nat`.
- Establishment of basic properties of addition and order.

Note: at the end of this chapter, the {name}`Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
{name}`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their
tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's {name}`Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the {kw (of := «term_+_»)}`+` notation to be used for natural number
    addition.-/
instance Nat.instAdd : Add Nat where add := add

/-- Compare with Mathlib's {name}`Nat.zero_add`. -/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's {name}`Nat.succ_add`. -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's {name}`Nat.one_add`. -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- The sum of two natural numbers is again a natural number.
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 ({lean}`n + 0 = n`). Compare with Mathlib's {name}`Nat.add_zero`. -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- This proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 ({lean}`n+(m++) = (n+m)++`). Compare with Mathlib's {name}`Nat.add_succ`. -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- {lean}`n++ = n + 1` (Why?). Compare with Mathlib's {name}`Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  calc
    n++ = (n + 0)++ := by rw [add_zero]
    _ = n + (0++) := by rw [add_succ]
    _ = n + 1 := by rfl

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's {name}`Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's {name}`Nat.add_assoc`. -/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert c; apply induction
  . rw [add_zero, add_zero]
  intro c ih
  rw [add_succ, add_succ, add_succ, ih]

/-- Proposition 2.2.6 (Cancellation law).
    Compare with Mathlib's {name}`Nat.add_left_cancel`. -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) {name}`Nat` can be given the structure of a commutative additive monoid.
    This permits tactics such as {tactic}`abel` to apply to the Chapter 2 natural numbers. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- This illustration of the {tactic}`abel` tactic is not from the
    textbook. -/
example (a b c d:Nat) : (a+b)+(c+0+d) = (b+c)+(d+a) := by abel

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's {name}`Nat.add_pos_left`. -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- This proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

/-- Compare with Mathlib's {name}`Nat.add_pos_right`.

This theorem is a consequence of the previous theorem and {name}`add_comm`, and {tactic}`grind` can
automatically discover such proofs. -/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  grind [add_comm, add_pos_left]

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's {name}`Nat.add_eq_zero`. -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  obtain ha | hb := h
  . rw [← isPos_iff] at ha
    observe : (a + b).IsPos
    contradiction
  rw [← isPos_iff] at hb
  observe : (a + b).IsPos
  contradiction

/-
The API in `Tools/ExistsUnique.Lean`, and the method `existsUnique_of_exists_of_unique` in
particular, may be useful for the next problem.  Also, the `obtain` tactic is
useful for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.IsPos) : ∃! b, b++ = a := by
  apply existsUnique_of_exists_of_unique
  · induction a with
    | zero => contradiction
    | succ a _ => use a
  · intro b c hb hc
    rw [← hb] at hc
    exact (succ_cancel hc).symm

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the {kw (of := «term_≤_»)}`≤` notation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the {kw (of := «term_<_»)}`<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

/-- Compare with Mathlib's {name}`le_iff_exists_add`. -/
lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's {name}`ge_iff_le`. -/
@[symm]
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's {name}`gt_iff_lt`. -/
@[symm]
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's {name}`Nat.le_of_lt`. -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's {name}`Nat.le_iff_lt_or_eq`. -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

/-- Compare with Mathlib's {name}`Nat.lt_succ_self`. -/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  · use 1
    grind [succ_eq_add_one]
  · by_contra h
    rw [succ_eq_add_one] at h
    nth_rewrite 1 [← add_zero n] at h
    apply add_left_cancel at h
    contradiction

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's {name}`Nat.le_refl`.-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  rw [Nat.ge_iff_le, Nat.le_iff]
  use 0
  rw [add_zero]

@[refl]
theorem Nat.le_refl (a:Nat) : a ≤ a := a.ge_refl

/-- The refl tag allows for the {tactic}`rfl` tactic to work for inequalities. -/
example (a b:Nat): a+b ≥ a+b := by rfl

/-- (b) (Order is transitive).  The {tactic}`obtain` tactic will be useful here.
    Compare with Mathlib's {name}`Nat.le_trans`. -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  rw [Nat.ge_iff_le, Nat.le_iff] at hab hbc
  obtain ⟨d, hd⟩ := hab
  obtain ⟨e, he⟩ := hbc
  use d + e
  rw [hd, he, add_comm d e, ←add_assoc]

theorem Nat.le_trans {a b c:Nat} (hab: a ≤ b) (hbc: b ≤ c) : a ≤ c := Nat.ge_trans hbc hab

/-- (c) (Order is anti-symmetric). Compare with Mathlib's {name}`Nat.le_antisymm`. -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  rw [Nat.ge_iff_le, Nat.le_iff] at hab hba
  obtain ⟨d, hd⟩ := hab
  obtain ⟨e, he⟩ := hba

  rw [hd, add_assoc] at he
  nth_rewrite 1 [← add_zero b] at he
  apply add_left_cancel at he

  have he := he.symm
  apply add_eq_zero at he
  obtain ⟨hd0, he0⟩ := he
  rw [hd, hd0, add_zero]

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_right`. -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  -- rw [Nat.ge_iff_le, Nat.ge_iff_le, Nat.le_iff, Nat.le_iff]
  constructor
  · rintro ⟨d, hd⟩
    rw [hd, ge_iff_le, le_iff]
    use d
    grind
  · rintro ⟨d, hd⟩
    rw [add_comm, add_comm b c, add_assoc] at hd
    apply add_left_cancel at hd
    rw [ge_iff_le, le_iff]
    use d

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_left`.  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_right`.  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_left`.  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's {name}`Nat.succ_le_iff`. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  rw [Nat.lt_iff, Nat.le_iff]
  constructor
  · rintro ⟨⟨d, hd⟩, hne⟩
    have hdpos : d ≠ 0 := by
      by_contra hzero
      -- apply hne
      rw [hzero, add_zero] at hd
      have hd := hd.symm
      contradiction

    apply uniq_succ_eq at hdpos
    obtain ⟨c, hsucc, _⟩ := hdpos
    use c
    rw [hd, ←hsucc, add_succ, succ_add]
  · rintro ⟨d, hd⟩
    constructor
    · use d + 1
      rw [←add_assoc, hd, succ_eq_add_one]
      grind
    · by_contra heq
      rw [heq, succ_eq_add_one, add_assoc] at hd
      nth_rewrite 1 [← add_zero b] at hd
      apply add_left_cancel at hd
      contradiction

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.IsPos ∧ b = a + d := by
  rw [Nat.lt_iff]
  constructor
  · rintro ⟨hle, hne⟩
    obtain ⟨d, hd⟩ := hle
    use d
    constructor
    · intro hzero
      apply hne
      rw [hzero, add_zero] at hd
      exact hd.symm
    · exact hd
  · rintro ⟨d, ⟨hdpos, hd⟩⟩
    constructor
    · use d
    · intro h
      apply hdpos
      rw [← add_zero a, hd] at h
      exact (add_left_cancel _ _ _ h).symm

/-- If a < b then a ̸= b,-/
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

theorem Nat.lt_of_le_of_lt {a b c : Nat} (hab: a ≤ b) (hbc: b < c) : a < c := by
  rw [lt_iff_add_pos] at *
  choose d hd using hab
  choose e he1 he2 using hbc
  use d + e; split_ands
  . exact add_pos_right d he1
  . rw [he2, hd, add_assoc]

/-- This lemma was a {lit}`why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
theorem Nat.zero_le (a:Nat) : 0 ≤ a := by
  rw [Nat.le_iff]
  use a
  rw [zero_add]

/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's {name}`trichotomous`.  Parts of this theorem have been placed
    in the preceding Lean theorems. -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . observe why : 0 ≤ b
    rw [le_iff_lt_or_eq] at why
    tauto
  intro a ih
  obtain case1 | case2 | case3 := ih
  . rw [lt_iff_succ_le] at case1
    rw [le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by
      rw [← case2]
      exact succ_gt_self a
    tauto
  have why : a++ > b :=
    have h1 := succ_gt_self a
    have h2 := le_of_lt case3
    lt_of_le_of_lt h2 h1
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the proof
  involving decidability has been provided; the remaining sorries involve claims about the natural
  numbers.  One could also have established this result by the {tactic}`classical` tactic followed
  by {syntax tactic}`exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's {name}`Nat.decLe`.
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    exact zero_le b
  | a++, b => by
    cases decLe a b with
    | isTrue hle =>
      cases decEq a b with
      | isTrue heq =>
        apply isFalse
        intro h2
        rw [←lt_iff_succ_le] at h2
        grind [not_lt_self]
      | isFalse hne =>
        rw [←lt_iff_succ_le, lt_iff, ←le_iff]
        apply isTrue
        grind
    | isFalse hle =>
      apply isFalse

      intro h1
      rw [←lt_iff_succ_le] at h1
      have h2: a ≤ b := le_of_lt h1

      grind

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

/-- (Not from textbook) {name}`Nat` has the structure of a linear ordering. This allows for tactics
such as {tactic}`order` and {tactic}`calc` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_ge a b := by
    constructor
    . intro h; refine ⟨ le_of_lt h, ?_ ⟩
      by_contra h'
      exact not_lt_self (lt_of_le_of_lt h' h)
    rintro ⟨ h1, h2 ⟩
    rw [lt_iff, ←le_iff]; refine ⟨ h1, ?_ ⟩
    by_contra h
    subst h
    contradiction
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total a b := by
    obtain h | rfl | h := trichotomous a b
    . left; exact le_of_lt h
    . simp [ge_refl]
    . right; exact le_of_lt h
  toDecidableLE := decidableRel

/-- This illustration of the {tactic}`order` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

/-- An illustration of the {tactic}`calc` tactic with {kw (of := «term_≤_»)}`≤`/
    {kw (of :=«term_<_»)}`<`. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hcd: c ≤ d)
        (hde: d ≤ e) : a + 0 < e := by
  calc
    a + 0 = a := by simp
        _ ≤ b := hab
        _ < c := hbc
        _ ≤ d := hcd
        _ ≤ e := hde

/-- (Not from textbook) {name}`Nat` has the structure of an ordered monoid. This allows for tactics
    such as {tactic}`gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left a b hab c := (Nat.add_le_add_right a b c).mp hab

/-- This illustration of the {tactic}`gcongr` tactic is not from the
    textbook. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hde: d < e) :
  a + d ≤ c + e := by
  gcongr
  order

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's {name}`Nat.strong_induction_on`.
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by

  have hm0 := hind m₀
  simp at hm0

  have hlemma: ∀ k n, n ≥ m₀ ∧ n ≤ m₀ + k → P n := by
    apply induction
    . simp; intro k h1 h2;
      have: k = m₀ := by grind
      grind -- hm0
    intro k h1 a h2
    -- lemma for rw h1
    have (a b:Nat) : a ≤ b ↔ a < b++ := by
      constructor
      . have hb := succ_gt_self b
        grind [lt_of_le_of_lt]
      . rw [lt_iff_succ_le, succ_eq_add_one, succ_eq_add_one]
        grind [add_le_add_right]

    -- rw h1: n ≤ m₀ + k ↔ n < m₀ + k + 1 to fit hind
    have h1rw : ∀ (n : Nat), n ≥ m₀ ∧ n < (m₀ + k)++ → P n := by grind
    rw [succ_eq_add_one] at h1rw
    have: m₀ + k + 1 ≥ m₀ := by grind [le_iff, add_le_add_left, ge_trans]
    have h3 := hind (m₀ + k + 1) this h1rw

    specialize h1 a
    have h4: a ≥ m₀ ∧ a ≤ m₀ + k + 1 → P a := by grind -- merge h1 and h3
    rw [succ_eq_add_one, ←add_assoc] at h2
    exact h4 h2

  intro m hm
  simp [le_iff] at hm
  obtain ⟨a, hm2⟩ := hm
  have : m ≥ m₀ ∧ m ≤ m₀ + a := by grind [le_iff]
  exact hlemma a m this

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's {name}`Nat.decreasingInduction`. -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  intro m hmn
  revert n; apply induction
  . intro hp0 hle
    have : m ≥ 0 := by grind [zero_le]
    have : m = 0 := by grind
    rwa [←this] at hp0
  -- n -> n++
  intro n h1 h2 h3
  have hpn := hind n h2
  rw [le_iff_lt_or_eq] at h3
  cases h3 with
  | inl hleft =>
    rw [lt_iff_succ_le, succ_eq_add_one, succ_eq_add_one] at hleft
    have : m ≤ n := by grind [add_le_add_right]
    exact h1 hpn this
  | inr hright => rwa [←hright] at h2

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's {name}`Nat.le_induction`. -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  intro hPn m hge

  revert m; apply induction
  . intro h1
    have : n ≥ 0 := by grind [zero_le]
    have : n = 0 := by grind
    rwa [this] at hPn
  intro m hPm hmn
  rw [ge_iff_le, le_iff_lt_or_eq] at hmn
  cases hmn with
  | inl hleft =>
    rw [lt_iff_succ_le, succ_eq_add_one, succ_eq_add_one] at hleft
    have : m ≥ n := by grind [add_le_add_right]
    exact hind m (hPm this)
  | inr hright => rwa [←hright]

end Chapter2
