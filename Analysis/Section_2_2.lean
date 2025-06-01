import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`
- Establishment of basic properties of addition and order

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of `Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers). -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

instance Nat.instAdd : Add Nat where
  add := add

theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- sum of two natural numbers is again a natural number
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n) -/
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Why?) -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  revert n
  apply induction
  decide
  intro n ih
  rw [succ_add, ih]

/-- Proposition 2.2.4 (Addition is commutative) -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

theorem add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
/- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1-/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert a; apply induction
  rw [zero_add, zero_add]
  intro a IH
  rw [succ_add, succ_add, succ_add]
  rw [IH]

/-- Proposition 2.2.6 (Cancellation law) -/
theorem Nat.add_cancel_left (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.isPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.isPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).-/
theorem Nat.pos_add {a:Nat} (b:Nat) (ha: a.isPos) : (a + b).isPos := by
  -- this proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

theorem Nat.add_pos {a:Nat} (b:Nat) (ha: a.isPos) : (b + a).isPos := by
  rw [add_comm]
  exact pos_add _ ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).-/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- this proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [← isPos_iff] at ha
    have : (a + b).isPos := pos_add _ ha
    contradiction
  rw [← isPos_iff] at hb
  have : (a + b).isPos := add_pos _ hb
  contradiction

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma uniq_succ_eq (a:Nat) (ha: a.isPos) : ∃! b, b++ = a := by
  revert a; apply induction

  . intro h
    exfalso
    rw [Nat.isPos_iff] at h
    trivial

  intro a IH h
  use a
  constructor
  . dsimp

  dsimp
  intro y hy
  exact succ_cancel hy

/-- Definition 2.2.11 (Ordering of the natural numbers) -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers) -/
instance Nat.instLT : LT Nat where
  lt n m := (∃ a:Nat, m = n + a) ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

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

theorem Nat.self_ne_succ (n:Nat) : n ≠ n++ := by
  revert n
  apply induction
  exact Ne.symm (succ_ne 0)
  intro n IH
  apply succ_ne_succ
  exact IH

theorem Nat.succ_gt (n:Nat) : n++ > n := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  use 1
  exact succ_eq_add_one n
  exact Nat.self_ne_succ n

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). -/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  use 0
  exact Eq.symm (add_zero a)

/-- (b) (Order is transitive) -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  rcases hab with ⟨d, hd⟩
  rcases hbc with ⟨e, he⟩
  use d + e
  rw [hd, he]
  rw [add_assoc]
  rw [add_comm e]

theorem Nat.eq_0_of_idempotent_add (a b : Nat) (h : a = a + b) : b = 0 := by
  rw (occs := .pos [1]) [show a = a + 0 by exact Eq.symm (add_zero a)] at h
  exact add_cancel_left a b 0 (Eq.symm h)

/-- (c) (Order is anti-symmetric)  -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  rcases hab with ⟨d, hd⟩
  rcases hba with ⟨e, he⟩
  rw [hd] at he
  rw [add_assoc] at he
  have := add_eq_zero d e (Nat.eq_0_of_idempotent_add _ _ he)
  rcases this with ⟨rw1, rw2⟩
  rw [rw1] at hd
  rw [add_zero] at hd
  exact hd

/-- (d) (Addition preserves order)  -/
theorem add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  intro h
  rcases h with ⟨d, hd⟩
  use d
  rw [hd]
  rw [add_assoc, add_comm d, ←add_assoc]

  intro h
  rcases h with ⟨d, hd⟩
  rw [add_comm b, add_assoc] at hd
  rw [add_comm a] at hd
  have hd := add_cancel_left _ _ _ hd
  use d

/-- (d) (Addition preserves order)  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order)  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order)  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b. -/
theorem lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  constructor
  intro h
  rcases h with ⟨⟨d, h1⟩, h2⟩

  have : d ≠ 0 := by
    intro d_eq_0
    rw [d_eq_0, add_zero] at h1
    exact h2 (Eq.symm h1)

  have := uniq_succ_eq d this

  rcases this with ⟨p, h3, h4⟩
  use p
  rw [h1]
  rw [succ_add, add_comm a p, ← succ_add, h3, add_comm]

  intro h
  rcases h with ⟨d, h⟩
  constructor
  use d.succ

  rw [succ_add] at h
  rw [add_succ]
  exact h

  by_contra a_eq_b
  rw [← a_eq_b] at h

  have h1 : a ≥ a.succ := by use d

  have h2 : a.succ ≥ a := by
    use 1
    exact succ_eq_add_one a

  have : a = a.succ := ge_antisymm h1 h2

  exact self_ne_succ a this

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.isPos ∧ b = a + d := by
  constructor
  intro h
  rcases h with ⟨⟨d, h1⟩, h2⟩
  use d
  constructor
  unfold Nat.isPos
  by_contra h3
  rw [h3, add_zero] at h1
  exact h2 (Eq.symm h1)
  exact h1

  intro h
  rcases h with ⟨d, h1, h2⟩
  constructor
  use d
  by_contra a_eq_b
  rw [← a_eq_b] at h2

  have d_eq_0 := eq_0_of_idempotent_add _ _ h2
  exact h1 d_eq_0

/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction


/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4 -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . have why : 0 ≤ b := by
      use b
      exact Eq.symm (zero_add b)
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [Nat.le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by
      rw [case2]
      exact Nat.succ_gt b
    tauto
  have why : a++ > b := by
    rw [Nat.gt_iff_lt] at *
    rw [lt_iff_add_pos] at *
    rcases case3 with ⟨d, h1, h2⟩
    use d.succ
    constructor
    unfold Nat.isPos
    exact succ_ne d
    rw [add_succ, ← h2]
  tauto

/-- (Not from textbook) The order is decidable.  This exercise is only recommended for Lean experts. -/
instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := by
  sorry

/-- (Not from textbook) Nat has the structure of a linear ordering. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_le := sorry
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Not from textbook) Nat has the structure of an ordered monoid. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
-/
theorem strong_induction {m₀:Nat} {P: Nat → Prop} (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) : ∀ m, m ≥ m₀ → P m := by
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

/-- Exercise 2.2.6 (backwards induction) -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}  (hind: ∀ m, P (m++) → P m) (hn: P n) : ∀ m, m ≤ n → P m := by
  sorry

/-- Exercise 2.2.7 (induction from a starting point) -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) : P n → ∀ m, m ≥ n → P m := by
  sorry
  -- intro h m
  -- apply induction




end Chapter2
