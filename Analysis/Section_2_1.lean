import Mathlib.Tactic

/-!
# Analysis I, Section 2.1

This file is a translation of Section 2.1 of Analysis I to Lean 4.  All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Definition of the "Chapter 2" natural numbers, `Chapter2.Nat`. (In the book, the natural numbers are treated in a purely axiomatic fashion, as a type that obeys the Peano axioms; but here we take advantage of Lean's native inductive types to explicitly construct a version of the natural numbers that obey those axioms.  One could also proceed more axiomatically, as is done in Section 3 for set theory, but we leave this as an exercise for the reader.)
- Establishment of the Peano axioms for `Chapter2.Nat`
- Recursive definitions for `Chapter2.Nat`

Note: at the end of this Chapter, the `Chapter2.Nat` class will be deprecated in favor of the standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of `Chapter2.Nat` "by hand" for pedagogical purposes.

-/

namespace Chapter2

/-- Assumption 2.6 (Existence of natural numbers).  Here we use an explicit construction of the natural numbers (using an inductive type).  For a more axiomatic approach, see the epilogue to this chapter. -/
inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq  -- this allows `decide` to work on `Nat`

/-- Axiom 2.1 (0 is a natural number) -/
instance Nat.instZero : Zero Nat := ⟨ zero ⟩
#check (0:Nat)

/-- Axiom 2.2 (Successor of a natural number is a natural number) -/
postfix:100 "++" => Nat.succ
#check (fun n ↦ n++)


/-- Definition 2.1.3 (Definition of the numerals 0, 1, 2, etc.). Note: to avoid ambiguity, one may need to use explicit casts such as (0:Nat), (1:Nat), etc. to refer to this Chapter's version of the natural numbers. -/
instance Nat.instOfNat {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

instance Nat.instOne : One Nat := ⟨ 1 ⟩
lemma Nat.zero_succ : 0++ = 1 := by rfl
#check (1:Nat)

lemma Nat.one_succ : 1++ = 2 := by rfl
#check (2:Nat)

/-- Proposition 2.1.4 (3 is a natural number)-/
lemma Nat.two_succ : 2++ = 3 := by rfl
#check (3:Nat)

/-- Axiom 2.3 (0 is not the successor of any natural number) -/
theorem Nat.succ_ne (n:Nat) : n++ ≠ 0 := by
  by_contra h
  simp only [reduceCtorEq] at h

/-- Proposition 2.1.6 (4 is not equal to zero) -/
theorem Nat.four_ne : (4:Nat) ≠ 0 := by
  -- By definition, 4 = 3++.
  change 3++ ≠ 0
  -- By axiom 2.3, 3++ is not zero.
  exact succ_ne _

/-- Axiom 2.4 (Different natural numbers have different successors) -/
theorem Nat.succ_cancel {n m:Nat} (hnm: n++ = m++) : n = m := by
  rwa [succ.injEq] at hnm

/-- Axiom 2.4 (Different natural numbers have different successors) -/
theorem Nat.succ_ne_succ (n m:Nat) : n ≠ m → n++ ≠ m++ := by
  intro h
  contrapose! h
  exact succ_cancel h

/-- Proposition 2.1.8 (6 is not equal to 2) -/
theorem Nat.six_ne_two : (6:Nat) ≠ 2 := by
-- this proof is written to follow the structure of the original text.
  by_contra h
  change 5++ = 1++ at h
  replace h := succ_cancel h
  change 4++ = 0++ at h
  replace h := succ_cancel h
  have := four_ne
  contradiction

/-- One can also prove this sort of result by the `decide` tactic -/
theorem Nat.six_ne_two' : (6:Nat) ≠ 2 := by
  decide

/-- Axiom 2.5 (principle of mathematical induction). -/
theorem Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind _ ih

abbrev Nat.recurse (f: Nat → Nat → Nat) (c: Nat) : Nat → Nat := fun n ↦ match n with
| 0 => c
| n++ => f n (recurse f c n)

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.recurse_zero (f: Nat → Nat → Nat) (c: Nat) : Nat.recurse f c 0 = c := by rfl

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.recurse_succ (f: Nat → Nat → Nat) (c: Nat) (n: Nat) : recurse f c (n++) = f n (recurse f c n) := by rfl

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.eq_recurse (f: Nat → Nat → Nat) (c: Nat) (a: Nat → Nat) : (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c := by
  constructor
  . intro ⟨ h0, hsucc ⟩
    -- this proof is written to follow the structure of the original text.
    apply funext; apply induction
    . exact h0
    intro n hn
    rw [hsucc n, recurse_succ, hn]
  intro h
  rw [h]
  constructor
  . exact recurse_zero _ _
  exact recurse_succ _ _


/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.recurse_uniq (f: Nat → Nat → Nat) (c: Nat) : ∃! (a: Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
apply ExistsUnique.intro (recurse f c)
. constructor
  . exact recurse_zero _ _
  . exact recurse_succ _ _
intro a
exact (eq_recurse _ _ a).mp

end Chapter2
