import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue

In this (technical) epilogue, we show that the "Chapter 2" natural numbers `Chapter2.Nat` are isomorphic in various standard senses to the standard natural numbers `ℕ`.


From this point onwards, `Chapter2.Nat` will be deprecated, and we will use the standard natural numbers `ℕ` instead.  In particular, one should use the full Mathlib API for `ℕ` for all subsequent chapters, in lieu of the `Chapter2.Nat` API.

Filling the sorries here requires both the Chapter2.Nat API and the Mathlib API for the standard natural numbers `ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers via the Peano axioms.  The treatment in the preceding three sections was only partially axiomatic, because we used a specific construction `Chapter2.Nat` of the natural numbers that was an inductive type, and used that inductive type to construct a recursor.  Here, we give some exercises to show how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific implementation of the natural numbers.
-/

abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | Chapter2.Nat.zero => 0
  | Chapter2.Nat.succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := Chapter2.Nat.toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn
    . rfl
    simp [Chapter2.Nat.succ_toNat, hn]
    symm
    exact succ_eq_add_one _
  right_inv n := by
    induction' n with n hn
    . rfl
    simp [←succ_eq_add_one]
    exact hn

abbrev Chapter2.Nat.equivNat_order : Chapter2.Nat ≃o ℕ where
  toEquiv := Chapter2.Nat.equivNat
  map_rel_iff' := by
    intro n m
    simp [equivNat]
    sorry

abbrev Chapter2.Nat.equivNat_ring : Chapter2.Nat ≃+* ℕ where
  toEquiv := Chapter2.Nat.equivNat
  map_add' := by
    intro n m
    simp [equivNat]
    sorry
  map_mul' := by
    intro n m
    simp [equivNat]
    sorry

lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) : n.toNat ^ m.toNat = n^m := by
  sorry


/-- The Peano axioms for an abstract type `Nat` -/
@[ext]
class PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop), P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2.Nat : PeanoAxioms where
  Nat := _root_.Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib.Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast  := by
  sorry

theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  sorry

/-- The notion of an equivalence between two structures obeying the Peano axioms -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

abbrev Equiv.symm (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by sorry
  equiv_succ n := by sorry

abbrev Equiv.trans (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by sorry
  equiv_succ n := by sorry

abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib.Nat P where
  equiv := {
    toFun := P.natCast
    invFun := by sorry
    left_inv := by sorry
    right_inv := by sorry
  }
  equiv_zero := by sorry
  equiv_succ n := by sorry

abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := by sorry

theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) : equiv1 = equiv2 := by
  sorry

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) : ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  sorry

end PeanoAxioms
