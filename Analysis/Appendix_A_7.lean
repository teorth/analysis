import Mathlib.Tactic

/-!
# Analysis I, Appendix A.7: Equality

Introduction to equality in Lean

-/

example : ∑' n:ℕ, 9*(10:ℝ)^(-(n:ℤ)-1) = 1 := by
  convert_to ∑' n:ℕ, (9/10)*(1/10:ℝ)^n = 1
  . apply tsum_congr
    intro n
    rw [zpow_sub₀ (by positivity), ←zpow_natCast, one_div_zpow]
    simp; ring
  convert_to (9/10) * ∑' n:ℕ, (1/10:ℝ)^n = 1
  . convert tsum_const_smul'' (9/10:ℝ) (f := fun n ↦ (1/10:ℝ)^n) using 1
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

example : 12 = (2:Fin 10)  := by
  decide


/-- Reflexive axiom -/
example {X:Type} (x:X) : x = x := by
  rfl

#check Eq.refl

/-- Symmetry axiom -/
example {X:Type} (x y:X) (h: x = y) : y = x := by
  rw [h]

#check Eq.symm

/-- Transitivity axiom -/
example {X:Type} (x y z:X) (h1: x = y) (h2: y = z) : x = z := by
  rw [h1, h2]

#check Eq.trans

/-- Substitution axiom -/
example {X Y:Type} (f:X → Y) (x y:X) (h: x = y) : f x = f y := by
  rw [h]

#check congrArg

def equality_as_equiv_relation (X:Type) : Setoid X := {
  r a b := a = b
  iseqv := {
    refl := Eq.refl
    symm := Eq.symm
    trans := Eq.trans
  }
}


open Real in
/-- Example A.7.1 -/
example {x y:ℝ} (h:x = y) : 2*x = 2*y ∧ sin x = sin y ∧ ∀ z, x + z = y + z := by
  split_ands
  . rw [h]
  . rw [h]
  intro z
  rw [h]

/-- Example A.7.2 -/
example {n m:ℤ} (hn: Odd n) (h: n = m) : Odd m := by
  rw [h] at hn
  exact hn

example {n m k:ℤ} (hnk: n > k) (h: n = m) : m > k := by
  rw [h] at hnk
  exact hnk

open Real in
example {x y z:ℝ} (hxy : x = sin y) (hyz : y = z^2) : x = sin (z^2) := by
  have : sin y = sin (z^2) := by rw [hyz]
  exact hxy.trans this

abbrev make_twelve_equal_two : ℤ → ℤ → Prop := fun a b ↦ a = 12 ∧ b = 2

/-- A version of the integers where 12 has been forced to equal 2. -/
abbrev NewInt := Quot make_twelve_equal_two

/-- A coercion from integers to new integers -/
instance : Coe ℤ NewInt where
  coe n := Quot.mk make_twelve_equal_two n

#check ((2:ℤ):NewInt)
#check ((12:ℤ):NewInt)

example : ((12:ℤ):NewInt) = ((2:ℤ):NewInt) := by
  apply Quot.sound
  simp [make_twelve_equal_two]

theorem NewInt.is_coe (N:NewInt) : ∃ n:ℤ, N = (n:NewInt) := by
  apply Quot.ind (q := N); intro n
  use n

abbrev NewInt.quot {X:Type} {f: ℤ → X} (hf: f 12 = f 2) : NewInt → X := by
  apply Quot.lift f
  intro a b
  simp [make_twelve_equal_two]
  intro ha hb
  rw [ha, hb, hf]

example {X:Type} {f:ℤ → X} (hf: f 12 = f 2) (n:ℤ) : NewInt.quot hf (n:NewInt) = f n := rfl

/-- Exercise A.7.1 -/
example {a b c d:ℝ} (hab: a = b) (hcd : c = d) : a + d = b + c := by
  sorry
