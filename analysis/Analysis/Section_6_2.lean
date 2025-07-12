import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.2

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals `EReal`, particularly with regard to the supremum
  operation `sSup` and infimum operation `sInf`.

-/

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  rw [EReal.forall]
  simp

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) :=  add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  unfold IsFinite IsInfinite
  rcases EReal.def x with h | h | h
  all_goals simp [h]
  obtain ⟨ y, rfl ⟩ := h
  simp

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  rcases EReal.def x with hx | rfl | rfl
  all_goals rcases EReal.def y with hy | rfl | rfl
  all_goals simp
  obtain ⟨ x', rfl ⟩ := hx
  obtain ⟨ y', rfl ⟩ := hy
  simp

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by sorry

/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := by sorry

/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := by sorry

/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by sorry

#check instCompleteLinearOrderEReal

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := by sorry

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := by sorry

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := by sorry

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := by sorry

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := by sorry

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := by sorry

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := by sorry

/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]
    congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm
    convert WithBot.coe_sSup' _ _
    . simp [hnon]
    exact Monotone.map_bddAbove WithTop.coe_mono hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by
    congr; symm
    exact WithTop.coe_sSup' hbound
  _ = _ := by rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  rcases EReal.def b with hb' | rfl | rfl
  . obtain ⟨ y, rfl ⟩ := hb'
    simp
    contrapose! hunbound
    exact ⟨ y, hunbound ⟩
  . simp at hb
  simp
  exact hnon

/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) :=
  (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]
  constructor
  . intro h a ha
    specialize h (-a) (by simp [ha])
    exact neg_le_neg_iff.mp h
  intro h a ha
  specialize h ha
  exact EReal.le_neg_of_le_neg h

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem]
  sorry

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup]
  sorry

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

example : sInf Example_6_2_8 = (0.9:ℝ) := by sorry

example : sSup Example_6_2_8 = 1 := by sorry

/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

example : sInf Example_6_2_9 = 1 := by sorry

example : sSup Example_6_2_9 = ⊤ := by sorry

example : sInf (∅ : Set EReal) = ⊤ := by sorry

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by sorry

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sSup E := by sorry

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sInf E := by sorry

/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sSup E ≤ M := by sorry

/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sInf E ≥ M := by sorry

#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib extended reals.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:Chapter5.ExtendedReal) : EReal := match x with
  | real r => ((Chapter5.Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by sorry

theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by sorry

noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal where
  toFun := toEReal
  invFun := sorry
  left_inv x := by
    sorry
  right_inv x := by
    sorry
