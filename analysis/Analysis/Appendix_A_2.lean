import Mathlib.Tactic

/-!
# Analysis I, Appendix A.2: Implication

An introduction to implications.  Showcases some basic tactics and Lean syntax.

-/

example {X Y: Prop} (hX: X) : (X → Y) ↔ Y := by tauto

example {X Y: Prop} (hX: ¬X) : X → Y := by
  intro hX'
  contradiction

example {X Y: Prop} (hXY: X → Y) (hX: X) : Y := by
  exact hXY hX

example {X Y: Prop} (hXY: X → Y) (hX: X) : Y := hXY hX

example {X Y: Prop} (hXY: X → Y) (hY: ¬ Y) : ¬ X := by
  contrapose! hY
  exact hXY hY


theorem example_A_2_1 (x:ℤ) : x = 2 → x^2 = 4 := by
  intro h
  rw [h]
  rfl

example : (2:ℤ) = 2 → (2:ℤ)^2 = 4 := example_A_2_1 2

example : (3:ℤ) = 2 → (3:ℤ)^2 = 4 := example_A_2_1 3

example : (-2:ℤ) = 2 → (-2:ℤ)^2 = 4 := example_A_2_1 (-2)

#check _root_.not_imp

example : ¬ ((2+2=4) → (4+4)=2) := by
  rw [Classical.not_imp]
  constructor
  . norm_num
  norm_num

example {X Y: Prop} : (X → Y) ↔ (Y ≥ X) := by simp

example {X Y: Prop} : (X → Y) ↔ ((¬X) ≥ ¬Y) := by simp; tauto

example {John_left_at_five John_here_now:Prop}
  (h1: John_left_at_five → John_here_now)
  (h2: ¬ John_here_now) :
  ¬ John_left_at_five := by
  contrapose! h2
  exact h1 h2

example {Washington_capital_US:Prop} (h: Washington_capital_US) : (1+1=2) → Washington_capital_US := by
  intro h'
  exact h

example {NYC_capital_US:Prop} : (2+2=3) → NYC_capital_US := by
  intro h
  simp at h

/-- Proposition A.2.2 -/
example : ((2+2:ℤ)=5) → (4=(10-4:ℤ)) := by
  intro h
  have : (4 + 4:ℤ) = 10 := by
    replace h := congr(2*$h)
    convert h using 1
  rwa [←eq_sub_iff_add_eq] at this

/-- Theorem A.2.4 -/
theorem theorem_A_2_4 (n:ℤ) : Even (n * (n+1)) := by
  have : Even n ∨ Odd n := Int.even_or_odd n
  obtain heven | hodd := this  -- can also use `rcases this with heven | hodd`
  . exact Even.mul_right heven _
  have : Even (n+1) := Odd.add_one hodd
  exact Even.mul_left this _

/-- Corollary A.2.5 -/
example :
  let n:ℤ := (253+142)*123-(423+198)^342+538-213
  Even (n * (n+1)) := theorem_A_2_4 _

example : ∀ x:ℝ, x = 2 → x^2 = 4 := by
  intro x h
  simp [h]
  norm_num

example : ¬ ∀ x:ℝ, x^2 = 4 → x = 2 := by
  simp
  use -2
  norm_cast

example {X Y : Prop} : (X ↔ Y) = ((X → Y) ∧ (Y → X)) := by
  simp; tauto

example (x:ℝ) : x = 2 ↔ 2*x = 4 := by
  constructor
  . intro h
    linarith
  intro h
  linarith

example {X Y :Prop} : (X ↔ Y) = (X = Y) := by simp

example : (3 = 2) → (6 = 4) := by simp

example : ∃ (X Y:Prop), (X → Y) ≠ (Y → X) := by
  set x := -2
  use x = 2, x^2 = 4
  simp [x]

theorem contrapositive {X Y: Prop} (hXY: X → Y) : ¬ Y → ¬ X := by
  intro hY
  by_contra hX
  have := hXY hX
  contradiction

theorem imp_example (x:ℝ) : (x = 2) → (x^2 = 4) := by
  intro h
  rw [h]
  norm_num

theorem imp_contrapositive (x:ℝ) : (x^2 ≠ 4) → (x ≠ 2) := by
  convert contrapositive (imp_example x)

/-- Proposition A.2.6 -/
example {x:ℝ} (h:x>0) (hsin: Real.sin x = 1) : x ≥ Real.pi / 2 := by
  by_contra! h'
  have h1 : Real.sin 0 < Real.sin x := by
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two _ _ h
    . have : Real.pi > 0 := Real.pi_pos
      linarith
    linarith
  have h2 : Real.sin x < Real.sin (Real.pi / 2) := by
  -- the <;> tactic applies the next tactic to all currently visible goals.
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two _ _ h' <;> linarith
  simp at h1 h2
  linarith
