import Mathlib.Tactic
import Analysis.Section_11_1

/-!
# Analysis I, Section 11.2: Piecewise constant functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Piecewise constant functions.
- The piecewise constant integral.

-/

namespace Chapter11
open BoundedInterval

/-- Definition 11.2.1 -/
abbrev Constant {X Y:Type} (f: X → Y) : Prop := ∃ c, ∀ x, f x = c

open Classical in
noncomputable abbrev constant_value {X Y:Type} [hY: Nonempty Y] (f:X → Y) : Y :=
  if h: Constant f then h.choose else hY.some

theorem Constant.eq {X Y:Type} {f: X → Y} [Nonempty Y] (h: Constant f) (x:X) :
  f x = constant_value f := by simp [constant_value, h]; apply h.choose_spec

theorem Constant.of_const {X Y:Type} {f:X → Y} {c:Y} (h: ∀ x, f x = c) :
  Constant f := by use c

theorem Constant.const_eq {X Y:Type} {f:X → Y} [hX: Nonempty X] [Nonempty Y] {c:Y} (h: ∀ x, f x = c) :
  constant_value f = c := by rw [←eq (of_const h) hX.some, h hX.some]

theorem Constant.of_subsingleton {X Y:Type} [hs: Subsingleton X] [hY: Nonempty Y] {f:X → Y} :
  Constant f := by
  by_cases h:Nonempty X
  . use f h.some; intros; congr; exact hs.elim _ h.some
  simp at h; exact ⟨ hY.some, h.elim ⟩

abbrev ConstantOn (f: ℝ → ℝ) (X: Set ℝ) : Prop := Constant (fun x : X ↦ f ↑x)

noncomputable abbrev constant_value_on (f:ℝ → ℝ) (X: Set ℝ) : ℝ := constant_value (fun x : X ↦ f ↑x)

theorem ConstantOn.eq {f: ℝ → ℝ} {X: Set ℝ} (h: ConstantOn f X) {x:ℝ} (hx: x ∈ X) :
  f x = constant_value_on f X := by
  convert Constant.eq h ⟨ _, hx ⟩

theorem ConstantOn.of_const {f:ℝ → ℝ} {X: Set ℝ} {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  ConstantOn f X := ⟨ c, by grind ⟩

theorem ConstantOn.of_const' (c:ℝ) (X:Set ℝ): ConstantOn (fun _ ↦ c) X := of_const (c := c) (by simp)

theorem ConstantOn.const_eq {f:ℝ → ℝ} {X: Set ℝ} (hX: X.Nonempty) {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  constant_value_on f X = c := by
    rw [←eq (of_const h) hX.some_mem, h _ hX.some_mem]

theorem ConstantOn.congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) : ConstantOn f X ↔ ConstantOn g X := by
  simp_rw [ConstantOn, iff_iff_eq]; congr; grind

theorem ConstantOn.congr' {f g: ℝ → ℝ} {X: Set ℝ} (hf: ConstantOn f X) (h: ∀ x ∈ X, f x = g x) : ConstantOn g X := (congr h).mp hf

theorem ConstantOn.of_subsingleton {f: ℝ → ℝ} {X: Set ℝ} [Subsingleton X] :
  ConstantOn f X := Constant.of_subsingleton

theorem constant_value_on_congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) :
  constant_value_on f X = constant_value_on g X := by
  simp [constant_value_on]; congr; grind

/-- Definition 11.2.3 (Piecewise constant functions I) -/
abbrev PiecewiseConstantWith (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : Prop := ∀ J ∈ P, ConstantOn f (J:Set ℝ)

theorem PiecewiseConstantWith.def (f:ℝ → ℝ) {I: BoundedInterval} {P: Partition I} :
  PiecewiseConstantWith f P ↔ ∀ J ∈ P, ∃ c, ∀ x ∈ J, f x = c := by
    simp [PiecewiseConstantWith, ConstantOn, Constant, mem_iff]

theorem PiecewiseConstantWith.congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantWith f P ↔ PiecewiseConstantWith g P := by
  simp [PiecewiseConstantWith]; peel with J hJ
  apply ConstantOn.congr; have := P.contains _ hJ; grind [subset_iff]

/-- Definition 11.2.5 (Piecewise constant functions I) -/
abbrev PiecewiseConstantOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ P : Partition I, PiecewiseConstantWith f P

theorem PiecewiseConstantOn.def (f:ℝ → ℝ) (I: BoundedInterval):
  PiecewiseConstantOn f I ↔ ∃ P : Partition I, ∀ J ∈ P, ConstantOn f (J:Set ℝ) := by rfl

theorem PiecewiseConstantOn.congr {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantOn f I ↔ PiecewiseConstantOn g I := by
  simp_rw [PiecewiseConstantOn, PiecewiseConstantWith.congr h]

theorem PiecewiseConstantOn.congr' {f g: ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) (h: ∀ x ∈ (I:Set ℝ), f x = g x) : PiecewiseConstantOn g I := (congr h).mp hf

/-- Example 11.2.4 / Example 11.2.6 -/
noncomputable abbrev f_11_2_4 : ℝ → ℝ := fun x ↦
  if x < 1 then 0 else  -- junk value
    if x < 3 then 7 else
      if x = 3 then 4 else
        if x < 6 then 5 else
          if x = 6 then 2 else
            0 -- junk value

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use Partition.mk { Ico 1 3, Icc 3 3, Ioo 3 6, Icc 6 6} ?_ ?_
  . sorry
  . sorry
  sorry

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use Partition.mk { Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 3, Ioo 3 5, Ico 5 6, Icc 6 6} ?_ ?_
  . sorry
  . sorry
  sorry

/-- Example 11.2.6 -/
theorem ConstantOn.piecewiseConstantOn {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f (I:Set ℝ)) :
  PiecewiseConstantOn f I := by sorry

/-- Lemma 11.2.7 / Exercise 11.2.1 -/
theorem PiecewiseConstantWith.mono {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I} (hPP': P ≤ P')
  (hP: PiecewiseConstantWith f P) : PiecewiseConstantWith f P' := by
  sorry

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I := by
  sorry

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f - g) I := by
  sorry

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.max {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (max f g) I := by
  sorry

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.min {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (min f g) I := by
  sorry

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.mul {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f * g) I := by
  sorry

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.smul {f: ℝ → ℝ} {I: BoundedInterval}
  (c:ℝ) (hf: PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by
  sorry

/-- Lemma 11.2.8 / Exercise 11.2.2.  I believe the hypothesis that {name}`g` does not vanish is not needed. -/
theorem PiecewiseConstantOn.div {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn f I) : PiecewiseConstantOn (f / g) I := by
  sorry

/-- Definition 11.2.9 (Piecewise constant integral I)-/
noncomputable abbrev PiecewiseConstantWith.integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I)  :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * |J|ₗ

theorem PiecewiseConstantWith.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f P = integ g P := by
  apply Finset.sum_congr rfl; intro J hJ; congr 1; apply constant_value_on_congr
  have := P.contains _ hJ; grind [subset_iff]

/-- Example 11.2.12 -/
noncomputable abbrev f_11_2_12 : ℝ → ℝ := fun x ↦
    if x < 3 then 2 else
      if x = 3 then 4 else
        6

noncomputable abbrev P_11_2_12 : Partition (Icc 1 4) :=
  ((⊥: Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))

example : PiecewiseConstantWith f_11_2_12 P_11_2_12 := by
  sorry

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12 = 10 := by
  sorry

noncomputable abbrev P_11_2_12' : Partition (Icc 1 4) :=
  ((((⊥: Partition (Ico 1 2)).join (⊥ : Partition (Ico 2 3))
  (join_Ico_Ico (by norm_num) (by norm_num) )).join
  (⊥: Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num))).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))).add_empty

example : PiecewiseConstantWith f_11_2_12 P_11_2_12' := by
  sorry

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12' = 10 := by
  sorry

/-- Proposition 11.2.13 (Piecewise constant integral is independent of partition) / Exercise 11.2.3 -/
theorem PiecewiseConstantWith.integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') : integ f P = integ f P' := by
  sorry

open Classical in
/-- Definition 11.2.14 (Piecewise constant integral II)  -/
noncomputable abbrev PiecewiseConstantOn.integ (f:ℝ → ℝ) (I: BoundedInterval) :
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.integ f h.choose else 0

noncomputable abbrev PiecewiseConstantOn.integ' {f:ℝ → ℝ} {I: BoundedInterval} (_:PiecewiseConstantOn f I) := integ f I

theorem PiecewiseConstantOn.integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) : integ f I = PiecewiseConstantWith.integ f P := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [integ, h']; exact PiecewiseConstantWith.integ_eq h'.choose_spec h

theorem PiecewiseConstantOn.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f I = integ g I := by
  by_cases hf : PiecewiseConstantOn f I
  <;> (have hg := hf; rw [congr h] at hg; simp [integ, hf, hg])
  rw [PiecewiseConstantWith.integ_congr h, ←integ_def hg.choose_spec, ←integ_def]
  rw [←PiecewiseConstantWith.congr h]; exact hf.choose_spec

/-- Example 11.2.15 -/
example : PiecewiseConstantOn.integ f_11_2_4 (Icc 1 6) = 10 := by
  sorry

/-- Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f + g) I = integ f I + integ g I := by
  sorry

/-- Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ) (hf: PiecewiseConstantOn f I) :
  integ (c • f) I = c * integ f I
   := by
  sorry

/-- Theorem 11.2.16 (c) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f - g) I = integ f I - integ g I := by
  sorry

/-- Theorem 11.2.16 (d) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, 0 ≤ f x)
  (hf: PiecewiseConstantOn f I) :
  0 ≤ integ f I := by
  sorry

/-- Theorem 11.2.16 (e) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_mono {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, f x ≤ g x)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ f I ≤ integ g I := by
  sorry


/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const (c: ℝ) (I: BoundedInterval) :
  integ (fun _ ↦ c) I = c * |I|ₗ := by
  sorry

/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const' {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f I) :
  integ f I = (constant_value_on f I) * |I|ₗ := by
  sorry

open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  sorry

open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  sorry

/-- Theorem 11.2.16 (h) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  (f: ℝ → ℝ) : PiecewiseConstantOn f K ↔ PiecewiseConstantOn f I ∧ PiecewiseConstantOn f J := by
  sorry

/-- Theorem 11.2.16 (h) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) :
  integ f K = integ f I + integ f J := by
  sorry

end Chapter11
