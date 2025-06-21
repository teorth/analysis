import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.6

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
-
-/

namespace Chapter9

/-- Definition 9.6.1 -/
abbrev BddAboveOn (f:ℝ → ℝ) (X:Set ℝ) : Prop :=
  ∃ M, ∀ x ∈ X, f x ≤ M

abbrev BddBelowOn (f:ℝ → ℝ) (X:Set ℝ) : Prop :=
  ∃ M, ∀ x ∈ X, -M ≤ f x

abbrev BddOn (f:ℝ → ℝ) (X:Set ℝ) : Prop :=
  ∃ M, ∀ x ∈ X, |f x| ≤ M

/-- Remark 9.6.2 -/
theorem BddOn.iff (f:ℝ → ℝ) (X:Set ℝ) :
  BddOn f X ↔ BddAboveOn f X ∧ BddBelowOn f X := by
  sorry

theorem BddOn.iff' (f:ℝ → ℝ) (X:Set ℝ) :
  BddOn f X ↔ Bornology.IsBounded (f '' X) := by
  sorry

example : Continuous (fun x:ℝ ↦ x) := by sorry

example : ¬ BddOn (fun x:ℝ ↦ x) Set.univ  := by sorry

example : BddOn (fun x:ℝ ↦ x) (Set.Icc 1 2) := by sorry

example : ContinuousOn (fun x:ℝ ↦ 1/x) (Set.Ioo 0 1) := by sorry

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (Set.Ioo 0 1) := by sorry

/-- Lemma 7.6.3 -/
theorem BddOn.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (Set.Icc a b) ) :
  BddOn f (Set.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hunbound
  simp [BddOn] at hunbound
  set x := fun (n:ℕ) ↦ (hunbound n).choose
  have hx (n:ℕ) : a ≤ x n ∧ x n ≤ b ∧ n < |f (x n)| := (hunbound n).choose_spec
  set X := Set.Icc a b
  have hXclosed : IsClosed X := Icc_closed (by linarith)
  have hXbounded : Bornology.IsBounded X := Icc_bounded _ _
  have haX (n:ℕ): x n ∈ X := by simp [X]; exact ⟨ (hx n).1, (hx n).2.1 ⟩
  obtain ⟨ n, hn, ⟨ L, hLX, hconv ⟩ ⟩ := ((Heine_Borel X).mp ⟨ hXclosed, hXbounded ⟩) x haX
  have why (j:ℕ) : n j ≥ j := by sorry
  replace hf := ContinuousOn.continuousWithinAt hf hLX
  rw [ContinuousWithinAt.iff] at hf
  replace hf := Convergesto.comp (AdherentPt.of_mem hLX) hf (fun j ↦ haX (n j)) hconv
  replace hf := Metric.isBounded_range_of_tendsto _ hf
  rw [isBounded_def] at hf
  obtain ⟨ M, hpos, hM ⟩ := hf
  obtain ⟨ j, hj ⟩ := exists_nat_gt M
  replace hx := (hx (n j)).2.2
  replace hM : f (x (n j)) ∈ Set.Icc (-M) M := by
    apply hM; simp
  simp [←abs_le] at hM
  have : n j ≥ (j:ℝ) := by simp [why j]
  linarith

/-- Definition 7.6.5 -/
abbrev HasMaxAt (f:ℝ → ℝ) (X:Set ℝ) (x₀:ℝ) : Prop :=
  ∀ x ∈ X, f x ≤ f x₀

abbrev HasMinAt (f:ℝ → ℝ) (X:Set ℝ) (x₀:ℝ) : Prop :=
  ∀ x ∈ X, f x₀ ≤ f x

/-- Remark 7.6.6 -/
theorem BddAboveOn.hasMaxAt {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: HasMaxAt f X x₀): BddAboveOn f X := by sorry

theorem BddBelowOn.hasMinAt {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: HasMinAt f X x₀): BddBelowOn f X := by sorry

/-- Proposition 9.6.7 (Maximum principle) -/
theorem HasMaxAt.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (Set.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, HasMaxAt f (Set.Icc a b) xmax := by
  -- This proof is written to follow the structure of the original text.
  sorry -- TODO

theorem HasMinAt.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (Set.Icc a b)) :
  ∃ xmin ∈ Set.Icc a b, HasMinAt f (Set.Icc a b) xmin := by
  sorry

example : HasMaxAt (fun x ↦ x^2) (Set.Icc (-2) 2) 2 := by sorry

example : HasMaxAt (fun x ↦ x^2) (Set.Icc (-2) 2) (-2) := by sorry

theorem sSup.of_hasMaxAt {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: HasMaxAt f X x₀) :
  sSup (f '' X) = f x₀ := by
  sorry -- TODO

theorem sInf.of_hasMinAt {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: HasMinAt f X x₀) :
  sInf (f '' X) = f x₀ := by
  sorry -- TODO

theorem sSup.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (Set.Icc a b)) : ∃ xmax ∈ Set.Icc a b, sSup (f '' Set.Icc a b) = f xmax := by
  obtain ⟨ xmax, hmax, hhas ⟩ := HasMaxAt.of_continuous_on_compact h f hf
  exact ⟨ xmax, hmax, sSup.of_hasMaxAt hhas ⟩

theorem sInf.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (Set.Icc a b)) : ∃ xmin ∈ Set.Icc a b, sInf (f '' Set.Icc a b) = f xmin := by
  obtain ⟨ xmin, hmin, hhas ⟩ := HasMinAt.of_continuous_on_compact h f hf
  exact ⟨ xmin, hmin, sInf.of_hasMinAt hhas ⟩

/-- Exercise 9.6.1 -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (Set.Ioo 1 2) ∧ BddOn f (Set.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, HasMinAt f (Set.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, HasMaxAt f (Set.Ioo 1 2) x₀
  := by sorry

/-- Exercise 9.6.1 -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (Set.Ioo 1 2) ∧ BddOn f (Set.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, HasMaxAt f (Set.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, HasMinAt f (Set.Ioo 1 2) x₀
  := by sorry

/-- Exercise 9.6.1 -/
example : ∃ f: ℝ → ℝ, BddOn f (Set.Icc (-1) 1) ∧
  ¬ ∃ x₀ ∈ Set.Icc (-1) 1, HasMinAt f (Set.Icc (-1) 1) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Icc (-1) 1, HasMaxAt f (Set.Icc (-1) 1) x₀
  := by sorry

/-- Exercise 9.6.1 -/
example : ∃ f: ℝ → ℝ, ¬ BddAboveOn f (Set.Icc (-1) 1) ∧ ¬ BddBelowOn f (Set.Icc (-1) 1) := by sorry


end Chapter9
