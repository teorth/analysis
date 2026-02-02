import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.ContinuousOn
import Analysis.Section_9_3

/-!
# Analysis I, Section 9.4: Continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuity of functions, using the Mathlib notions

-/

namespace Chapter9

/-- Definition 9.4.1.  Here we use the Mathlib definition of continuity.  The hypothesis `x ∈ X` is not needed! -/
theorem ContinuousWithinAt.iff (X:Set ℝ) (f: ℝ → ℝ)  (x₀:ℝ) :
  ContinuousWithinAt f X x₀ ↔ Convergesto X f (f x₀) x₀ := by
  rw [ContinuousWithinAt.eq_1, Convergesto.iff, nhdsWithin.eq_1]

#check ContinuousOn.eq_1
#check continuous_iff_continuousOn_univ
#check continuousWithinAt_univ

/-- Example 9.4.2 --/
example (c x₀:ℝ) : ContinuousWithinAt (fun x ↦ c) .univ x₀ := by sorry

example (c x₀:ℝ) : ContinuousAt (fun x ↦ c) x₀ := by sorry

example (c:ℝ) : ContinuousOn (fun x:ℝ ↦ c) .univ := by sorry

example (c:ℝ) : Continuous (fun x:ℝ ↦ c) := by sorry

/-- Example 9.4.3 --/
example : Continuous (fun x:ℝ ↦ x) := by sorry

/-- Example 9.4.4 --/
example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt Real.sign x₀ := by sorry

example  :¬ ContinuousAt Real.sign 0 := by sorry

/-- Example 9.4.5 --/
example (x₀:ℝ) : ¬ ContinuousAt f_9_3_21 x₀ := by sorry

/-- Example 9.4.6 --/
noncomputable abbrev f_9_4_6 (x:ℝ) : ℝ := if x ≥ 0 then 1 else 0

example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt f_9_4_6 x₀ := by sorry

example : ¬ ContinuousAt f_9_4_6 0 := by sorry

example : ContinuousWithinAt f_9_4_6 (.Ici 0) 0 := by sorry

/-- Proposition 9.4.7 / Exercise 9.4.1.  It is possible that the hypothesis `x₀ ∈ X` is unnecessary. -/
theorem ContinuousWithinAt.tfae (X:Set ℝ) (f: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X) :
  [
    ContinuousWithinAt f X x₀,
    ∀ a:ℕ → ℝ, (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds x₀) → Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)),
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x-x₀| < δ → |f x - f x₀| < ε
  ].TFAE := by
  sorry

/-- Remark 9.4.8 --/
theorem _root_.Filter.Tendsto.comp_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h : x₀ ∈ X)
  (h_cont: ContinuousWithinAt f X x₀) {a: ℕ → ℝ} (ha: ∀ n, a n ∈ X)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)):
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)) := by
  have := (ContinuousWithinAt.tfae X f h).out 0 1
  grind

/- Proposition 9.4.9 -/
theorem ContinuousWithinAt.add {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f + g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.add (AdherentPt.of_mem h) hg using 1


theorem ContinuousWithinAt.sub {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f - g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.sub (AdherentPt.of_mem h) hg using 1

theorem ContinuousWithinAt.max {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (max f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.max (AdherentPt.of_mem h) hg using 1


theorem ContinuousWithinAt.min {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (min f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.min (AdherentPt.of_mem h) hg using 1


theorem ContinuousWithinAt.mul' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f * g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.mul (AdherentPt.of_mem h) hg using 1

theorem ContinuousWithinAt.div' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X) (hM: g x₀ ≠ 0)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f / g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.div (AdherentPt.of_mem h) hM hg using 1

/-- Proposition 9.4.10 / Exercise 9.4.3  -/
theorem Continuous.exp {a:ℝ} (ha: a>0) : Continuous (fun x:ℝ ↦ a ^ x) := by
  sorry

/-- Proposition 9.4.11 / Exercise 9.4.4 -/
theorem Continuous.exp' (p:ℝ) : ContinuousOn (fun x:ℝ ↦ x ^ p) (.Ioi 0) := by
  sorry

/-- Proposition 9.4.12 -/
theorem Continuous.abs : Continuous (fun x:ℝ ↦ |x|) := by
  sorry -- TODO

/-- Proposition 9.4.13 / Exercise 9.4.5 -/
theorem ContinuousWithinAt.comp {X Y: Set ℝ} {f g:ℝ → ℝ} (hf: ∀ x ∈ X, f x ∈ Y) {x₀:ℝ} (hx₀: x ∈ X) (hf_cont: ContinuousWithinAt f X x₀) (hg_cont: ContinuousWithinAt g Y (f x₀)): ContinuousWithinAt (g ∘ f) X x₀ := by sorry

/-- Example 9.4.14 -/
example : Continuous (fun x:ℝ ↦ 3*x + 1) := by
  sorry

example : Continuous (fun x:ℝ ↦ (5:ℝ)^x) := by
  sorry

example : Continuous (fun x:ℝ ↦ (5:ℝ)^(3*x+1)) := by
  sorry

example : Continuous (fun x:ℝ ↦ |x^2-8*x+8|^(Real.sqrt 2) / (x^2 + 1)) := by
  sorry

/-- Exercise 9.4.6 -/
theorem ContinuousOn.restrict {X Y:Set ℝ} {f: ℝ → ℝ} (hY: Y ⊆ X) (hf: ContinuousOn f X) : ContinuousOn f Y := by
  intro x hx
  have h_cont_X := hf x (hY hx)
  unfold ContinuousWithinAt at *
  apply Filter.Tendsto.mono_left h_cont_X
  exact nhdsWithin_mono x hY

/-- Exercise 9.4.7 -/
theorem Continuous.polynomial {n:ℕ} (c: Fin n → ℝ) : Continuous (fun x:ℝ ↦ ∑ i, c i * x ^ (i:ℕ)) := by
  sorry
