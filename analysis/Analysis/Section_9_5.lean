import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Left and right limits
-/

namespace Chapter9

/-- Definition 9.5.1.  We give left and right limits the "junk" value of 0 if the limit does not exist. -/
abbrev right_limit_exists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Ioi x₀)) (nhds L)

open Classical in
noncomputable abbrev right_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h : right_limit_exists X f x₀ then h.choose else 0

abbrev left_limit_exists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Iio x₀)) (nhds L)

open Classical in
noncomputable abbrev left_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h: left_limit_exists X f x₀ then h.choose else 0

theorem right_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ Set.Ioi x₀))
  (h: Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Ioi x₀)) (nhds L)) : right_limit X f x₀ = L := by
  have h' : right_limit_exists X f x₀ := by use L
  simp [right_limit, h']
  have hne : (nhds x₀ ⊓ Filter.principal (X ∩ Set.Ioi x₀)).NeBot := by
    rwa [←nhdsWithin.eq_1, ←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem left_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ Set.Iio x₀)) (h: Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Iio x₀))
  (nhds L)) : left_limit X f x₀ = L := by
  have h' : left_limit_exists X f x₀ := by use L
  simp [left_limit, h']
  have hne : (nhds x₀ ⊓ Filter.principal (X ∩ Set.Iio x₀)).NeBot := by
    rwa [←nhdsWithin.eq_1, ←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

  theorem right_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: right_limit_exists X f x₀) : Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Ioi x₀)) (nhds (right_limit X f x₀)) := by
    simp [right_limit, h]
    convert h.choose_spec

theorem left_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: left_limit_exists X f x₀) : Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Iio x₀)) (nhds (left_limit X f x₀)) := by
  simp [left_limit, h]
  convert h.choose_spec

/-- Example 9.5.2.  The second part of this example is no longer operative as we assign "junk" values to our functions instead of leaving them undefined. -/
example : right_limit Set.univ Real.sign 0 = 1 := by sorry

example : left_limit Set.univ Real.sign 0 = -1 := by sorry

theorem right_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ Set.Ioi x₀))
  (h: right_limit_exists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ Set.Ioi x₀)
  (hconv: Filter.Tendsto a Filter.atTop (nhds x₀)) :
  Filter.Tendsto (fun n ↦ f (a n)) Filter.atTop (nhds (right_limit X f x₀)) := by
  obtain ⟨ L, hL ⟩ := h
  apply Convergesto.comp had _ ha hconv
  rwa [Convergesto.iff, right_limit.eq had hL]

theorem left_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ Set.Iio x₀))
  (h: left_limit_exists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ Set.Iio x₀)
  (hconv: Filter.Tendsto a Filter.atTop (nhds x₀)) :
  Filter.Tendsto (fun n ↦ f (a n)) Filter.atTop (nhds (left_limit X f x₀)) := by
  obtain ⟨ L, hL ⟩ := h
  apply Convergesto.comp had _ ha hconv
  rwa [Convergesto.iff, left_limit.eq had hL]

/-- Proposition 9.5.3 -/
theorem ContinuousAt.iff_eq_left_right_limit {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: x₀ ∈ X)
  (had_left: AdherentPt x₀ (X ∩ Set.Iio x₀)) (had_right: AdherentPt x₀ (X ∩ Set.Ioi x₀)) :
  ContinuousWithinAt f X x₀ ↔ right_limit_exists X f x₀ ∧ left_limit_exists X f x₀ ∧
  right_limit X f x₀ = f x₀ ∧ left_limit X f x₀ = f x₀ := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . sorry
  rintro ⟨ hre, hle, hright, lheft ⟩
  set L := f x₀
  have := (ContinuousWithinAt.tfae X f h).out 0 2
  rw [this]
  intro ε hε
  replace hre := right_limit.eq' hre
  replace hle := left_limit.eq' hle
  rw [hright, ←Convergesto.iff] at hre
  rw [lheft, ←Convergesto.iff] at hle
  simp [Convergesto, Real.close_near, Real.close_fn] at hre hle
  specialize hre ε hε
  specialize hle ε hε
  obtain ⟨ δ_plus, hδ_plus, hre ⟩ := hre
  obtain ⟨ δ_minus, hδ_minus, hle ⟩ := hle
  use min δ_plus δ_minus, (by positivity)
  intro x hx hxx₀
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  . sorry
  . sorry
  sorry

abbrev has_jump_discontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  right_limit_exists X f x₀ ∧ left_limit_exists X f x₀ ∧ right_limit X f x₀ ≠ left_limit X f x₀

example : has_jump_discontinuity Set.univ Real.sign 0 := by sorry

abbrev has_removable_discontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  right_limit_exists X f x₀ ∧ left_limit_exists X f x₀ ∧ right_limit X f x₀ = left_limit X f x₀ ∧
  right_limit X f x₀ ≠ f x₀

example : has_removable_discontinuity Set.univ f_9_3_17 0 := by sorry

example : ¬ has_removable_discontinuity Set.univ (fun x ↦ 1/x) 0 := by sorry

example : ¬ has_jump_discontinuity Set.univ (fun x ↦ 1/x) 0 := by sorry

/- Exercise 9.5.1: Write down a definition of what it would mean for a limit of a function to be `+∞` or `-∞`, apply to `fun x ↦ 1/x`, and state and prove a version of Proposition 9.3.9. -/


end Chapter9
