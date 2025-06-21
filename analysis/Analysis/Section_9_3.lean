import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_1

/-!
# Analysis I, Section 9.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Limits of continuous functions
- Connection with Mathilb's filter convergence concepts
- Limit laws for functions

Technical point: in the text, the functions `f` studied are defined only on subsets `X` of `ℝ`, and left undefined elsewhere.  However, in Lean, this then creates some fiddly conversions when trying to restrict `f` to various subsets of `X` (which, technically, are not precisely subsets of `ℝ`, though they can be coerced to such).  To avoid this issue we will deviate from the text by having our functions defined on all of `ℝ` (with the understanding that they are assigned "junk" values outside of the domain `X` of interest).
-/

/-- Definition 9.3.1 -/
abbrev Real.close_fn (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) : Prop :=
  ∀ x ∈ X, |f x - L| < ε

/-- Definition 9.3.3 -/
abbrev Real.close_near (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop :=
  ∃ δ > 0, ε.close_fn (X ∩ Set.Ioo (x₀-δ) (x₀+δ)) f L

namespace Chapter9

/-- Example 9.3.2 -/
example : (5:ℝ).close_fn (Set.Icc 1 3) (fun x ↦ x^2) 4 := by sorry

/-- Example 9.3.2 -/
example : (0.41:ℝ).close_fn (Set.Icc 1.9 2.1) (fun x ↦ x^2) 4 := by sorry

/-- Example 9.3.4 -/
example: ¬ (0.1:ℝ).close_fn (Set.Icc 1 3) (fun x ↦ x^2) 4 := by
  sorry

/-- Example 9.3.4 -/
example: (0.1:ℝ).close_near (Set.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  sorry

/-- Example 9.3.5 -/
example: ¬ (0.1:ℝ).close_fn (Set.Icc 1 3) (fun x ↦ x^2) 9 := by
  sorry

/-- Example 9.3.5 -/
example: (0.1:ℝ).close_near (Set.Icc 1 3) (fun x ↦ x^2) 9 3 := by
  sorry

/-- Definition 9.3.6 (Convergence of functions at a point)-/
abbrev Convergesto (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.close_near X f L x₀

/-- Connection with Mathlib filter convergence concepts -/
theorem Convergesto.iff (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) :
  Convergesto X f L x₀ ↔ Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal X) (nhds L) := by
  unfold Convergesto Real.close_near Real.close_fn
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  apply forall_congr'; intro ε
  apply imp_congr_right; intro hε
  rw [Filter.eventually_inf_principal]
  simp [Filter.Eventually, mem_nhds_iff_exists_Ioo_subset]
  constructor
  . rintro ⟨ δ, hpos, hδ ⟩
    use (x₀-δ), (x₀+δ), ⟨ by linarith, by linarith⟩
    intro x
    simp
    exact fun h1 h2 hX ↦ hδ x hX h1 h2
  rintro ⟨ l, u, ⟨ h1, h2 ⟩, h ⟩
  have h1' : 0 < x₀ - l := by linarith
  have h2' : 0 < u - x₀ := by linarith
  set δ := min (x₀ - l) (u - x₀)
  have hδ1 : δ ≤ x₀ - l := min_le_left _ _
  have hδ2 : δ ≤ u - x₀ := min_le_right _ _
  use δ, (by positivity)
  intro x hxX hx1 hx2
  have hmem : x ∈ Set.Ioo l u := by
    simp
    exact ⟨ by linarith, by linarith ⟩
  specialize h hmem
  simp [hxX] at h; exact h

/-- Example 9.3.8 -/
example: Convergesto (Set.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  sorry

/-- Proposition 9.3.9 / Exercise 9.3.1 -/
theorem Convergesto.iff_conv {E:Set ℝ} (f: ℝ → ℝ) (L:ℝ) {x₀:ℝ} (h: AdherentPt x₀ E) :
  Convergesto E f L x₀ ↔ ∀ a:ℕ → ℝ, (∀ n:ℕ, a n ∈ E) →
  Filter.Tendsto a Filter.atTop (nhds x₀) →
  Filter.Tendsto (fun n ↦ f (a n)) Filter.atTop (nhds L) := by
  sorry

theorem Convergesto.comp {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (hf: Convergesto E f L x₀) {a:ℕ → ℝ} (ha: ∀ n:ℕ, a n ∈ E) (hconv: Filter.Tendsto a Filter.atTop (nhds x₀)) :
  Filter.Tendsto (fun n ↦ f (a n)) Filter.atTop (nhds L) := by
  rw [iff_conv f L h] at hf
  exact hf a ha hconv

-- Remark 9.3.11 may possibly be inaccurate, in that one may be able to safely delete the hypothesis `AdherentPt x₀ E` in the above theorems.  This is something that formalization might be able to clarify!  If so, the hypothesis may also be deletable in several of the theorems below.

/-- Corollary 9.3.13 -/
theorem Convergesto.uniq {E:Set ℝ} {f: ℝ → ℝ} {L L':ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hf': Convergesto E f L' x₀) : L = L' := by
  -- This proof is written to follow the structure of the original text.
  let ⟨ a, ha, hconv ⟩ := (limit_of_AdherentPt _ _).mp h
  have hL := hf.comp h ha hconv
  have hL' := hf'.comp h ha hconv
  exact tendsto_nhds_unique  hL hL'

/-- Proposition 9.3.14 (Limit laws for functions) -/
theorem Convergesto.add {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f + g) (L + M) x₀ := by
    -- This proof is written to follow the structure of the original text.
    rw [iff_conv _ _ h] at hf hg ⊢
    intro a ha hconv
    specialize hf a ha hconv
    specialize hg a ha hconv
    convert Filter.Tendsto.add hf hg using 1

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.sub {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f - g) (L - M) x₀ := by
    sorry

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.max {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (max f g) (max L M) x₀ := by
    sorry

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.min {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (min f g) (min L M) x₀ := by
    sorry

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.smul {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (c:ℝ) :
  Convergesto E (c • f) (c * L) x₀ := by
    sorry

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.mul {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f * g) (L * M) x₀ := by
    sorry

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2.  The hypothesis in the book that g is non-vanishing on E can be dropped. -/
theorem Convergesto.div {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (hM: M ≠ 0)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f / g) (L / M) x₀ := by
    sorry

theorem Convergesto.const {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (c:ℝ)
  : Convergesto E (fun x ↦ c) c x₀ := by
  sorry

theorem Convergesto.id {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  : Convergesto E (fun x ↦ x) x₀ x₀ := by
  sorry

theorem Convergesto.sq {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  : Convergesto E (fun x ↦ x^2) x₀ (x₀^2) := by
  sorry

theorem Convergesto.linear {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (c:ℝ)
  : Convergesto E (fun x ↦ c * x) x₀ (c * x₀) := by
  sorry

theorem Convergesto.quadratic {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (c d:ℝ)
  : Convergesto E (fun x ↦ x^2 + c * x + d) x₀ (x₀^2 + c * x₀ + d) := by
  sorry

theorem Convergesto.restrict {X Y:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ X) (hf: Convergesto X f L x₀) (hY: Y ⊆ X) : Convergesto Y f L x₀ := by
  sorry

theorem Real.sign_def (x:ℝ) : Real.sign x = if x < 0 then -1 else if x > 0 then 1 else 0 := rfl

/-- Example 9.3.16 -/
theorem Convergesto.sign_right : Convergesto (Set.Ioi 0) Real.sign 1 0 := by sorry

/-- Example 9.3.16 -/
theorem Convergesto.sign_left : Convergesto (Set.Iio 0) Real.sign (-1) 0 := by sorry

/-- Example 9.3.16 -/
theorem Convergesto.sign_all : ¬ ∃ L, Convergesto (Set.univ) Real.sign L 0 := by sorry

noncomputable abbrev f_9_3_17 : ℝ → ℝ := fun x ↦ if x = 0 then 1 else 0

theorem Convergesto.f_9_3_17_remove : Convergesto (Set.univ \ {0}) f_9_3_17 0 0 := by sorry

theorem Convergesto.f_9_3_17_all : ¬ ∃ L, Convergesto (Set.univ) f_9_3_17 L 0 := by sorry

/-- Proposition 9.3.18 / Exercise 9.3.3 -/
theorem Convergesto.local {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) {δ:ℝ} (hδ: δ > 0) :
  Convergesto E f L x₀ ↔ Convergesto (E ∩ Set.Ioo (x₀-δ) (x₀+δ)) f L x₀ := by
    sorry

/-- Example 9.3.19.  The point of this example is somewhat blunted by the ability to remove the hypothesis that `g` is non-zero from the relevant part of Proposition 9.3.14 -/
example : Convergesto Set.univ (fun x ↦ (x+2)/(x+1)) (4/3:ℝ) 2 := by sorry

/-- Example 9.3.20 -/
example : Convergesto (Set.univ \ {1}) (fun x ↦ (x^2-1)/(x-1)) 2 1 := by sorry

open Classical in
/-- Example 9.3.21 -/
noncomputable abbrev f_9_3_21 : ℝ → ℝ := fun x ↦ if x ∈ (fun q:ℚ ↦ (q:ℝ)) '' Set.univ then 1 else 0

example : Filter.Tendsto (fun n ↦ f_9_3_21 (1/n:ℝ)) Filter.atTop (nhds 1) := by sorry

example : Filter.Tendsto (fun n ↦ f_9_3_21 ((Real.sqrt 2)/n:ℝ)) Filter.atTop (nhds 0) := by sorry

example : ¬ ∃ L, Convergesto Set.univ f_9_3_21 L 0 := by sorry

/- Exercise 9.3.4: State a definition of limit superior and limit inferior for functions, and prove an analogue of Proposition 9.3.9 for those definitions. -/

/-- Exercise 9.3.5 (Continuous version of squeeze test) -/
theorem Convergesto.squeeze {E:Set ℝ} {f g h: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (had: AdherentPt x₀ E)
  (hfg: ∀ x ∈ E, f x ≤ g x) (hgh: ∀ x ∈ E, g x ≤ h x)
  (hf: Convergesto E f L x₀) (hh: Convergesto E h L x₀) :
  Convergesto E g L x₀ := by
    sorry


end Chapter9
