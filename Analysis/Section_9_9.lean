import Mathlib.Tactic
import Analysis.Section_6_1
import Mathlib.Data.Nat.Nth
import Analysis.Section_9_6
/-!
# Analysis I, Section 9.9: Uniform continuity

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`UniformContinuousOn`.
- Continuous functions on compact intervals are uniformly continuous.

-/

open Chapter6 Filter

namespace Chapter9

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Icc 0 2) := by
  sorry

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Icc 0 2) := by
  sorry

/-- Example 9.9.1 -/
example (x : ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 1/11
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  extract_lets f ε x₀ δ
  sorry

example (x:ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 0.1
  let δ : ℝ := 1/1010
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  extract_lets -merge f ε x₀ δ -- need the `-merge` flag due to the collision of `ε` and `x₀`
  sorry

example (x:ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  extract_lets g ε x₀ δ
  sorry

example (x₀ x : ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  extract_lets g ε δ
  sorry

/-- Definition 9.9.2.  Here we use the Mathlib term {name}`UniformContinuousOn` -/
theorem UniformContinuousOn.iff (f: ℝ → ℝ) (X:Set ℝ) : UniformContinuousOn f X  ↔
  ∀ ε > (0:ℝ), ∃ δ > (0:ℝ), ∀ x₀ ∈ X, ∀ x ∈ X, δ.Close x x₀ → ε.Close (f x) (f x₀) := by
  simp_rw [Metric.uniformContinuousOn_iff_le, Real.Close]
  grind

theorem ContinuousOn.ofUniformContinuousOn {X:Set ℝ} (f: ℝ → ℝ) (hf: UniformContinuousOn f X) :
  ContinuousOn f X := by
  sorry

example : ¬ UniformContinuousOn (fun x:ℝ ↦ 1/x) (Set.Icc 0 2) := by
  sorry

end Chapter9

/-- Definition 9.9.5.  This is similar but not identical to `Real.close_seq` from Section 6.1. -/
abbrev Real.CloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  (a.m = b.m) ∧ ∀ n ≥ a.m, ε.Close (a n) (b n)

abbrev Real.EventuallyCloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeqs (a.from N) (b.from N)

abbrev Chapter6.Sequence.equiv (a b: Sequence) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyCloseSeqs a b

/-- Remark 9.9.6 -/
theorem Chapter6.Sequence.equiv_iff_rat (a b: Sequence) :
  a.equiv b ↔ ∀ ε > (0:ℚ), (ε:ℝ).EventuallyCloseSeqs a b := by
  sorry

/-- Lemma 9.9.7 / Exercise 9.9.1 -/
theorem Chapter6.Sequence.equiv_iff (a b: Sequence) :
  a.equiv b ↔ atTop.Tendsto (fun n ↦ a n - b n) (nhds 0) := by
  sorry


namespace Chapter9


/-- Proposition 9.9.8 / Exercise 9.9.2 -/
theorem UniformContinuousOn.iff_preserves_equiv {X:Set ℝ} (f: ℝ → ℝ) :
  UniformContinuousOn f X ↔
  ∀ x y: ℕ → ℝ, (∀ n, x n ∈ X) → (∀ n, y n ∈ X) →
  (x:Sequence).equiv (y:Sequence) →
  (f ∘ x:Sequence).equiv (f ∘ y:Sequence) := by
  sorry

/-- Remark 9.9.9 -/
theorem Chapter6.Sequence.equiv_const (x₀: ℝ) (x:ℕ → ℝ) : atTop.Tendsto x (nhds x₀) ↔
  (x:Sequence).equiv (fun n:ℕ ↦ x₀:Sequence) := by
  sorry

/-- Example 9.9.10 -/
noncomputable abbrev f_9_9_10 : ℝ → ℝ := fun x ↦ 1/x

example : (fun n:ℕ ↦ 1/(n+1:ℝ):Sequence).equiv (fun n:ℕ ↦ 1/(2*(n+1):ℝ):Sequence) := by sorry

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by sorry

example (n:ℕ) : 1/(2*(n+1):ℝ) ∈ Set.Ioo 0 2 := by sorry

example : ¬ (fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ)):Sequence).equiv (fun n:ℕ ↦ f_9_9_10 (1/(2*(n+1):ℝ)):Sequence) := by sorry

example : ¬ UniformContinuousOn f_9_9_10 (.Ioo 0 2) := by
  sorry

/-- Example 9.9.11 -/
abbrev f_9_9_11 : ℝ → ℝ := fun x ↦ x^2

example : ((fun n:ℕ ↦ (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ (n+1)+1/(n+1:ℝ)):Sequence) := by
  sorry

example : ¬ ((fun n:ℕ ↦ f_9_9_11 (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ f_9_9_11 ((n+1)+1/(n+1:ℝ))):Sequence) := by
  sorry

example : ¬ UniformContinuousOn f_9_9_11 .univ := by
  sorry

/-- Proposition 9.9.12 / Exercise 9.9.3  -/
theorem UniformContinuousOn.ofCauchy  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x: ℕ → ℝ} (hx: (x:Sequence).IsCauchy) (hmem : ∀ n, x n ∈ X) :
  (f ∘ x:Sequence).IsCauchy := by
  sorry

/-- Example 9.9.13 -/
example : ((fun n:ℕ ↦ 1/(n+1:ℝ)):Sequence).IsCauchy := by
  sorry

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  sorry

example : ¬ ((fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ))):Sequence).IsCauchy := by
  sorry

example : ¬ UniformContinuousOn f_9_9_10 (Set.Ioo 0 2) := by
  sorry

/-- Corollary 9.9.14 / Exercise 9.9.4 -/
theorem UniformContinuousOn.limit_at_adherent  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x₀:ℝ} (hx₀: AdherentPt x₀ X) :
  ∃ L:ℝ, (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  sorry

/-- Proposition 9.9.15 / Exercise 9.9.5 -/
theorem UniformContinuousOn.of_bounded {E X:Set ℝ} {f: ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hEX: E ⊆ X) (hE: Bornology.IsBounded E) :
  Bornology.IsBounded (f '' E) := by
  sorry

/-- Theorem 9.9.16 -/
theorem UniformContinuousOn.of_continuousOn {a b:ℝ} {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) :
  UniformContinuousOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; rw [iff_preserves_equiv] at h
  simp [-Set.mem_Icc] at h
  choose x hx y hy hequiv ε hε h using h
  set E : Set ℕ := {n | ¬ ε.Close (f (x n)) (f (y n)) }
  have hE : Infinite E := by
    rw [←not_finite_iff_infinite]
    by_contra! this
    replace : ε.EventuallyCloseSeqs (fun n ↦ f (x n):Sequence) (fun n ↦ f (y n):Sequence) := by
      sorry
    sorry
  observe : Countable E
  set n : ℕ → ℕ := Nat.nth E
  rw [Set.infinite_coe_iff] at hE
  have hmono : StrictMono n := by apply_rules [Nat.nth_strictMono]
  have hmem (j:ℕ) : n j ∈ E := j.nth_mem_of_infinite hE
  have hsep (j:ℕ) : |f (x (n j)) - f (y (n j))| > ε := by
    specialize hmem j
    simpa [E, Real.Close, Real.dist_eq] using hmem
  observe hxmem : ∀ j, x (n j) ∈ Set.Icc a b
  observe hymem : ∀ j, y (n j) ∈ Set.Icc a b
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ j, hj, ⟨ L, hL, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨ hclosed, hbounded ⟩ _ hxmem
  replace hcont := ContinuousOn.continuousWithinAt hcont hL
  have hconv' := hconv.comp_of_continuous hL hcont (fun k ↦ hxmem (j k))
  rw [Sequence.equiv_iff] at hequiv
  replace hequiv : atTop.Tendsto (fun k ↦ x (n (j k)) - y (n (j k))) (nhds 0) := by
    observe hj' : atTop.Tendsto j .atTop
    observe hn' : atTop.Tendsto n .atTop
    observe hcoe : atTop.Tendsto (fun n:ℕ ↦ (n:ℤ)) .atTop
    exact hequiv.comp (hcoe.comp (hn'.comp hj'))
  have hyconv : atTop.Tendsto (fun k ↦ y (n (j k))) (nhds L) := by
    convert hconv.sub hequiv with k
    . abel
    simp
  replace hyconv := hyconv.comp_of_continuous hL hcont (fun k ↦ hymem (j k))
  have : atTop.Tendsto (fun k ↦ f (x (n (j k))) - f (y (n (j k)))) (nhds 0) := by
    convert hconv'.sub hyconv; simp
  sorry


/-- Exercise 9.9.6 -/
theorem UniformContinuousOn.comp {X Y: Set ℝ} {f g:ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hg: UniformContinuousOn g Y)
  (hrange: f '' X ⊆ Y) : UniformContinuousOn (g ∘ f) X := by
  sorry

end Chapter9
