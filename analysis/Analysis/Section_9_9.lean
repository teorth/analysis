import Mathlib.Tactic
import Analysis.Section_6_1
import Mathlib.Data.Nat.Nth
import Analysis.Section_9_6

/-!
# Analysis I, Section 9.9

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

-/

open Chapter6

namespace Chapter9

/-!
Main constructions and results of this section:
- API for Mathlib's `UniformContinuousOn`
- Continuous functions on compact intervls are uniformly continuous

-/

example : ContinuousOn (fun x:ℝ ↦ 1/x) (Set.Icc 0 2) := by
  sorry

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (Set.Icc 0 2) := by
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
  -- note: there is currently a bug with `extract_lets` in that `let` statements with identically
  -- assigned values are not being handled correctly.
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

/-- Definition 9.9.2.  Here we use the Mathlib term `UniformContinuousOn` -/
theorem UniformContinuousOn.iff (f: ℝ → ℝ) (X:Set ℝ) : UniformContinuousOn f X  ↔
  ∀ ε > (0:ℝ), ∃ δ > (0:ℝ), ∀ x₀ ∈ X, ∀ x ∈ X, δ.Close x x₀ → ε.Close (f x) (f x₀) := by
  simp_rw [Metric.uniformContinuousOn_iff_le, Real.Close]
  apply forall_congr'; intro ε
  apply imp_congr_right; intro hε
  apply exists_congr; intro δ
  apply and_congr_right; intro hδ
  constructor
  . exact fun h x₀ hx₀ x hx ↦ h x hx x₀ hx₀
  exact fun h x hx y hy ↦ h y hy x hx

theorem ContinuousOn.ofUniformContinuousOn {X:Set ℝ} (f: ℝ → ℝ) (hf: UniformContinuousOn f X) :
  ContinuousOn f X := by
  sorry

example : ¬ UniformContinuousOn (fun x:ℝ ↦ 1/x) (Set.Icc 0 2) := by
  sorry

end Chapter9

/-- Definition 9.9.5.  This is similar but not identical to `Real.close_seq` from Section 6.1. -/
abbrev Real.close_seqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  (a.m = b.m) ∧ ∀ n ≥ a.m, ε.Close (a n) (b n)

abbrev Real.eventually_close_seqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.close_seqs (a.from N) (b.from N)

abbrev Chapter6.Sequence.equiv (a b: Sequence) : Prop :=
  ∀ ε > (0:ℝ), ε.eventually_close_seqs a b

/-- Remark 9.9.6 -/
theorem Chapter6.Sequence.equiv_iff_rat (a b: Sequence) :
  Sequence.equiv a b ↔ ∀ ε > (0:ℚ), (ε:ℝ).eventually_close_seqs a b := by
  sorry

/-- Lemma 9.9.7 / Exercise 9.9.1 -/
theorem Chapter6.Sequence.equiv_iff (a b: Sequence) :
  Sequence.equiv a b ↔ Filter.Tendsto (fun n ↦ a n - b n) Filter.atTop (nhds 0) := by
  sorry


namespace Chapter9


/-- Proposition 9.9.8 / Exercise 9.9.2 -/
theorem UniformContinuousOn.iff_preserves_equiv {X:Set ℝ} (f: ℝ → ℝ) :
  UniformContinuousOn f X ↔
  ∀ x y: ℕ → ℝ, (∀ n, x n ∈ X) → (∀ n, y n ∈ X) →
  Sequence.equiv (x:Sequence) (y:Sequence) →
  Sequence.equiv (f ∘ x:Sequence) (f ∘ y:Sequence) := by
  sorry

/-- Remark 9.9.9 -/
theorem Chapter6.Sequence.equiv_const (x₀: ℝ) (x:ℕ → ℝ) : Filter.Tendsto x Filter.atTop (nhds x₀) ↔
  Sequence.equiv (x:Sequence) (fun n:ℕ ↦ x₀:Sequence) := by
  sorry

/-- Example 9.9.10 -/
noncomputable abbrev f_9_9_10 : ℝ → ℝ := fun x ↦ 1/x

example : Sequence.equiv (fun n:ℕ ↦ 1/(n+1:ℝ):Sequence) (fun n:ℕ ↦ 1/(2*(n+1):ℝ):Sequence) := by sorry

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by sorry

example (n:ℕ) : 1/(2*(n+1):ℝ) ∈ Set.Ioo 0 2 := by sorry

example : ¬ Sequence.equiv (fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ)):Sequence) (fun n:ℕ ↦ f_9_9_10 (1/(2*(n+1):ℝ)):Sequence) := by sorry

example : ¬ UniformContinuousOn f_9_9_10 (Set.Ioo 0 2) := by
  sorry

/-- Example 9.9.11 -/
abbrev f_9_9_11 : ℝ → ℝ := fun x ↦ x^2

example : Sequence.equiv ((fun n:ℕ ↦ (n+1:ℝ)):Sequence) ((fun n:ℕ ↦ (n+1)+1/(n+1:ℝ)):Sequence) := by
  sorry

example : ¬ Sequence.equiv ((fun n:ℕ ↦ f_9_9_11 (n+1:ℝ)):Sequence) ((fun n:ℕ ↦ f_9_9_11 ((n+1)+1/(n+1:ℝ))):Sequence) := by
  sorry

example : ¬ UniformContinuousOn f_9_9_11 Set.univ := by
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
  ∃ L:ℝ, Filter.Tendsto f (nhds x₀ ⊓ Filter.principal X) (nhds L) := by
  sorry

/-- Proposition 9.9.15 / Exercise 9.9.5 -/
theorem UniformContinuousOn.of_bounded {E X:Set ℝ} {f: ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hEX: E ⊆ X) (hE: Bornology.IsBounded E) :
  Bornology.IsBounded (f '' E) := by
  sorry

/-- Theorem 9.9.16 -/
theorem UniformContinuousOn.of_continuousOn {a b:ℝ} {f:ℝ → ℝ}
  (hcont: ContinuousOn f (Set.Icc a b)) :
  UniformContinuousOn f (Set.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  rw [iff_preserves_equiv] at h
  simp only [ge_iff_le, Function.comp_apply, not_forall, Classical.not_imp, gt_iff_lt, not_exists,
  not_and, sup_le_iff, dite_eq_ite, and_imp, not_le, forall_const, exists_and_left] at h
  obtain ⟨ x, y, hx, hy, hequiv, ε, hε, h ⟩ := h
  set E : Set ℕ := {n | ¬ ε.Close (f (x n)) (f (y n)) }
  have hE : Infinite E := by
    rw [←not_finite_iff_infinite]
    by_contra! this
    replace : ε.eventually_close_seqs (fun n ↦ f (x n):Sequence) (fun n ↦ f (y n):Sequence) := by
      sorry
    sorry
  have : Countable E := by infer_instance
  set n : ℕ → ℕ := Nat.nth E
  rw [Set.infinite_coe_iff] at hE
  have hmono : StrictMono n := by
    apply Nat.nth_strictMono
    convert hE
  have hmem (j:ℕ) : n j ∈ E := Nat.nth_mem_of_infinite hE j
  have hsep (j:ℕ) : |f (x (n j)) - f (y (n j))| > ε := by
    specialize hmem j
    simp [E, Real.Close, Real.dist_eq] at hmem
    exact hmem
  have hxmem (j:ℕ) : x (n j) ∈ Set.Icc a b := hx (n j)
  have hymem (j:ℕ) : y (n j) ∈ Set.Icc a b := hy (n j)
  have hclosed : IsClosed (Set.Icc a b) := Icc_closed
  have hbounded : Bornology.IsBounded (Set.Icc a b) := Icc_bounded _ _
  obtain ⟨ j, hj, ⟨ L, hL, hconv⟩ ⟩ := (Heine_Borel (Set.Icc a b)).mp ⟨ hclosed, hbounded ⟩ _ hxmem
  replace hcont := ContinuousOn.continuousWithinAt hcont hL
  have hconv' := Filter.Tendsto.comp_of_continuous hL hcont (fun k ↦ hxmem (j k)) hconv
  rw [Sequence.equiv_iff] at hequiv
  replace hequiv : Filter.Tendsto (fun k ↦ x (n (j k)) - y (n (j k))) Filter.atTop (nhds 0) := by
    have hj' : Filter.Tendsto j Filter.atTop Filter.atTop := StrictMono.tendsto_atTop hj
    have hn' : Filter.Tendsto n Filter.atTop Filter.atTop := StrictMono.tendsto_atTop hmono
    have hcoe : Filter.Tendsto (fun n:ℕ ↦ (n:ℤ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    convert hequiv.comp (hcoe.comp (hn'.comp hj'))
  have hyconv : Filter.Tendsto (fun k ↦ y (n (j k))) Filter.atTop (nhds L) := by
    convert Filter.Tendsto.sub hconv hequiv with k
    . abel
    simp
  replace hyconv := Filter.Tendsto.comp_of_continuous hL hcont (fun k ↦ hymem (j k)) hyconv
  have : Filter.Tendsto (fun k ↦ f (x (n (j k))) - f (y (n (j k)))) Filter.atTop (nhds 0) := by
    convert Filter.Tendsto.sub hconv' hyconv
    simp
  sorry


/-- Exercise 9.9.6 -/
theorem UniformContinuousOn.comp {X Y: Set ℝ} {f g:ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hg: UniformContinuousOn g Y)
  (hrange: f '' X ⊆ Y) : UniformContinuousOn (g ∘ f) X := by
  sorry

end Chapter9
