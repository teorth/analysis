import Mathlib.Tactic
import Analysis.Section_4_3

/-!
# Analysis I, Section 5.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

-/

namespace Chapter5

/-- Definition 5.1.1 (Sequence). To avoid some technicalities involving dependent types, we extend sequences by zero to the left of the starting point `n₀`. -/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n, n < n₀ → seq n = 0

/-- Sequence can be thought of as functions from ℤ to ℚ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/-- Functions from ℕ to ℚ can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℚ) Sequence where
  coe := fun a ↦ {
    n₀ := 0
    seq := fun n ↦ if n ≥ 0 then a n.toNat else 0
    vanish := by
      intro n hn
      simp [hn]
  }

abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq := fun n ↦ if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by
    intro n hn
    simp [hn]


lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) : (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by simp [seq, h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by simp [seq]

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (fun n ↦ n^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- need to temporarily leave the `Chapter5` namespace to introduce the following notation

end Chapter5

abbrev Rat.steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n m, ε.close (a n) (a m)

namespace Chapter5

lemma Rat.steady_def (ε: ℚ) (a: Sequence) :
  ε.steady a ↔ ∀ n m, ε.close (a n) (a m) := by rfl

lemma Rat.steady_def' (ε: ℚ) (a: Sequence) :
  ε.steady a ↔ ∀ n m, n ≥ a.n₀ ∧ m ≥ a.n₀ → ε.close (a n) (a m) := by
  rw [steady_def]
  constructor
  . intro h n m ⟨ hn, hm ⟩
    sorry
  intro h n m
  sorry

/-- Example 5.1.5 -/
example : (1:ℚ).steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by sorry

/-- Example 5.1.5 -/
example : ¬ (0.5:ℚ).steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by sorry

/-- Example 5.1.5 -/
example : (0.1:ℚ).steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by sorry

/-- Example 5.1.5 -/
example : ¬(0.01:ℚ).steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by sorry

/-- Example 5.1.5 -/
example (ε:ℚ) : ¬ ε.steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by sorry

/-- Example 5.1.5 -/
example (ε:ℚ) (hε: ε>0) : ε.steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by sorry

example : (10:ℚ).steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by sorry

example (ε:ℚ) (hε:ε<10):  ¬ ε.steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by sorry

/-- a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns the "junk" value of the original sequence `a` otherwise. -/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by
  simp [Sequence.from, seq, hn]
  intro h
  exact (a.vanish n h).symm

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.eventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop := ∃ N, (N ≥ a.n₀) ∧ ε.steady (a.from N)

namespace Chapter5

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Sequence) :
  ε.eventuallySteady a ↔ ∃ N, (N ≥ a.n₀) ∧ ε.steady (a.from N) := by rfl

/-- Example 5.1.7 -/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by sorry

lemma Sequence.ex_5_1_7_b : (0.1:ℚ).steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by sorry

lemma Sequence.ex_5_1_7_c : (0.1:ℚ).eventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by sorry

lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) : ε.eventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by sorry

abbrev Sequence.isCauchy (a:Sequence) : Prop := ∀ (ε:ℚ), (ε > 0 → (ε.eventuallySteady a))

lemma Sequence.isCauchy_def (a:Sequence) :
  a.isCauchy ↔ ∀ (ε:ℚ), (ε > 0 → ε.eventuallySteady a) := by rfl

lemma Sequence.isCauchy_of_coe (a:ℕ → ℚ) : (a:Sequence).isCauchy ↔ ∀ (ε:ℚ), ε > 0 → ∃ N, ∀ j k, j ≥ N ∧ k ≥ N → Section_4_3.dist (a j) (a k) ≤ ε := by sorry

lemma Sequence.isCauchy_of_mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) : (mk' n₀ a).isCauchy ↔ ∀ (ε:ℚ), ε > 0 → ∃ N, N ≥ n₀ ∧ ∀ j k, j ≥ N ∧ k ≥ N → Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by sorry

noncomputable def Sequence.sqrt_two : Sequence := (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

/-- Example 5.1.10.  (This requires extensive familiarity with Mathlib's API for the real numbers. )-/
theorem Sequence.ex_5_1_10_a : (1:ℚ).steady sqrt_two := by sorry

/-- Example 5.1.10.  (This requires extensive familiarity with Mathlib's API for the real numbers. )-/
theorem Sequence.ex_5_1_10_b : (0.1:ℚ).steady (sqrt_two.from 1) := by sorry

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).eventuallySteady sqrt_two := by sorry

/-- Proposition 5.1.11 -/
theorem Sequence.harmonic_steady : (mk' 1 (fun n ↦ (1:ℚ)/n)).isCauchy := by
  -- This is proof is probably longer than it needs to be; there should be a shorter proof that is still in the spirit of  the proof in the book.
  rw [isCauchy_of_mk (fun n ↦ (1:ℚ)/n)]
  intro ε hε
  have : ∃ N:ℕ, N > 1/ε := exists_nat_gt (1 / ε)
  obtain ⟨ N, hN ⟩ := this
  use N
  have hN' : (N:ℤ) > 0 := by
    have : (1/ε) > 0 := by positivity
    replace hN := this.trans hN
    simp at hN ⊢; assumption
  constructor
  . simp at hN' ⊢; linarith
  intro j k ⟨ hj, hk ⟩
  have hj' : (j:ℚ) ≥ 0 := by simp; linarith
  have hj'' : (1:ℚ)/j ≤ (1:ℚ)/N := by
    gcongr
    . simp at hN' ⊢; assumption
    . simp at hj ⊢; qify at hj; assumption
  have hj''' : (1:ℚ)/j ≥ 0 := by positivity
  have hj'''' : j ≥ 1 := by simp at hj'; linarith
  have hk' : (k:ℚ) ≥ 0 := by simp; linarith
  have hk'' : (1:ℚ)/k ≤ (1:ℚ)/N := by
    gcongr
    . simp at hN' ⊢; assumption
    . simp at hk ⊢; qify at hk; assumption
  have hk''' : (1:ℚ)/k ≥ 0 := by positivity
  have hk'''' : k ≥ 1 := by simp at hk'; linarith
  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    constructor <;> linarith
  simp [seq, hj'''', hk'''']
  convert hdist.trans _ using 2
  . simp
  . simp
  rw [div_le_iff₀, mul_comm, ←div_le_iff₀ hε]
  . exact le_of_lt hN
  simp at hN' ⊢; assumption

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : Prop :=
  ∀ i, |a i| ≤ M

/-- Definition 5.1.12 (bounded sequences).  Here we start sequences from 0 rather than 1 to align better with Mathlib conventions. -/
lemma BoundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) :
  BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.BoundedBy_def (a:Sequence) (M:ℚ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

abbrev Sequence.isBounded (a:Sequence) : Prop := ∃ M, M ≥ 0 ∧ a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.isBounded ↔ ∃ M, M ≥ 0 ∧ a.BoundedBy M := by rfl

/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by sorry

/-- Example 5.1.13 -/
example : ¬ ((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).isBounded := by sorry

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).isBounded := by sorry

/-- Example 5.1.13 -/
example : ¬ ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).isCauchy := by sorry

/-- Lemma 5.1.14 -/
lemma bounded_of_finite {n:ℕ} (a: Fin n → ℚ) : ∃ M, M ≥ 0 ∧  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0
    simp [BoundedBy_def]
  set a' : Fin n → ℚ := fun m ↦ a m
  obtain ⟨ M, hpos, hM ⟩ := hn a'
  have h1 : BoundedBy a' (M + |a n|) := by
    intro m
    apply (hM m).trans
    simp
  have h2 : |a n| ≤ M + |a n| := by simp [hpos]
  use M + |a n|
  constructor
  . positivity
  intro m
  rcases Fin.eq_castSucc_or_eq_last m with hm | hm
  . obtain ⟨ j, hj ⟩ := hm
    convert h1 j
    simp [hj]
  convert h2
  simp [hm]

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.isCauchy) : a.isBounded := by
  sorry

end Chapter5
