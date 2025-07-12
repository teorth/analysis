import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, Section 6.6

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence
-/

namespace Chapter6

/-- Definition 6.6.1 -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by sorry

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := by sorry

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (1:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (1:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a := by sorry

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by sorry

/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
  sorry

/-- Proposition 6.6.6 / Exercise 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
  sorry

/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this
  obtain ⟨ b, hsubseq, htends ⟩ := this
  refine ⟨ b, hsubseq, ⟨ L_plus, htends ⟩ ⟩

/- Exercise 6.6.2 -/

def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
    sorry

/--
  Exercise 6.6.3.  You may find the API around Mathlib's `Nat.find` to be useful
  (and `open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  sorry


end Chapter6
