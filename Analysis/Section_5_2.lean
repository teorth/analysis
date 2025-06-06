import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals
- Notion of an equivalent Cauchy sequence of rationals

-/


abbrev Rat.close_seq (ε: ℚ) (a b: Chapter5.Sequence) : Prop := ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.close (a n) (b n)

abbrev Rat.eventually_close (ε: ℚ) (a b: Chapter5.Sequence) : Prop := ∃ N, ε.close_seq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.close_seq_def (ε: ℚ) (a b: Sequence) : ε.close_seq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).close_seq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by sorry

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
:= by sorry

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence)
:= by sorry

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventually_close_def (ε: ℚ) (a b: Sequence) : ε.eventually_close a b ↔  ∃ N, ε.close_seq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventually_close_iff (ε: ℚ) (a b: ℕ → ℚ) : ε.eventually_close (a:Sequence) (b:Sequence) ↔  ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by sorry

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).close_seq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence) ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by sorry

example : (0.1:ℚ).eventually_close ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence) ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by sorry

example : (0.01:ℚ).eventually_close ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence) ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by sorry

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.eventually_close (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) : equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.eventually_close (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by sorry

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be possible that is still faithful to the original text.
  equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε εpos
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := by rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := by apply abs_of_nonneg; positivity

  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn
    rw [hab n]
    gcongr
    norm_num

  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        rw [mul_assoc, ←Section_4_3.pow_eq_zpow, ←zpow_add₀ (by norm_num)]
        simp
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num) (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1
        . simp
        . simp
        all_goals infer_instance
    have : ∃ N:ℕ, N > 2/ε := exists_nat_gt (2 / ε)
    obtain ⟨ N, hN ⟩ := this
    use N
    apply (hN' N).trans
    rw [div_le_iff₀ (by positivity)]
    replace hN := (div_lt_iff₀ εpos).mp hN
    apply le_of_lt (hN.trans _)
    rw [mul_comm]
    gcongr; linarith
  obtain ⟨ N, hN ⟩ := hN
  use N
  intro n hn
  exact (hab' N n hn).trans hN


/-- Exercise 5.2.1 -/
theorem Sequence.equiv_of_cauchy {a b: ℕ → ℚ} (hab: Sequence.equiv a b) : (a:Sequence).isCauchy ↔ (b:Sequence).isCauchy := by sorry

/-- Exercise 5.2.2 -/
theorem Sequence.close_of_bounded {ε:ℚ} (hε: ε>0) {a b: ℕ → ℚ} (hab: ε.eventually_close a b) : (a:Sequence).isBounded ↔ (b:Sequence).isBounded := by sorry

end Chapter5
