import Mathlib.Tactic
import Analysis.Section_6_4

/-!
# Analysis I, Section 6.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some standard limits, including limits of sequences of the form 1/n^α, x^n, and x^(1/n).

-/

namespace Chapter6

theorem Sequence.lim_of_const (c:ℝ) :  ((fun (n:ℕ) ↦ c):Sequence).TendsTo c := by sorry

instance Sequence.inst_pow: Pow Sequence ℕ where
  pow a k := {
    m := a.m
    seq := fun (n:ℤ) ↦ if n ≥ a.m then a n ^ k else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }

@[simp]
lemma Sequence.pow_one (a:Sequence) : a^1 = a := by
  ext n
  . rfl
  simp only [HPow.hPow, Pow.pow]
  by_cases h: n ≥ a.m
  . simp [h]
  simp [h, a.vanish n (by linarith)]

lemma Sequence.pow_succ (a:Sequence) (k:ℕ) : a^(k+1) = a^k * a := by
  ext n
  . simp only [HPow.hPow, Pow.pow, HMul.hMul, Mul.mul]
    simp
  simp only [HPow.hPow, Pow.pow, HMul.hMul, Mul.mul]
  by_cases h: n ≥ a.m
  . simp [h]; rfl
  simp [h, a.vanish n (by linarith)]

/-- Corollary 6.5.1 -/
theorem Sequence.lim_of_power_decay {k:ℕ} :
    ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence).TendsTo 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence)
  have ha : a.BddBelow := by
    use 0
    intro n hn
    simp [a]
    positivity
  have ha' : a.IsAntitone := by
    intro n hn
    simp [a] at hn ⊢
    have hn' : 0 ≤ n+1 := by linarith
    simp [hn,hn']
    rw [inv_le_inv₀ (by positivity) (by positivity),
        Real.rpow_le_rpow_iff  (by positivity) (by positivity) (by positivity)]
    simp [hn]
  replace ha' := convergent_of_antitone ha ha'
  have hpow (n:ℕ): (a^(n+1)).Convergent ∧ lim (a^(n+1)) = (lim a)^(n+1) := by
    induction' n with n ih
    . simp only [zero_add, pow_one, _root_.pow_one, ha', true_and]
    rw [pow_succ]
    convert lim_mul ih.1 ha'
    rw [ih.2]
    rfl
  have hlim : (lim a)^(k+1) = 0 := by
    rw [←(hpow k).2]
    convert lim_harmonic.2
    ext n; rfl
    simp only [HPow.hPow, Pow.pow, a]
    by_cases h : n ≥ 0
    all_goals simp [h]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    convert Real.rpow_one _
    field_simp
  simp only [lim_eq, ha', true_and, pow_eq_zero hlim]

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric {x:ℝ} (hx: |x| < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 0 := by
  sorry

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric' {x:ℝ} (hx: x = 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 1 := by
  sorry

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric'' {x:ℝ} (hx: x = -1 ∨ |x| > 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Divergent := by
  sorry

/-- Lemma 6.5.3 / Exercise 6.5.3 -/
theorem Sequence.lim_of_roots {x:ℝ} (hx: x > 0) :
    ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence).TendsTo 1 := by
  sorry

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_decay {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ 1/((n+1:ℝ)^(q:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_growth {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ ((n+1:ℝ)^(q:ℝ)):Sequence).Divergent := by
  sorry



end Chapter6
