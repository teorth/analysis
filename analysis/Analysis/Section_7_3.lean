import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Analysis.Section_6_1
import Analysis.Section_6_epilogue
import Analysis.Section_7_2

/-!
# Analysis I, Section 7.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Equivalent characterizations of convergence of nonnegative series
- Cauchy condensation test

-/

namespace Chapter7

abbrev Series.nonneg (s : Series) : Prop := ∀ n, s.seq n ≥ 0

abbrev Series.partial_of_nonneg {s : Series} (h : s.nonneg) : Monotone s.partial := by sorry

/-- Proposition 7.3.1 -/
theorem Series.converges_of_nonneg_iff {s : Series} (h : s.nonneg) : s.converges ↔ ∃ M, ∀ N, s.partial N ≤ M := by
  -- This broadly follows the argument in the text, though for one direction I choose to use Mathlib routines rather than Chapter6 results.
  constructor
  . intro hconv
    set S : Chapter6.Sequence := ⟨ s.m, s.partial, by intro n hn; simp [Series.partial, hn] ⟩
    have : S.IsBounded := by
      apply S.bounded_of_convergent
      rw [Chapter6.Sequence.converges_iff_Tendsto']
      convert hconv
    obtain ⟨ M, hpos, hM ⟩ := this
    use M; intro N; specialize hM N
    exact (le_abs_self _).trans hM
  intro hbound
  rcases tendsto_of_monotone (partial_of_nonneg h) with hinfin | hfin
  . obtain ⟨ M, hM ⟩ := hbound
    obtain ⟨ N, hN ⟩ := Filter.Eventually.exists (Filter.Tendsto.eventually_gt_atTop  hinfin M)
    specialize hM N
    linarith
  exact hfin

theorem Series.sum_of_nonneg_lt {s : Series} (h : s.nonneg) {M:ℝ} (hM: ∀ N, s.partial N ≤ M) : s.sum ≤ M := by
  have : ∃ M, ∀ N, s.partial N ≤ M  := by use M
  rw [←converges_of_nonneg_iff h] at this
  simp [sum, this]
  have hconv := this.choose_spec
  set L := this.choose
  simp [convergesTo] at hconv
  exact le_of_tendsto' hconv hM

theorem Series.partial_le_sum_of_nonneg {s : Series} (hnon : s.nonneg) (hconv : s.converges) (N : ℤ) :
  s.partial N ≤ s.sum := by
  apply Monotone.ge_of_tendsto (partial_of_nonneg hnon)
  simp [sum, hconv]
  convert hconv.choose_spec

/-- Some useful nonnegativity lemmas for later applications. -/
theorem Series.partial_nonneg {s : Series} (hnon : s.nonneg) (N : ℤ) : 0 ≤ s.partial N := by
  simp [Series.partial]
  apply Finset.sum_nonneg
  intro n _; exact hnon _

theorem Series.sum_of_nonneg {s:Series} (hnon : s.nonneg) : 0 ≤ s.sum := by
  by_cases h: s.converges <;> simp [Series.sum, h]
  have := h.choose_spec
  set L := h.choose
  apply ge_of_tendsto' this (partial_nonneg hnon)

/-- Corollary 7.3.2 (Comparison test) / Exercise 7.3.1 -/
theorem Series.converges_of_le {s t : Series} (hm : s.m = t.m) (hcomp : ∀ n ≥ s.m, |s.seq n| ≤ t.seq n) (hconv : t.converges) : s.absConverges ∧ |s.sum| ≤ s.abs.sum ∧ s.abs.sum ≤ t.sum := by sorry

theorem Series.diverges_of_ge {s t : Series} (hm : s.m = t.m) (hcomp : ∀ n ≥ s.m, |s.seq n| ≤ t.seq n) (hdiv: ¬ s.absConverges) : t.diverges := by sorry

/-- Lemma 7.3.3 (Geometric series) / Exercise 7.3.2 -/
theorem Series.converges_geom {x : ℝ} (hx : |x| < 1) : (fun n ↦ x ^ n : Series).convergesTo (1 / (1 - x)) := by sorry

theorem Series.absConverges_geom {x : ℝ} (hx : |x| < 1) : (fun n ↦ x ^ n : Series).absConverges := by sorry

theorem Series.diverges_geom {x : ℝ} (hx : |x| ≥ 1) : (fun n ↦ x ^ n : Series).diverges := by sorry

theorem Series.converges_geom_iff (x : ℝ) : (fun n ↦ x ^ n : Series).converges ↔ |x| < 1 := by sorry

/-- Proposition 7.3.4 (Cauchy criterion) -/
theorem Series.cauchy_criterion {s:Series} (hm: s.m = 1) (hs:s.nonneg) (hmono: ∀ n ≥ 1, s.seq (n+1) ≤ s.seq n) : s.converges ↔ (fun k ↦ 2^k * s.seq (2^k): Series).converges := by
  -- This proof is written to follow the structure of the original text.
  set t := (fun k ↦ 2^k * s.seq (2^k):Series)
  have ht: t.nonneg := by
    intro n
    by_cases h: n ≥ 0
    all_goals simp [t,h]
    exact hs _
  have hmono' : ∀ n ≥ 1, ∀ m ≥ n, s.seq m ≤ s.seq n := by
    intro n hn m hm
    obtain ⟨ k, rfl ⟩ := Int.le.dest hm
    clear hm
    induction' k with k hk
    . simp
    convert (hmono (n+k) (by linarith)).trans hk using 2
    simp; abel
  have htm : t.m = 0 := by simp [t]
  rw [converges_of_nonneg_iff hs, converges_of_nonneg_iff ht]
  set S := s.partial
  set T := t.partial
  have Lemma_7_3_6 (K:ℕ) : S (2^(K+1) - 1) ≤ T K ∧ T K ≤ 2 * S (2^K) := by
    induction' K with K hK
    . simp [S,T,Series.partial, hm, htm, t]
      linarith [hs 1]
    have h2K : 1 ≤ 2^K := Nat.one_le_two_pow
    have h2K' : 1 ≤ 2^(K+1) := Nat.one_le_two_pow
    obtain ⟨ hK1, hK2 ⟩ := hK
    have claim1 : T (K + 1) = T K + 2^(K+1) * s.seq (2^(K+1)) := by
      convert t.partial_succ ?_
      linarith
    have claim2a : S (2^(K+1)) ≥ S (2^K) + 2^K * s.seq (2^(K+1)) := calc
      _ = S (2^K) + ∑ n ∈ Finset.Ioc (2^K) (2^(K+1)), s.seq n := by
        have : Disjoint (Finset.Icc s.m (2^K)) (Finset.Ioc (2^K) (2^(K+1))) := by
          rw [Finset.disjoint_iff_ne]
          intro x hx y hy
          simp at hx hy; linarith
        convert Finset.sum_union this
        ext x; simp
        constructor
        . intro ⟨h1, h2⟩
          simp [h1, h2, le_or_lt]
        intro h
        rcases h with ⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩
        . simp [h1,pow_succ']; linarith
        simp [h2, hm]; linarith
      _ ≥ S (2^K) + ∑ n ∈ Finset.Ioc ((2:ℤ)^K) (2^(K+1)), s.seq (2^(K+1)) := by
        gcongr with n hn
        simp at hn
        exact hmono' _ (by linarith) _ hn.2
      _ = _ := by
        simp [pow_succ']; left
        ring_nf
        norm_cast
    have claim2 : 2 * S (2^(K+1)) ≥ 2 * S (2^K) + 2^(K+1) * s.seq (2^(K+1)) := by nth_rewrite 2 [pow_succ']; linarith
    have claim3 : S (2^(K+1+1) - 1) ≤ S (2^(K+1)-1) + 2^(K+1) * s.seq (2^(K+1)) := calc
      _ = S (2^(K+1)-1) + ∑ n ∈ Finset.Icc (2^(K+1)) (2^(K+1+1)-1), s.seq n := by
        have : Disjoint (Finset.Icc s.m (2^(K+1)-1)) (Finset.Icc (2^(K+1)) (2^(K+1+1)-1)) := by
          rw [Finset.disjoint_iff_ne]
          intro x hx y hy
          simp at hx hy; linarith
        convert Finset.sum_union this
        ext x; simp
        constructor
        . intro ⟨h1, h2⟩
          simp [h1, h2]; omega
        intro h
        rcases h with ⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩
        . simp [h1, pow_succ' _ (K+1)]; linarith
        simp [h2, hm]; linarith
      _ ≤ S (2^(K+1)-1) + ∑ n ∈ Finset.Icc ((2:ℤ)^(K+1)) (2^(K+1+1)-1), s.seq (2^(K+1)) := by
        gcongr with n hn
        simp at hn
        exact hmono' _ (by linarith) _ hn.1
      _ = _ := by
        simp [pow_succ']; left
        ring_nf
        norm_cast
    simp
    constructor <;> linarith
  constructor
  . intro h
    obtain ⟨ M, hM ⟩ := h
    use 2*M
    intro N; rcases lt_or_ge N 0 with hN | hN
    . simp [T, Series.partial, htm, hN]
      convert hM 0
      simp [S, Series.partial, hm]
    rw [Int.eq_natCast_toNat.mpr hN]
    apply (Lemma_7_3_6 N.toNat).2.trans
    gcongr
    exact hM _
  intro h
  obtain ⟨ M, hM ⟩ := h
  use M
  intro K'
  rcases lt_or_ge K' 1 with hK' | hK'
  . simp [S, Series.partial, hm, hK']
    convert hM (-1)
  set K := (K'-1).toNat
  have hK : K' = K + 1 := by
    rw [Int.toNat_of_nonneg (by linarith)]
    abel
  calc
    _ ≤ S (2 ^ (K+1) - 1) := by
      apply partial_of_nonneg hs
      rw [hK]
      generalize K = n
      induction' n with n hn
      . simp
      simp [pow_succ] at hn ⊢
      linarith
    _ ≤ T K := (Lemma_7_3_6 K).1
    _ ≤ M := hM K

/-- Corollary 7.3.7 -/
theorem Series.converges_qseries (q : ℝ) (hq : q > 0) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series).converges ↔ (q>1) := by
  -- This proof is written to follow the structure of the original text.
  set s := (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series)
  have hs : s.nonneg := by intro n; simp [s]; by_cases h : 1 ≤ n <;> simp [h]; positivity
  have hmono : ∀ n ≥ 1, s.seq (n+1) ≤ s.seq n := by
    intro n hn
    have hn1 : n ≥ 0 := by positivity
    have hn3 : n.toNat > 0 := by omega
    simp [s, hn, hn1]
    apply inv_anti₀ (by positivity)
    exact Real.rpow_le_rpow (by positivity) (by simp) (by positivity)
  rw [cauchy_criterion (by simp [s]) hs hmono]
  have (n:ℕ) : 2^n * s.seq (2^n) = (2^(1-q))^n := by
    have : 1 ≤ (2:ℤ)^n := by norm_cast; exact Nat.one_le_two_pow
    simp [s, this]
    rw [←Real.rpow_neg (by positivity), mul_comm, ←Real.rpow_add_one (by positivity), Real.rpow_pow_comm (by norm_num)]
    congr 1; abel
  simp [this, converges_geom_iff]
  rw [abs_of_nonneg (by positivity), Real.rpow_lt_one_iff_of_pos (by positivity)]
  simp

/-- Remark 7.3.8 -/
theorem Series.zeta_eq {q:ℝ} (hq: q > 1) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series).sum = riemannZeta q := by
  -- `riemannZeta` is defined over the complex numbers, so some preliminary work is needed to specialize to the reals.
  set L := ∑' n:ℕ, 1 / (n+1:ℝ)^q
  have hL : L = riemannZeta q := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_cast)]
    unfold L
    convert Complex.ofReal_tsum _ with n
    simp [Complex.ofReal_cpow (x := n+1) (by positivity) _]
  rw [←hL]
  norm_cast
  apply sum_of_converges
  have : Summable (fun (n : ℕ)↦ 1 / (n+1:ℝ) ^ q) := by
    convert (Real.summable_one_div_nat_add_rpow 1 q).mpr hq using 4 with n
    rw [abs_of_nonneg (by positivity)]
  have tail (a: ℤ → ℝ) (L:ℝ) : Filter.Tendsto a Filter.atTop (nhds L) ↔ Filter.Tendsto (fun n:ℕ ↦ a n) Filter.atTop (nhds L) := by
    convert Filter.tendsto_map'_iff (g:= fun n:ℕ ↦ (n:ℤ) )
    simp
  unfold convergesTo
  rw [tail _ L]
  convert Summable.tendsto_sum_tsum_nat this with n
  simp [Series.partial]
  set e : ℕ ↪ ℤ := {
    toFun n := n+1
    inj' := by intro a b h; simp at h; exact h
  }
  convert Finset.sum_map _ e _ using 2 with n _ m hm
  . ext x
    simp [e]
    constructor
    . intro ⟨ h1, h2 ⟩
      use (x-1).toNat; omega
    intro ⟨ a, han, hax ⟩; omega
  simp [e]

theorem Series.Basel_problem :  (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ 2 : Series).sum = Real.pi ^ 2 / 6 := by
  have := zeta_eq (show 2 > 1 by norm_num)
  simp [Complex.ofReal_ofNat, riemannZeta_two] at this
  simpa [←Complex.ofReal_inj]


/-- Exercise 7.3.3 -/
theorem Series.nonneg_sum_zero {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges) : (a:Series).sum = 0 ↔ ∀ n, a n = 0 := by sorry


end Chapter7
