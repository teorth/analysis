import Mathlib.Tactic
import Analysis.Section_6_7

/-!
# Analysis I, Chapter 6 epilogue: Connections with Mathlib limits

In this (technical) epilogue, we show that various operations and properties we have defined for
"Chapter 6" sequences `Chapter6.Sequence` are equivalent to Mathlib operations.  Note however
that Mathlib's operations are defined in far greater generality than the setting of real-valued
sequences, in particular using the language of filters.

-/

open Filter

/-- Identification with the Cauchy sequence support in Mathlib/Algebra/Order/CauSeq/Basic -/
theorem Chapter6.Sequence.isCauchy_iff_isCauSeq (a: ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ IsCauSeq _root_.abs a := by
  simp_rw [IsCauchy.coe, Real.dist_eq, IsCauSeq]
  constructor <;> intro h ε hε <;> have ⟨ N, h ⟩ := h _ (half_pos hε) <;> use N
  . intro n hn; linarith [h n hn N (by rfl)]
  intro n hn m hm
  calc
    _ ≤ |a n - a N| + |a m - a N| := by grind [abs_sub_comm, abs_sub_le]
    _ ≤ ε/2 + ε/2 := by grind
    _ = _ := by linarith

/-- Identification with the Cauchy sequence support in Mathlib/Topology/UniformSpace/Cauchy -/
theorem Chapter6.Sequence.Cauchy_iff_CauchySeq (a: ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ CauchySeq a := by
  rw [isCauchy_iff_isCauSeq]
  convert isCauSeq_iff_cauchySeq

/-- Identification with `Filter.Tendsto` -/
theorem Chapter6.Sequence.tendsto_iff_Tendsto (a: ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ atTop.Tendsto a (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor <;> intro h ε hε
  . have ⟨ N, hN ⟩ := h _ (half_pos hε); use N.toNat; intro n hn
    specialize hN n (Int.toNat_le.mp hn); simp at hN
    rw [Real.dist_eq]; linarith
  have ⟨ N, hN ⟩ := h ε hε; use N; intro n hn
  have hpos : n ≥ 0 := by grind
  rw [ge_iff_le, ←Int.le_toNat hpos] at hn
  simp [hpos, ←Real.dist_eq, le_of_lt (hN n.toNat hn)]

theorem Chapter6.Sequence.tendsto_iff_Tendsto' (a: Sequence) (L:ℝ) : a.TendsTo L ↔ atTop.Tendsto a.seq (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor <;> intro h ε hε
  . have ⟨ N, hN ⟩ := h _ (half_pos hε); use N; peel 2 hN; rw [Real.dist_eq]; linarith
  have ⟨ N, hN ⟩ := h _ hε; use N; peel 2 hN; rw [←Real.dist_eq]; linarith

theorem Chapter6.Sequence.converges_iff_Tendsto (a: ℕ → ℝ) :
    (a:Sequence).Convergent ↔ ∃ L, atTop.Tendsto a (nhds L) := by simp_rw [←tendsto_iff_Tendsto]

theorem Chapter6.Sequence.converges_iff_Tendsto' (a: Sequence) :
    a.Convergent ↔ ∃ L, atTop.Tendsto a.seq (nhds L) := by simp_rw [←tendsto_iff_Tendsto']

/-- A technicality: `CauSeq.IsComplete ℝ` was established for `_root_.abs` but not for `norm`. -/
instance inst_real_complete : CauSeq.IsComplete ℝ norm := by convert Real.instIsCompleteAbs

/-- Identification with `CauSeq.lim` -/
theorem Chapter6.Sequence.lim_eq_CauSeq_lim (a:ℕ → ℝ) (ha: (a:Sequence).IsCauchy) :
    Chapter6.lim (a:Sequence) = CauSeq.lim  ⟨ a, (isCauchy_iff_isCauSeq a).mp ha⟩ := by
  have h1 := CauSeq.tendsto_limit ⟨ a, (isCauchy_iff_isCauSeq a).mp ha⟩
  have h2 := lim_def ((a:Sequence).Cauchy_iff_convergent.mp ha)
  rw [←tendsto_iff_Tendsto] at h1
  by_contra! h; apply (a:Sequence).tendsTo_unique at h; tauto

/-- Identification with `limUnder` -/
theorem Chapter6.Sequence.lim_eq_limUnder (a:ℕ → ℝ) (ha: (a:Sequence).Convergent) :
    Chapter6.lim (a:Sequence) = limUnder Filter.atTop a := by
    sorry

/-- Identification with `Bornology.IsBounded` -/
theorem Chapter6.Sequence.isBounded_iff_isBounded_range (a:ℕ → ℝ):
    (a:Sequence).IsBounded ↔ Bornology.IsBounded (Set.range a) := by
  simp [isBounded_def, boundedBy_def, Metric.isBounded_iff]
  constructor
  . intro ⟨ M, hM, h ⟩; use 2*M; intro n m
    calc
      _ = |a n - a m| := Real.dist_eq _ _
      _ ≤ |a n| + |a m| := abs_sub _ _
      _ ≤ M + M := by gcongr; convert h n; convert h m
      _ = _ := by ring
  intro ⟨ C, h ⟩
  have : C ≥ 0 := by specialize h 0 0; simpa using h
  refine ⟨ C + |a 0|, by positivity, ?_ ⟩
  intro n; by_cases hn: n ≥ 0 <;> simp [hn]
  . calc
      _ ≤ |a n.toNat - a 0| + |a 0| := by convert abs_add_le _ _; abel; infer_instance
      _ ≤ C + |a 0| := by gcongr; rw [←Real.dist_eq]; convert h n.toNat 0
  positivity

theorem Chapter6.Sequence.sup_eq_sSup (a:ℕ → ℝ):
    (a:Sequence).sup = sSup (Set.range (fun n ↦ (a n:EReal))) := by sorry

theorem Chapter6.Sequence.inf_eq_sInf (a:ℕ → ℝ):
    (a:Sequence).inf = sInf (Set.range (fun n ↦ (a n:EReal))) := by sorry

theorem Chapter6.Sequence.bddAbove_iff (a:ℕ → ℝ):
    (a:Sequence).BddAbove ↔ _root_.BddAbove (Set.range a) := by sorry

theorem Chapter6.Sequence.bddBelow_iff (a:ℕ → ℝ):
    (a:Sequence).BddBelow ↔ _root_.BddBelow (Set.range a) := by sorry

theorem Chapter6.Sequence.Monotone_iff (a:ℕ → ℝ): (a:Sequence).IsMonotone ↔ Monotone a := by sorry

theorem Chapter6.Sequence.Antitone_iff (a:ℕ → ℝ): (a:Sequence).IsAntitone ↔ Antitone a := by sorry

/-- Identification with `MapClusterPt` -/
theorem Chapter6.Sequence.limit_point_iff (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ MapClusterPt L .atTop a := by
  simp_rw [limit_point_def, mapClusterPt_iff_frequently, frequently_atTop, Metric.mem_nhds_iff]
  constructor
  . intro h s ⟨ ε, hε, hεs ⟩ N
    have ⟨ n, hn1, hn2 ⟩ := h _ (half_pos hε) N (by positivity)
    have hn : n ≥ 0 := by grind
    refine ⟨ n.toNat, by rwa [ge_iff_le, Int.le_toNat hn], ?_ ⟩
    apply hεs; simp [Real.dist_eq, hn] at *; linarith
  intro h ε hε N _
  have ⟨ n, hn1, hn2 ⟩ := h (Metric.ball L ε) ⟨ _, hε, by aesop ⟩ N.toNat
  have hn : n ≥ 0 := by positivity
  refine ⟨ n, by rwa [ge_iff_le, ←Int.toNat_le], ?_ ⟩
  simp [Real.dist_eq, hn] at *; linarith

/-- Identification with `Filter.limsup` -/
theorem Chapter6.Sequence.limsup_eq (a:ℕ → ℝ) :
    (a:Sequence).limsup = atTop.limsup (fun n ↦ (a n:EReal)) := by
  simp_rw [Filter.limsup_eq, eventually_atTop]
  sorry

/-- Identification with `Filter.liminf` -/
theorem Chapter6.Sequence.liminf_eq (a:ℕ → ℝ) :
    (a:Sequence).liminf = atTop.liminf (fun n ↦ (a n:EReal)) := by
  simp_rw [Filter.liminf_eq, eventually_atTop]
  sorry

/-- Identification of `rpow` and Mathlib exponentiation -/
theorem Chapter6.Real.rpow_eq_rpow {x:ℝ} (hx: x > 0) (α:ℝ) : rpow x α = x^α := by
  sorry
