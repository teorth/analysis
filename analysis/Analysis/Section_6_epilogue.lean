import Mathlib.Tactic
import Analysis.Section_6_7

/-!
# Analysis I, Chapter 6 epilogue

In this (technical) epilogue, we show that various operations and properties we have defined for
"Chapter 6" sequences `Chapter6.Sequence` are equivalent to Mathlib operations.  Note however
that Mathlib's operations are defined in far greater generality than the setting of real-valued
sequences, in particular using the language of filters.

-/

/-- Identification with the Cauchy sequence support in Mathlib/Algebra/Order/CauSeq/Basic -/
theorem Chapter6.Sequence.Cauchy_iff_CauSeq (a: ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ IsCauSeq _root_.abs a := by
  simp_rw [isCauchy_of_coe, Real.dist_eq, IsCauSeq]
  constructor
  . intro h ε hε
    specialize h (ε/2) (half_pos hε)
    obtain ⟨ N, h ⟩ := h
    use N
    intro n hn
    specialize h n hn N (le_refl _)
    linarith
  intro h ε hε
  specialize h (ε/2) (half_pos hε)
  obtain ⟨ N, h ⟩ := h
  use N
  intro n hn m hm
  calc
    _ ≤ |a n - a N| + |a m - a N| := by rw [abs_sub_comm (a m) (a N)]; exact abs_sub_le _ _ _
    _ ≤ ε/2 + ε/2 := by apply le_of_lt; gcongr; exact h n hn; exact h m hm
    _ = _ := by linarith

/-- Identification with the Cauchy sequence support in Mathlib/Topology/UniformSpace/Cauchy -/
theorem Chapter6.Sequence.Cauchy_iff_CauchySeq (a: ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ CauchySeq a := by
  rw [Cauchy_iff_CauSeq]
  convert isCauSeq_iff_cauchySeq

/-- Identification with `Filter.Tendsto` -/
theorem Chapter6.Sequence.tendsto_iff_Tendsto (a: ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ Filter.Tendsto a Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor
  . intro h ε hε
    specialize h (ε/2) (half_pos hε)
    obtain ⟨ N, hN ⟩ := h
    use N.toNat
    intro n hn
    specialize hN n (Int.toNat_le.mp hn)
    simp at hN
    rw [Real.dist_eq]
    linarith
  intro h ε hε
  specialize h ε hε
  obtain ⟨ N, hN ⟩ := h
  use N
  intro n hn
  have hpos : n ≥ 0 := LE.le.trans (by positivity) hn
  rw [ge_iff_le, ←Int.le_toNat hpos] at hn
  specialize hN n.toNat hn
  simp [hpos, ←Real.dist_eq]
  exact le_of_lt hN

theorem Chapter6.Sequence.tendsto_iff_Tendsto' (a: Sequence) (L:ℝ) : a.TendsTo L ↔ Filter.Tendsto a.seq Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor
  . intro h ε hε
    specialize h (ε/2) (half_pos hε)
    obtain ⟨ N, hN ⟩ := h
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq]
    linarith
  intro h ε hε
  specialize h ε hε
  obtain ⟨ N, hN ⟩ := h
  use N
  intro n hn
  rw [ge_iff_le] at hn
  specialize hN n hn
  simp [←Real.dist_eq]
  exact le_of_lt hN

theorem Chapter6.Sequence.converges_iff_Tendsto (a: ℕ → ℝ) :
    (a:Sequence).Convergent ↔ ∃ L, Filter.Tendsto a Filter.atTop (nhds L) := by
  simp_rw [←tendsto_iff_Tendsto]

theorem Chapter6.Sequence.converges_iff_Tendsto' (a: Sequence) : a.Convergent ↔ ∃ L, Filter.Tendsto a.seq Filter.atTop (nhds L) := by
  simp_rw [←tendsto_iff_Tendsto']

/-- A technicality: `CauSeq.IsComplete ℝ` was established for `_root_.abs` but not for `norm`. -/
instance inst_real_complete : CauSeq.IsComplete ℝ norm := by
  convert Real.instIsCompleteAbs

/-- Identification with `CauSeq.lim` -/
theorem Chapter6.Sequence.lim_eq_CauSeq_lim (a:ℕ → ℝ) (ha: (a:Sequence).IsCauchy) :
    Chapter6.lim (a:Sequence) = CauSeq.lim  ⟨ a, (Cauchy_iff_CauSeq a).mp ha⟩ := by
  have h1 := CauSeq.tendsto_limit ⟨ a, (Cauchy_iff_CauSeq a).mp ha⟩
  have h2 := lim_def ((a:Sequence).Cauchy_iff_convergent.mp ha)
  rw [←tendsto_iff_Tendsto] at h1
  by_contra! h
  replace h := (a:Sequence).tendsTo_unique h
  tauto

/-- Identification with `Bornology.IsBounded` -/
theorem Chapter6.Sequence.isBounded_iff_isBounded_range (a:ℕ → ℝ):
    (a:Sequence).IsBounded ↔ Bornology.IsBounded (Set.range a) := by
  simp [isBounded_def, BoundedBy_def, Metric.isBounded_iff]
  constructor
  . intro h
    obtain ⟨ M, hM, h ⟩ := h
    use 2*M
    intro n m
    calc
      _ = |a n - a m| := Real.dist_eq _ _
      _ ≤ |a n| + |a m| := abs_sub _ _
      _ ≤ M + M := by gcongr; convert h n; convert h m
      _ = _ := by ring
  intro h
  obtain ⟨ C, h ⟩ := h
  have : C ≥ 0 := by
    specialize h 0 0
    simp at h
    assumption
  refine ⟨ C + |a 0|, by positivity, ?_ ⟩
  intro n
  by_cases hn: n ≥ 0
  all_goals simp [hn]
  . calc
      _ ≤ |a n.toNat - a 0| + |a 0| := by
        convert abs_add_le _ _
        . abel
        infer_instance
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
    (a:Sequence).LimitPoint L ↔ MapClusterPt L Filter.atTop a := by
  simp_rw [limit_point_def, mapClusterPt_iff_frequently,
           Filter.frequently_atTop, Metric.mem_nhds_iff]
  constructor
  . intro h s hs N
    obtain ⟨ ε, hε, hεs ⟩ := hs
    specialize h (ε/2) (half_pos hε) N (by positivity)
    obtain ⟨ n, hn1, hn2 ⟩ := h
    have hn : n ≥ 0 := LE.le.trans (by positivity) hn1
    refine ⟨ n.toNat, ?_, ?_ ⟩
    . rwa [ge_iff_le, Int.le_toNat hn]
    apply hεs
    simp [Real.dist_eq, hn] at hn2 ⊢
    linarith
  intro h ε hε N hN
  specialize h (Metric.ball L ε) ⟨ ε, hε, fun ⦃a⦄ a ↦ a ⟩ N.toNat
  obtain ⟨ n, hn1, hn2 ⟩ := h
  have hn : n ≥ 0 := by positivity
  refine ⟨ n, ?_, ?_ ⟩
  . rwa [ge_iff_le, ←Int.toNat_le]
  simp [Real.dist_eq, hn] at hn2 ⊢
  linarith

/-- Identification with `Filter.limsup` -/
theorem Chapter6.Sequence.limsup_eq (a:ℕ → ℝ) :
    (a:Sequence).limsup = Filter.limsup (fun n ↦ (a n:EReal)) Filter.atTop := by
  simp_rw [Filter.limsup_eq, Filter.eventually_atTop]
  sorry

/-- Identification with `Filter.liminf` -/
theorem Chapter6.Sequence.liminf_eq (a:ℕ → ℝ) :
    (a:Sequence).liminf = Filter.liminf (fun n ↦ (a n:EReal)) Filter.atTop := by
  simp_rw [Filter.liminf_eq, Filter.eventually_atTop]
  sorry

/-- Identification of `rpow` and Mathlib exponentiation -/
theorem Chapter6.Real.rpow_eq_rpow (x:ℝ) (α:ℝ) : rpow x α = x^α := by
  sorry
