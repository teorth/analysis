import Mathlib.Tactic
import Analysis.Section_9_9
import Analysis.Section_11_4

/-!
# Analysis I, Section 11.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of uniformly continuous functions
- Riemann integrability of bounded continuous functions

-/

namespace Chapter11
open BoundedInterval
open Chapter9

/-- Theorem 11.5.1 -/
theorem integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I) :
  IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  have hfbound : BddOn f I := by
    rw [BddOn.iff']
    exact UniformContinuousOn.of_bounded hf subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  refine ⟨ hfbound, ?_ ⟩
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1.2
  simp [length] at hsing
  set a := I.a
  set b := I.b
  have hsing' : 0 < b-a := by linarith
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ ε * (b-a) := by
    rw [UniformContinuousOn.iff] at hf
    specialize hf ε hε
    obtain ⟨ δ, hδ, hf ⟩ := hf
    simp [Real.Close, Real.dist_eq] at hf
    obtain ⟨ N, hN ⟩ :=exists_nat_gt ((b-a)/δ)
    have hNpos : 0 < N := by
      have : 0 < (b-a)/δ := by positivity
      replace := this.trans hN
      norm_cast at this
    have hN' : (b-a)/N < δ := by rwa [div_lt_comm₀ (by positivity) (by positivity)]
    have : ∃ P: Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = (b-a) / N := by
      sorry
    obtain ⟨ P, hcard, hlength ⟩ := this
    calc
      _ ≤ ∑ J ∈ P.intervals, (sSup (f '' J) - sInf (f '' J)) * |J|ₗ := by
        simp [sub_mul]
        have h1 := upper_integ_le_upper_sum hfbound P
        have h2 := lower_integ_ge_lower_sum hfbound P
        unfold upper_riemann_sum at h1
        unfold lower_riemann_sum at h2
        linarith
      _ ≤ ∑ J ∈ P.intervals, ε * |J|ₗ := by
        apply Finset.sum_le_sum
        intro J hJ
        gcongr
        have (x y:ℝ) (hx: x ∈ J) (hy: y ∈ J) : f x ≤ f y + ε := by
          have : J ⊆ I := P.contains J hJ
          have : |f x - f y| ≤ ε := by
            apply hf y _ x _ _
            . exact this _ hy
            . exact this _ hx
            apply (BoundedInterval.dist_le_length hx hy).trans
            simp [hlength J hJ, le_of_lt hN']
          rw [abs_le'] at this
          linarith
        have hJnon : (f '' J).Nonempty := by
          simp
          by_contra! h
          replace h : Subsingleton (J:Set ℝ) := by simp [h]
          simp only [length_of_subsingleton, hlength J hJ] at h
          have : 0 < (b-a) / N := by positivity
          linarith
        replace (y:ℝ) (hy:y ∈ J) : sSup (f '' J) ≤ f y + ε := by
          apply csSup_le hJnon
          intro a ha
          simp at ha
          obtain ⟨ x, hx, rfl ⟩ := ha
          simp_rw [mem_iff] at this
          exact this x y hx hy
        replace : sSup (f '' J) - ε ≤ sInf (f '' J) := by
          apply le_csInf hJnon
          intro a ha
          simp at ha
          obtain ⟨ y, hy, rfl ⟩ := ha
          simp_rw [mem_iff] at this
          specialize this y hy
          linarith
        linarith
      _ = ∑ J ∈ P.intervals, ε * (b-a)/N := by
        apply Finset.sum_congr rfl
        intro J hJ; simp [hlength J hJ]; ring
      _ = _ := by
        simp [hcard]; field_simp
  have lower_le_upper : 0 ≤ upper_integral f I - lower_integral f I := by linarith [lower_integral_le_upper hfbound]
  rw [le_iff_lt_or_eq] at lower_le_upper
  rcases lower_le_upper with h | h
  . set ε := (upper_integral f I - lower_integral f I)/(2*(b-a))
    specialize this ε (by positivity)
    simp only [ε] at this
    replace : upper_integral f I - lower_integral f I ≤ (upper_integral f I - lower_integral f I)/2 := by
      convert this using 1
      field_simp; ring
    linarith
  linarith

/-- Corollary 11.5.2 -/
theorem integ_of_cts {a b:ℝ} {f:ℝ → ℝ} (hf: ContinuousOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := integ_of_uniform_cts (UniformContinuousOn.of_continuousOn hf)

example : ContinuousOn (fun x:ℝ ↦ 1/x) (Icc 0 1) := by sorry

example : ¬ IntegrableOn (fun x:ℝ ↦ 1/x) (Icc 0 1) := by sorry

/-- Proposition 11.5.3-/
theorem integ_of_bdd_cts {I: BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: ContinuousOn f I) : IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1
  have hI : (I:Set ℝ).Nonempty := by
    by_contra!
    rw [←BoundedInterval.length_of_subsingleton] at hsing
    aesop
  simp at hsing
  set a := I.a
  set b := I.b
  have lower_le_upper := lower_integral_le_upper hbound
  have := hbound
  obtain ⟨ M, hM ⟩ := this
  have hMpos : 0 ≤ M := by
    specialize hM hI.some hI.some_mem
    exact (abs_nonneg _).trans hM
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ (4*M+2) * ε := by
    wlog hε' : ε < (b-a)/2
    . simp at hε'
      specialize this hbound hf hI hsing lower_le_upper M hM hMpos ((b-a)/3) (by linarith) (by linarith)
      apply this.trans
      gcongr
      linarith
    set I' := Icc (a+ε) (b-ε)
    set Ileft : BoundedInterval := match I with
    | Icc _ _ => Ico a (a + ε)
    | Ico _ _ => Ico a (a + ε)
    | Ioc _ _ => Ioo a (a + ε)
    | Ioo _ _ => Ioo a (a + ε)
    set Iright : BoundedInterval := match I with
    | Icc _ _ => Ioc (b - ε) b
    | Ico _ _ => Ioo (b - ε) b
    | Ioc _ _ => Ioc (b - ε) b
    | Ioo _ _ => Ioo (b - ε) b
    set Ileft' : BoundedInterval := match I with
    | Icc _ _ => Icc a (b - ε)
    | Ico _ _ => Icc a (b - ε)
    | Ioc _ _ => Ioc a (b - ε)
    | Ioo _ _ => Ioc a (b - ε)
    have Ileftlen : |Ileft|ₗ = ε := by
      cases I
      case Icc _ _ => simp [Ileft, length, le_of_lt hε]
      case Ico _ _ => simp [Ileft, length, le_of_lt hε]
      case Ioc _ _ => simp [Ileft, length, le_of_lt hε]
      case Ioo _ _ => simp [Ileft, length, le_of_lt hε]
    have Irightlen : |Iright|ₗ = ε := by
      cases I
      case Icc _ _ => simp [Iright, length, le_of_lt hε]
      case Ico _ _ => simp [Iright, length, le_of_lt hε]
      case Ioc _ _ => simp [Iright, length, le_of_lt hε]
      case Ioo _ _ => simp [Iright, length, le_of_lt hε]
    have hjoin1 : Ileft'.joins Ileft I' := by
      cases I
      case Icc _ _ => exact join_Ico_Icc (by linarith) (by linarith)
      case Ico _ _ => exact join_Ico_Icc (by linarith) (by linarith)
      case Ioc _ _ => exact join_Ioo_Icc (by linarith) (by linarith)
      case Ioo _ _ => exact join_Ioo_Icc (by linarith) (by linarith)
    have hjoin2: I.joins Ileft' Iright := by
      cases I
      case Icc _ _ => exact join_Icc_Ioc (by linarith) (by linarith)
      case Ico _ _ => exact join_Icc_Ioo (by linarith) (by linarith)
      case Ioc _ _ => exact join_Ioc_Ioc (by linarith) (by linarith)
      case Ioo _ _ => exact join_Ioc_Ioo (by linarith) (by linarith)
    have hf' : IntegrableOn f I' := by
      apply integ_of_cts (ContinuousOn.mono hf _)
      apply subset_trans _ ((subset_iff _ _).mp (Ioo_subset I))
      intro x
      simp
      intro h1 h2; exact ⟨ by linarith, by linarith ⟩
    obtain ⟨ h, hhmin, hhconst, hhint ⟩ := lt_of_gt_upper_integral hf'.1 (show upper_integral f I' < integ f I' + ε by linarith [hf'.2])
    classical
    set h' : ℝ → ℝ := fun x ↦ if x ∈ I' then h x else M
    have h'const_left (x:ℝ) (hx: x ∈ Ileft) : h' x = M := by
      simp [h', hx, mem_iff]
      intro hx'
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp at hjoin1
      tauto
    have h'const_right (x:ℝ) (hx: x ∈ Iright) : h' x = M := by
      simp [h', hx, mem_iff]
      intro hx'
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (fun A ↦ x ∈ A) hjoin1.2.1
      simp at hjoin1 hjoin2
      tauto
    have h'const : PiecewiseConstantOn h' I := by
      rw [PiecewiseConstantOn.of_join hjoin2 _]
      constructor
      . rw [PiecewiseConstantOn.of_join hjoin1 _]
        constructor
        . apply PiecewiseConstantOn.of_const
          exact ConstantOn.of_const h'const_left
        apply (PiecewiseConstantOn.congr _).mp hhconst
        intro x hx
        simp [h', hx, mem_iff]
      apply PiecewiseConstantOn.of_const
      exact ConstantOn.of_const h'const_right
    have h'maj : MajorizesOn h' f I := by
      intro x hx
      by_cases hxI': x ∈ I'
      all_goals simp [h', hxI']
      . exact hhmin x hxI'
      specialize hM x hx; rw [abs_le'] at hM; tauto
    replace h'maj := upper_integral_le_integ hbound h'maj h'const
    have h'integ1 := PiecewiseConstantOn.integ_of_join hjoin2 h'const
    have h'integ2 := PiecewiseConstantOn.integ_of_join hjoin1 ((PiecewiseConstantOn.of_join hjoin2 _).mp h'const).1
    have h'integ3 : PiecewiseConstantOn.integ h' Ileft = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_left, PiecewiseConstantOn.integ_const, Ileftlen]
    have h'integ4 : PiecewiseConstantOn.integ h' Iright = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_right, PiecewiseConstantOn.integ_const, Irightlen]
    have h'integ5 : PiecewiseConstantOn.integ h' I' = PiecewiseConstantOn.integ h I' := by
      apply PiecewiseConstantOn.integ_congr
      intro x hx
      simp [h', hx, mem_iff]
    obtain ⟨ g, hgmin, hgconst, hgint ⟩ := gt_of_lt_lower_integral hf'.1 (show integ f I' - ε < lower_integral f I' by linarith [hf'.2])
    set g' : ℝ → ℝ := fun x ↦ if x ∈ I' then g x else -M
    have g'const_left (x:ℝ) (hx: x ∈ Ileft) : g' x = -M := by
      simp [g', hx, mem_iff]
      intro hx'
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp at hjoin1
      tauto
    have g'const_right (x:ℝ) (hx: x ∈ Iright) : g' x = -M := by
      simp [g', hx, mem_iff]
      intro hx'
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (fun A ↦ x ∈ A) hjoin1.2.1
      simp at hjoin1 hjoin2
      tauto
    have g'const : PiecewiseConstantOn g' I := by
      rw [PiecewiseConstantOn.of_join hjoin2 _]
      constructor
      . rw [PiecewiseConstantOn.of_join hjoin1 _]
        constructor
        . apply PiecewiseConstantOn.of_const
          exact ConstantOn.of_const g'const_left
        apply (PiecewiseConstantOn.congr _).mp hgconst
        intro x hx
        simp [g', hx, mem_iff]
      apply PiecewiseConstantOn.of_const
      exact ConstantOn.of_const g'const_right
    have g'maj : MinorizesOn g' f I := by
      intro x hx
      by_cases hxI': x ∈ I'
      all_goals simp [g', hxI']
      . exact hgmin x hxI'
      specialize hM x hx; rw [abs_le'] at hM; linarith
    replace g'maj := integ_le_lower_integral hbound g'maj g'const
    have g'integ1 := PiecewiseConstantOn.integ_of_join hjoin2 g'const
    have g'integ2 := PiecewiseConstantOn.integ_of_join hjoin1 ((PiecewiseConstantOn.of_join hjoin2 _).mp g'const).1
    have g'integ3 : PiecewiseConstantOn.integ g' Ileft = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_left, PiecewiseConstantOn.integ_const, Ileftlen]
    have g'integ4 : PiecewiseConstantOn.integ g' Iright = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_right, PiecewiseConstantOn.integ_const, Irightlen]
    have g'integ5 : PiecewiseConstantOn.integ g' I' = PiecewiseConstantOn.integ g I' := by
      apply PiecewiseConstantOn.integ_congr
      intro x hx
      simp [g', hx, mem_iff]
    ring_nf
    linarith
  replace := nonneg_of_le_const_mul_eps this
  exact ⟨ hbound, by linarith ⟩

/-- Definition 11.5.4 -/
abbrev PiecewiseContinuousOn (f:ℝ → ℝ) (I:BoundedInterval) : Prop :=
  ∃ P: Partition I, ∀ J ∈ P.intervals, ContinuousOn f J

/-- Example 11.5.5 -/
noncomputable abbrev f_11_5_5 : ℝ → ℝ := fun x ↦
  if x < 2 then x^2
  else if x = 2 then 7
  else x^3

example : ¬ ContinuousOn f_11_5_5 (Icc 1 3) := by sorry

example : ContinuousOn f_11_5_5 (Ico 1 2) := by sorry

example : ContinuousOn f_11_5_5 (Icc 2 2) := by sorry

example : ContinuousOn f_11_5_5 (Ioc 2 3) := by sorry

example : PiecewiseContinuousOn f_11_5_5 (Icc 1 3) := by sorry

/-- Proposition 11.5.6 / Exercise 11.5.1 -/
theorem integ_of_bdd_piecewise_cts {I: BoundedInterval} {f:ℝ → ℝ}
  (hbound: BddOn f I) (hf: PiecewiseContinuousOn f I) : IntegrableOn f I := by
  sorry

/-- Exercise 11.5.2 -/
theorem integ_zero {a b:ℝ} (hab: a ≤ b) (f: ℝ → ℝ) (hf: ContinuousOn f (Icc a b))
  (hnonneg: MajorizesOn f (fun _ ↦ 0) (Icc a b)) (hinteg : integ f (Icc a b) = 0) :
  ∀ x ∈ Icc a b, f x = 0 := by
    sorry

end Chapter11
