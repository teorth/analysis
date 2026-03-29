import Mathlib.Tactic
import Analysis.Section_7_3
/-!
# Analysis I, Section 7.4: Rearrangement of series

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Rearrangement of non-negative or absolutely convergent series.
-/

namespace Chapter7

theorem Series.sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0) : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind

/-- Proposition 7.4.1 -/
theorem Series.converges_of_permute_nonneg {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n) : Series).converges ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set af : ℕ → ℝ := fun n ↦ a (f n)
  have haf : (af:Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h, af]
    specialize ha (f n.toNat); grind
  set S := (a:Series).partial
  set T := (af:Series).partial
  have hSmono : Monotone S := Series.partial_of_nonneg ha
  have hTmono : Monotone T := Series.partial_of_nonneg haf
  set L := iSup S
  set L' := iSup T
  have hSBound : ∃ Q, ∀ N, S N ≤ Q := (converges_of_nonneg_iff ha).mp hconv
  suffices : (∃ Q, ∀ M, T M ≤ Q) ∧ L = L'
  . have Ssum : L = (a:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L]
      apply tendsto_atTop_isLUB hSmono (isLUB_csSup _ _)
      . use (S 0); aesop
      choose Q hQ using hSBound; use Q; simp [upperBounds, hQ]
    have Tsum : L' = (af:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L']
      apply tendsto_atTop_isLUB hTmono (isLUB_csSup _ _)
      . use (T 0); aesop
      choose Q hQ using this.1; use Q; simp [upperBounds, hQ]
    simp [←Ssum, ←Tsum, this.2, converges_of_nonneg_iff haf]
    convert this.1
  have hTL (M:ℤ) : T M ≤ L := by
    by_cases hM : M ≥ 0
    swap
    . have hM' : M < 0 := by linarith
      simp [T, Series.partial, hM']
      convert le_ciSup (f := S) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
    set Y := Finset.Iic M.toNat
    have hN : ∃ N, ∀ m ∈ Y, f m ≤ N := by
      use (Y.image f).sup id; intro m hm
      apply Finset.le_sup (f := id); grind
    choose N hN using hN
    calc
      _ = ∑ m ∈ Y, af m := by simp [T, Series.partial, af]; exact sum_eq_sum af hM
      _ = ∑ n ∈ f '' Y, a n := by symm; convert Finset.sum_image (by solve_by_elim [hf.injective]); simp
      _ ≤ ∑ n ∈ .Iic N, a n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro _ _; aesop
        intro i _ _; specialize ha i; aesop
      _ = S N := by simp [S, Series.partial]; symm; apply sum_eq_sum (N:=N) a; positivity
      _ ≤ L := by apply le_ciSup _ (N:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
  have hTbound : ∃ Q, ∀ M, T M ≤ Q := by use L
  simp [hTbound]
  have hSL' (N:ℤ) : S N ≤ L' := by
    by_cases hN : N ≥ 0
    swap
    . have hN' : N < 0 := by linarith
      simp [S, Series.partial, hN']
      convert le_ciSup (f := T) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
    set X := Finset.Iic N.toNat
    have hM : ∃ M, ∀ n ∈ X, ∃ m, f m = n ∧ m ≤ M := by
      use (X.preimage f (Set.injOn_of_injective hf.1)).sup id
      intro n hn; choose m hm using hf.2 n
      refine ⟨ _, hm, ?_ ⟩
      apply Finset.le_sup (f := id)
      simp [Finset.mem_preimage, hm, hn]
    choose M hM using hM
    have sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0)
      : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
    calc
      _ = ∑ n ∈ X, a n := by simp [S, sum_eq_sum, hN, X]
      _ = ∑ n ∈ ((Finset.Iic M).filter (f · ∈ X)).image f, a n := by
        congr; ext; simp; constructor
        . intro h; obtain ⟨ m, rfl, hm' ⟩ := hM _ h; use m
        rintro ⟨ _, ⟨ _, _⟩, rfl ⟩; simp_all
      _ ≤ ∑ m ∈ .Iic M, af m := by
        rw [Finset.sum_image (by solve_by_elim [hf.injective])]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        . aesop
        intro i _ _; specialize haf i; aesop
      _ = T M := by simp [T, Series.partial, af]; symm; apply sum_eq_sum af; positivity
      _ ≤ L' := by apply le_ciSup _ (M:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
  linarith [ciSup_le hSL', ciSup_le hTL]

/-- Example 7.4.2 -/
theorem Series.zeta_2_converges : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).converges := by sorry

theorem Series.permuted_zeta_2_converges :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).converges := by
    sorry

theorem Series.permuted_zeta_2_eq_zeta_2 :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum := by
    sorry

/-- Proposition 7.4.3 (Rearrangement of series) -/
theorem Series.absConverges_of_permute {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set L := (a:Series).abs.sum
  have hconv := converges_of_absConverges ha
  unfold absConverges at ha
  have habs : (fun n ↦ |a (f n)| : Series).converges ∧ L = (fun n ↦ |a (f n)| : Series).sum := by
    convert converges_of_permute_nonneg (a := fun n ↦ |a n|) _ _ hf using 3
    . simp; ext n; by_cases n ≥ 0 <;> grind
    . intro n; by_cases h: n ≥ 0 <;> simp [h]
    convert ha with n; by_cases n ≥ 0 <;> grind
  set L' := (a:Series).sum
  set af : ℕ → ℝ := fun n ↦ a (f n)
  suffices : (af:Series).convergesTo L'
  . simp [sum_of_converges this, absConverges]
    convert habs.1 with n; by_cases n ≥ 0 <;> grind
  simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds]
  intro ε hε
  rw [converges_iff_tail_decay] at ha
  choose N₁ hN₁ ha using ha _ (half_pos hε); simp at hN₁
  have : ∃ N ≥ N₁, |(a:Series).partial N - L'| < ε/2 := by
    apply convergesTo_sum at hconv
    simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds] at hconv
    choose N hN using hconv _ (half_pos hε)
    use max N N₁, (by grind); apply hN; grind
  choose N hN hN2 using this
  have hNpos : N ≥ 0 := by linarith
  let finv : ℕ → ℕ := Function.invFun f
  have : ∃ M, ∀ n ≤ N.toNat, finv n ≤ M := by
    use ((Finset.Iic (N.toNat)).image finv).sup id
    intro n hn
    apply Finset.le_sup (f := id); simp [Finset.mem_image]; use n, hn; rfl
  choose M hM using this; use M; intro M' hM'
  have hM'_pos : M' ≥ 0 := by linarith
  have why : (Finset.Iic M'.toNat).image f ⊇ .Iic N.toNat := by
    sorry
  set X : Finset ℕ := (Finset.Iic M'.toNat).image f \ .Iic N.toNat
  have claim : ∑ m ∈ .Iic M'.toNat, a (f m) = ∑ n ∈ .Iic N.toNat, a n + ∑ n ∈ X, a n := calc
    _ = ∑ n ∈ (Finset.Iic M'.toNat).image f , a n := by
      symm; apply Finset.sum_image; solve_by_elim [hf.1]
    _ = _ := by
      convert Finset.sum_union _ using 2
      . simp [X, why]
      . infer_instance
      rw [Finset.disjoint_right]; intro n hn; simp only [X, Finset.mem_sdiff] at hn; tauto
  choose q' hq using X.bddAbove
  set q := max q' N.toNat
  have why2 : X ⊆ Finset.Icc (N.toNat+1) q := by sorry
  have claim2 : |∑ n ∈ X, a n| ≤ ε/2 := calc
    _ ≤ ∑ n ∈ X, |a n| := X.abs_sum_le_sum_abs a
    _ ≤ ∑ n ∈ .Icc (N.toNat+1) q, |a n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg why2; simp
    _ ≤ ε/2 := by
      convert ha (N.toNat+1) _ q _ <;> try omega
      simp [hNpos]; rw [abs_of_nonneg (by positivity)]; symm
      convert Finset.sum_image (g := fun (n:ℕ) ↦ (n:ℤ)) (by simp) using 2
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
  calc
    _ ≤ |(af:Series).partial M' - (a:Series).partial N| + |(a:Series).partial N - L'| := abs_sub_le _ _ _
    _ < |(af:Series).partial M' - (a:Series).partial N| + ε/2 := by gcongr
    _ ≤ ε/2 + ε/2 := by
      gcongr; convert claim2
      simp [Series.partial, sum_eq_sum _ hM'_pos, sum_eq_sum _ hNpos]; grind
    _ = ε := by ring


/-- Example 7.4.4 -/
noncomputable abbrev Series.a_7_4_4 : ℕ → ℝ := fun n ↦ (-1:ℝ)^n / (n+2)

theorem Series.ex_7_4_4_conv : (a_7_4_4 : Series).converges := by sorry

theorem Series.ex_7_4_4_sum : (a_7_4_4 : Series).sum > 0 := by sorry

abbrev Series.f_7_4_4 : ℕ → ℕ := fun n ↦ if n % 3 = 0 then 2 * (n/3) else 4 * (n/3) + 2 * (n % 3) - 1

theorem Series.f_7_4_4_bij : Function.Bijective f_7_4_4 := by sorry

theorem Series.ex_7_4_4'_conv : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges := by sorry

theorem Series.ex_7_4_4'_sum : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by sorry

/-- Exercise 7.4.1 -/
theorem Series.absConverges_of_subseries {a:ℕ → ℝ} (ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: StrictMono f) :
  (fun n ↦ a (f n):Series).absConverges := by sorry

/--
{given -show}`n : ℕ`
Exercise 7.4.2 : reprove Proposition 7.4.3 using Proposition 7.41, Proposition 7.2.14,
and expressing {lean}`a n` as the difference of {lean}`a n + |a n|` and {lean}`|a n|`.
-/
theorem Series.absConverges_of_permute' {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n):Series).sum := by sorry

end Chapter7
