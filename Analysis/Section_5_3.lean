import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence
- Construction of a real number type `Chapter5.Real`
- Basic arithmetic operations and properties
-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.isCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext
  . rw [a.zero, b.zero]
  exact h

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by
    intro n hn
    exact (a:Sequence).vanish n hn
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : (mk' ha).toSequence = (a:Sequence) := by rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe := fun a n ↦ a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) : ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext
  . rw [a.zero]
  ext n
  by_cases h:n ≥ 0
  all_goals simp [h]
  rw [a.vanish]
  rw [a.zero]
  exact lt_of_not_ge h

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Sequence.equiv a b) (hbc: Sequence.equiv b c) :
  Sequence.equiv a c := by sorry

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.equiv a b
  iseqv := {
     refl := sorry
     symm := sorry
     trans := sorry
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.isCauchy_of_const (a:ℚ) : ((fun n:ℕ ↦ a):Sequence).isCauchy := by sorry

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.isCauchy_of_const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/-- It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.  This requires Classical logic, because the property of being Cauchy is not computable or decidable.  -/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real := Quotient.mk _ (if h : (a:Sequence).isCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).isCauchy ∧ x = LIM a := by
  -- I had a lot of trouble with this proof; perhaps there is a more idiomatic way to proceed
  apply Quot.ind _ x; intro a
  set a' : ℕ → ℚ := (a:ℕ → ℚ); use a'
  set s : Sequence := (a':Sequence)
  have : s = a.toSequence := CauchySequence.coe_to_sequence a
  rw [this]
  refine ⟨ a.cauchy, ?_ ⟩
  congr
  convert (dif_pos a.cauchy).symm with n
  . apply CauchySequence.ext'
    change a.seq = s.seq
    rw [this]
  classical
  exact Classical.propDecidable _

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) :
  LIM a = LIM b ↔ Sequence.equiv a b := by
  constructor
  . intro h
    replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h
  apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.add_cauchy {a b:ℕ → ℚ}  (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) : (a + b:Sequence).isCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [isCauchy_def] at ha hb ⊢
  intro ε hε
  have : ε/2 > 0 := by exact half_pos hε
  replace ha := ha (ε/2) this
  replace hb := hb (ε/2) this
  rw [Rat.eventuallySteady_def] at ha hb ⊢
  obtain ⟨ N, hN, hha ⟩ := ha
  obtain ⟨ M, hM, hhb ⟩ := hb
  use max N M
  simp at hN hM ⊢
  simp [hN, Rat.steady_def'] at hha hhb ⊢
  intro n m hnN hnM hmN hmM
  have hn := hN.trans hnN
  have hm := hM.trans hmM
  replace hha := hha n m hnN hmN
  replace hhb := hhb n m hn hnM hm hmM
  simp [hn, hm, hnN, hnM, hmN, hmM] at hha hhb ⊢
  convert Section_4_3.add_close hha hhb
  ring

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Sequence.equiv a a') :
  Sequence.equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at haa' ⊢
  intro ε hε
  replace haa' := haa' ε hε
  rw [Rat.eventually_close_def] at haa' ⊢
  obtain ⟨ N, haa' ⟩ := haa'
  use N
  rw [Rat.close_seq_def] at haa' ⊢
  simp at haa' ⊢
  intro n hn hN _ _
  replace haa' := haa' n hn hN hn hN
  simp [hn, hN] at haa' ⊢
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Sequence.equiv b b') :
  Sequence.equiv (a + b) (a + b') := by
  simp_rw [add_comm]
  exact add_equiv_left a hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Sequence.equiv a a') (hbb': Sequence.equiv b b') :
  Sequence.equiv (a + b) (a' + b') := equiv_trans (add_equiv_left b haa') (add_equiv_right a' hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.add_equiv haa' hbb'
      all_goals apply Sequence.add_cauchy
      all_goals rw [CauchySequence.coe_to_sequence]
      . exact a.cauchy
      . exact b.cauchy
      . exact a'.cauchy
      exact b'.cauchy
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.add_of_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  have hab := Sequence.add_cauchy ha hb
  simp_rw [LIM_def ha, LIM_def hb, LIM_def hab]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos _]

/--Proposition 5.3.10 (Product of Cauchy sequences is Cauchy)-/
theorem Sequence.mul_cauchy {a b:ℕ → ℚ}  (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) : (a * b:Sequence).isCauchy := by
  sorry

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Sequence.equiv a a') :
  Sequence.equiv (a * b) (a' * b) := by
  sorry

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Sequence.equiv b b') :
  Sequence.equiv (a * b) (a * b') := by
  simp_rw [mul_comm]
  exact mul_equiv_left a hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv {a b a' b':ℕ → ℚ} (haa': Sequence.equiv a a') (hbb': Sequence.equiv b b') :
  Sequence.equiv (a * b) (a' * b') := equiv_trans (mul_equiv_left b haa') (mul_equiv_right a' hbb')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv haa' hbb'
      all_goals apply Sequence.mul_cauchy
      all_goals rw [CauchySequence.coe_to_sequence]
      . exact a.cauchy
      . exact b.cauchy
      . exact a'.cauchy
      exact b'.cauchy
      )

theorem Real.mul_of_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  have hab := Sequence.mul_cauchy ha hb
  simp_rw [LIM_def ha, LIM_def hb, LIM_def hab]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos _]

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.isCauchy_of_const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by
  rw [LIM_def]
  rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  sorry

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

@[simp]
theorem Real.LIM_zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by
  rw [←ratCast_def 0]
  rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

theorem Real.add_of_ratCast (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by sorry

theorem Real.mul_of_ratCast (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by sorry

noncomputable instance Real.instNeg : Neg Real where
  neg := fun x ↦ ((-1:ℚ):Real) * x

theorem Real.neg_of_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by sorry

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_of_LIM (a:ℕ → ℚ) (ha: (a:Sequence).isCauchy) : -LIM a = LIM (-a) := by sorry

theorem Real.neg_of_cauchy (a:ℕ → ℚ) (ha: (a:Sequence).isCauchy) : ((-a:ℕ → ℚ):Sequence).isCauchy := by sorry


/-- Proposition 5.3.11 -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
AddGroup.ofLeftAxioms (by sorry) (by sorry) (by sorry)

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) :=  rfl

theorem Real.sub_of_cauchy {a b:ℕ → ℚ} (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) : ((a-b:ℕ → ℚ):Sequence).isCauchy := by sorry

theorem Real.sub_of_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) :
  LIM a - LIM b = LIM (a - b) := by sorry

/-- Proposition 5.3.12 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by sorry

/-- Proposition 5.3.12 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry

/-- Proposition 5.3.12 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  natCast_succ := by sorry
  intCast_negSucc := by sorry

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- Definition 5.3.12 (sequences bounded away from zero).  Sequences are indexed to start from zero as this is more convenient for Mathlib purposes. -/
abbrev bounded_away_zero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : bounded_away_zero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : bounded_away_zero (fun n ↦ (-1)^n) := by sorry

/-- Examples 5.3.13 -/
example : ¬ bounded_away_zero (fun n ↦ 10^(-(n:ℤ)-1)) := by sorry

/-- Examples 5.3.13 -/
example : ¬ bounded_away_zero (fun n ↦ 1 - 10^(-(n:ℤ))) := by sorry

/-- Examples 5.3.13 -/
example : bounded_away_zero (fun n ↦ 10^(n+1)) := by sorry

/-- Examples 5.3.13 -/
example : ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).isBounded := by sorry

/-- Lemma 5.3.14 -/
theorem Real.bounded_away_zero_of_nonzero {x:Real} (hx: x ≠ 0) : ∃ a:ℕ → ℚ, (a:Sequence).isCauchy ∧ bounded_away_zero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM_zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.isCauchy_of_const 0), Sequence.equiv_iff] at hx
  simp at hx
  obtain ⟨ ε, hε, hx ⟩ := hx
  have hb' := (Sequence.isCauchy_of_coe _).mp hb (ε/2) (half_pos hε)
  obtain ⟨ N, hb' ⟩ := hb'
  obtain ⟨n₀, hn₀, hx ⟩ := hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by sorry
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then (ε/2) else b n
  have not_hard : Sequence.equiv a b := by sorry
  have ha :(a:Sequence).isCauchy := (Sequence.equiv_of_cauchy not_hard).mpr hb
  refine ⟨ a, ha, ?_, ?_ ⟩
  . rw [bounded_away_zero_def]
    use ε/2, half_pos hε
    intro n
    by_cases hn: n < n₀
    all_goals simp [a, hn]
    . exact le_abs_self _
    apply how
    linarith
  rw[(LIM_eq_LIM ha hb).mpr not_hard]

/-- This result was not explicitly stated in the text, but is needed in the theory. It's a good exercise, so I'm setting it as such. -/
theorem Real.lim_of_bounded_away_zero {a:ℕ → ℚ} (ha: bounded_away_zero a) (ha_cauchy: (a:Sequence).isCauchy) :
  LIM a ≠ 0 := by
   sorry

theorem Real.bounded_away_zero_nonzero {a:ℕ → ℚ} (ha: bounded_away_zero a) (n: ℕ) : a n ≠ 0 := by
   obtain ⟨ c, hc, ha ⟩ := ha
   replace ha := ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_of_bounded_away_zero_cauchy {a:ℕ → ℚ} (ha: bounded_away_zero a) (ha_cauchy: (a:Sequence).isCauchy) :
  ((a⁻¹:ℕ → ℚ):Sequence).isCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := bounded_away_zero_nonzero ha n
  rw [bounded_away_zero_def] at ha
  obtain ⟨ c, hc, ha ⟩ := ha
  simp_rw [Sequence.isCauchy_of_coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε
  replace ha_cauchy := ha_cauchy (c^2 * ε) (by positivity)
  obtain ⟨ N, ha_cauchy ⟩ := ha_cauchy
  use N
  intro n m ⟨hn, hm⟩
  replace ha_cauchy := ha_cauchy n m ⟨hn, hm⟩
  calc
    _ = |(a m - a n) / (a m * a n)| := by
      congr
      field_simp [ha' m, ha' n]
      simp [mul_comm]
    _ ≤ |a m - a n| / c^2 := by
      rw [abs_div, abs_mul, sq]
      gcongr
      . exact ha m
      exact ha n
    _ = |a n - a m| / c^2 := by
      rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by
      gcongr
    _ = ε := by
      field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: bounded_away_zero a) (ha_cauchy: (a:Sequence).isCauchy) (hb: bounded_away_zero b) (hb_cauchy: (b:Sequence).isCauchy) (hlim: LIM a = LIM b) :
  LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have ha' (n:ℕ) : a n ≠ 0 := bounded_away_zero_nonzero ha n
  have hb' (n:ℕ) : b n ≠ 0 := bounded_away_zero_nonzero hb n
  have hainv_cauchy := Real.inv_of_bounded_away_zero_cauchy ha ha_cauchy
  have hbinv_cauchy := Real.inv_of_bounded_away_zero_cauchy hb hb_cauchy
  have haainv_cauchy := Sequence.mul_cauchy hainv_cauchy ha_cauchy
  have habinv_cauchy := Sequence.mul_cauchy hainv_cauchy hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    unfold P
    rw [mul_of_LIM hainv_cauchy ha_cauchy, mul_of_LIM haainv_cauchy hbinv_cauchy]
    rcongr n
    simp [ha' n]
  have claim2 : P = LIM a⁻¹ := by
    unfold P
    rw [hlim, mul_of_LIM hainv_cauchy hb_cauchy, mul_of_LIM habinv_cauchy hbinv_cauchy]
    rcongr n
    simp [hb' n]
  simp [←claim1, ←claim2]

open Classical in
/-- Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to assign a "junk" value to the inverse of 0.  -/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (bounded_away_zero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: bounded_away_zero a) (hc: (a:Sequence).isCauchy) : (LIM a)⁻¹ = LIM a⁻¹ := by
  set x := LIM a
  have hx : x ≠ 0 := lim_of_bounded_away_zero h hc
  set hb := bounded_away_zero_of_nonzero hx
  simp only [instInv, ne_eq, Classical.dite_not, hx, ↓reduceDIte, Pi.inv_apply]
  apply inv_of_equiv hb.choose_spec.2.1 hb.choose_spec.1 h hc hb.choose_spec.2.2.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by
  simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  sorry

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  sorry

theorem Real.inv_of_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  sorry

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := by rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by sorry
  mul_inv_cancel := by sorry
  inv_zero := by sorry
  ratCast_def := by sorry
  qsmul := _
  nnqsmul := _

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by sorry

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by sorry

/-- Exercise 5.3.4 -/
theorem Real.equiv_of_bounded {a b:ℕ → ℚ} (ha: (a:Sequence).isBounded) (hab: Sequence.equiv a b) : (b:Sequence).isBounded := by sorry

/-- Exercise 5.3.5 -/
theorem Real.LIM_of_harmonic : LIM (fun n ↦ 1/n) = 0 := by sorry

end Chapter5
