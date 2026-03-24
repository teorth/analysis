import Mathlib.Tactic

/-! Some finite probability theory -/

namespace ProbabilityTheory

class FinitelyAdditive (A:Type*) [BooleanAlgebra A] where
  prob : A → ℝ
  prob_top : prob ⊤ = 1
  prob_nonneg (E:A) : 0 ≤ prob E
  prob_disj_sup {E F:A} (hEF: Disjoint E F) : prob (E ⊔ F) = prob E + prob F

namespace FinitelyAdditive

instance instFunLike (A:Type*) [BooleanAlgebra A] : FunLike (FinitelyAdditive A) A ℝ where
  coe ℙ := ℙ.prob
  coe_injective' f g h := by { cases f; cases g; congr }

variable {A:Type*} [BooleanAlgebra A] (ℙ: FinitelyAdditive A)
         {A':Type*} [BooleanAlgebra A'] (ℙ': FinitelyAdditive A')

@[simp]
theorem top : ℙ ⊤ = 1 := ℙ.prob_top

theorem nonneg (E:A) : 0 ≤ ℙ E := ℙ.prob_nonneg E

theorem disj_sup {E F:A} (hEF: Disjoint E F) : ℙ (E ⊔ F) = ℙ E + ℙ F := ℙ.prob_disj_sup hEF

@[simp]
theorem bot : ℙ ⊥ = 0 := by
  have : Disjoint (⊥:A) ⊥ := fun ⦃x⦄ a _ ↦ a
  replace := ℙ.disj_sup this
  simpa using this

@[simp]
theorem compl (E:A) : ℙ Eᶜ = 1 - ℙ E := by
  have : Disjoint Eᶜ E := disjoint_compl_left
  replace := ℙ.disj_sup this
  simp at this
  linarith

theorem le_one (E:A) : ℙ E ≤ 1 := by
  linarith [ℙ.compl E, ℙ.nonneg Eᶜ]

theorem ge_eq_add_diff {E F:A} (hEF: E ≤ F) : ℙ F = ℙ (F \ E) + ℙ E := by
  have : Disjoint (F \ E) E := disjoint_sdiff_self_left
  replace := ℙ.disj_sup this
  rwa [sdiff_sup_cancel hEF] at this

theorem mono {E F:A} (hEF: E ≤ F) : ℙ E ≤ ℙ F := by
  linarith [ℙ.nonneg (F \ E), ℙ.ge_eq_add_diff hEF]

theorem sup_add_inf (E F:A) : ℙ (E ⊔ F) + ℙ (E ⊓ F) = ℙ E + ℙ F := by
  have h₁ : E ⊓ F ≤ E := inf_le_left; replace h₁ := ℙ.ge_eq_add_diff h₁
  have h₂ : F ≤ E ⊔ F := le_sup_right; replace h₂ := ℙ.ge_eq_add_diff h₂
  simp at h₁ h₂
  linarith

theorem sup_le_add (E F:A) : ℙ (E ⊔ F) ≤ ℙ E + ℙ F := by
  linarith [ℙ.sup_add_inf E F, ℙ.nonneg (E ⊓ F)]




-- Some API for extending a finitely additive probability space

def _root_.BoundedLatticeHom.preserves (f: BoundedLatticeHom A A') : Prop := ∀ E:A, ℙ' (f E) = ℙ E

@[simp]
theorem _root_.BoundedLatticeHom.preserves.map {f: BoundedLatticeHom A A'} (hf: f.preserves ℙ ℙ') (E:A) : ℙ' (f E) = ℙ E := hf E

-- an example of how a probability space can be extended while preserving various properties

class ExampleProb {A:Type*} [BooleanAlgebra A] (ℙ: FinitelyAdditive A) where
  E : A
  F : A
  G : A
  prob_E : ℙ E = 0.5
  prob_EF : ℙ (E ⊔ F) = 0.75
  prob_EF' : ℙ (E ⊓ F) = 0.25
  prob_EG : ℙ (E \ G) = 0.4
  prob_G : ℙ Gᶜ = 0.3

@[implicit_reducible] def ExampleProb.map {Ω: ExampleProb ℙ} {f: BoundedLatticeHom A A'} (hf: f.preserves ℙ ℙ') : ExampleProb ℙ' where
  E := f Ω.E
  F := f Ω.F
  G := f Ω.G
  prob_E := by simp [hf, Ω.prob_E]
  prob_EF := by simp [hf, Ω.prob_EF, ←map_sup]
  prob_EF' := by simp [hf, Ω.prob_EF', ←map_inf]
  prob_EG := by simp [hf, Ω.prob_EG, ←map_sdiff']
  prob_G := by simp [hf, Ω.prob_G, ←map_compl']


end FinitelyAdditive
end ProbabilityTheory
