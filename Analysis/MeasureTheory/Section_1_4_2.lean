import Mathlib.SetTheory.Cardinal.Aleph
import Analysis.MeasureTheory.Section_1_4_1
/-!
# Introduction to Measure Theory, Section 1.4.2: $\sigma$-algebras and measurable spaces

A companion to (the introduction to) Section 1.4.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.4.12 (Sigma algebra) -/
class ConcreteSigmaAlgebra (X:Type*) extends ConcreteBooleanAlgebra X where
  countable_union_mem : ∀ E : ℕ → Set X, (∀ n, measurable (E n)) → measurable (⋃ n, E n)

def ConcreteSigmaAlgebra.toMeasurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X :=
  by sorry

def MeasurableSpace.toConcreteSigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X :=
  by sorry

def ConcreteBooleanAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteBooleanAlgebra X) : Prop := ∀ E : ℕ → Set X, (∀ n, measurable (E n)) → measurable (⋃ n, E n)

theorem ConcreteSigmaAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteSigmaAlgebra X) : B.isSigmaAlgebra :=
  B.countable_union_mem

def ConcreteBooleanAlgebra.isSigmaAlgebra.toSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isSigmaAlgebra) : ConcreteSigmaAlgebra X :=
  { countable_union_mem := h }

/-- Exercise 1.4.10 -/
def ConcreteBooleanAlgebra.isAtomic.isSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isAtomic) : B.isSigmaAlgebra :=
  by sorry

/-- Exercise 1.4.11 -/
theorem LebesgueMeasurable.boolean_algebra.isSigmaAlgebra (d:ℕ) : (LebesgueMeasurable.boolean_algebra d).isSigmaAlgebra :=
  by sorry

def LebesgueMeasurable.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (LebesgueMeasurable.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

theorem IsNull.boolean_algebra.isSigmaAlgebra (d:ℕ) : (IsNull.boolean_algebra d).isSigmaAlgebra :=
  by sorry

def IsNull.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (IsNull.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

theorem JordanMeasurable.boolean_algebra.not_isSigmaAlgebra (d:ℕ) (hd: d ≥ 1) :
  ¬ (JordanMeasurable.boolean_algebra d).isSigmaAlgebra :=
  by sorry

/-- Exercise 1.4.12 -/
theorem ConcreteSigmaAlgebra.restrict_is_sigma {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X): (B.restrict A).isSigmaAlgebra := by sorry

def ConcreteSigmaAlgebra.restrict {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X) : ConcreteSigmaAlgebra A := (B.restrict_is_sigma A).toSigmaAlgebra

instance ConcreteSigmaAlgebra.instLE (X:Type*) : LE (ConcreteSigmaAlgebra X) :=
  ⟨fun B1 B2 => ∀ E, B1.measurable E → B2.measurable E⟩

instance ConcreteSigmaAlgebra.instPartialOrder (X:Type*) : PartialOrder (ConcreteSigmaAlgebra X) :=
  {
    le_refl := fun B E hE => hE
    le_trans := fun A B C hAB hBC E hE => hBC E (hAB E hE)
    le_antisymm := by
      intro A B hAB hBA
      have : A.measurable = B.measurable := by
        ext E
        exact ⟨hAB E, hBA E⟩
      cases A
      cases B
      congr
  }

instance ConcreteSigmaAlgebra.instOrderTop {X:Type*} : OrderTop (ConcreteSigmaAlgebra X) :=
  {
    top := {
      measurable := fun _ => True
      empty_mem := trivial
      compl_mem := fun _ _ => trivial
      union_mem := fun _ _ _ _ => trivial
      countable_union_mem := fun _ _ => trivial
    }
    le_top := fun _ _ _ => trivial
  }

instance ConcreteSigmaAlgebra.instOrderBot {X:Type*} : OrderBot (ConcreteSigmaAlgebra X) :=
  {
    bot := {
      measurable := fun E => E = ∅ ∨ E = Set.univ
      empty_mem := by grind
      compl_mem := fun E hE => by grind
      union_mem := fun E F hE hF => by grind
      countable_union_mem := fun E hE => by
        by_cases h : ∃ n, E n = Set.univ
        · obtain ⟨n, hn⟩ := h
          refine Or.inr ?_
          ext x
          simp
          exact ⟨n, by simp [hn]⟩
        · refine Or.inl ?_
          ext x
          simp
          intro n
          have hEn := hE n
          rcases hEn with h0 | h1
          · simp [h0]
          · exact (h ⟨n, h1⟩).elim
    }
    bot_le := fun B E hE => by
      rcases hE with h | h
      · simpa [h] using B.empty_mem
      · simpa [h, Set.compl_empty] using B.compl_mem ∅ B.empty_mem
  }

/-- Exercise 1.4.13 (Intersection of sigma-algebras) -/
instance ConcreteSigmaAlgebra.instInfSet {X:Type*} : InfSet (ConcreteSigmaAlgebra X) :=
  {
      sInf S :=
        {
          measurable := fun E => ∀ B ∈ S, B.measurable E
          empty_mem := fun B _ => B.empty_mem
          compl_mem := fun E hE B hB => B.compl_mem E (hE B hB)
          union_mem := fun E F hE hF B hB => B.union_mem E F (hE B hB) (hF B hB)
          countable_union_mem := fun E hE B hB => B.countable_union_mem E (fun n => hE n B hB)
        }
  }

def ConcreteSigmaAlgebra.generated_by {X:Type*} (F: Set (Set X)) : ConcreteSigmaAlgebra X :=
  sInf { B | ∀ E ∈ F, B.measurable E }

/-- Definition 1.4.14 (Generation of σ-algebras) -/
instance ConcreteSigmaAlgebra.instSupSet {X:Type*} : SupSet (ConcreteSigmaAlgebra X) :=
  {
      sSup S := ConcreteSigmaAlgebra.generated_by (⋃ B ∈ S, B.measurableSets)
  }

instance ConcreteSigmaAlgebra.instCompleteLattice {X:Type*} : CompleteLattice (ConcreteSigmaAlgebra X) :=
  {
    sup := sorry
    le_sup_left := sorry
    le_sup_right := sorry
    sup_le := sorry
    inf := sorry
    inf_le_left := sorry
    inf_le_right := sorry
    le_inf := sorry
    le_top := sorry
    bot_le := sorry
    isLUB_sSup := sorry
    isGLB_sInf := sorry
  }

theorem ConcreteSigmaAlgebra.generated_by_le {X:Type*} (F: Set (Set X)) : ConcreteBooleanAlgebra.generated_by F ≤ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra := by sorry

example : ∃ (X:Type*) (F: Set (Set X)), ConcreteBooleanAlgebra.generated_by F ≠ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra := by sorry

/-- Remark 1.4.15 -/
theorem ConcreteSigmaAlgebra.induction {X:Type*} {F: Set (Set X)} {P: Set X → Prop}
  (h1: P ∅) (h2: ∀ E ∈ F, P E) (h3: ∀ E, P E → P Eᶜ)
  (h4: ∀ (E : ℕ → Set X), (∀ n, P (E n)) → P (⋃ n, E n)) : ∀ E, (ConcreteSigmaAlgebra.generated_by F).measurable E → P E :=
  by sorry

/-- Definition 1.4.16 (Borel σ-algebra) -/
def BorelSigmaAlgebra (X:Type*) [TopologicalSpace X] : ConcreteSigmaAlgebra X :=
  ConcreteSigmaAlgebra.generated_by { U : Set X | IsOpen U }

/-- Exercise 1.4.14 (i) -/
theorem BorelSigmaAlgebra.generated_by_open (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { U : Set (EuclideanSpace' d) | IsOpen U } := rfl

/-- Exercise 1.4.14 (ii) -/
theorem BorelSigmaAlgebra.generated_by_closed (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { F : Set (EuclideanSpace' d) | IsClosed F } := by sorry

/-- Exercise 1.4.14 (iii) -/
theorem BorelSigmaAlgebra.generated_by_compact (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { K : Set (EuclideanSpace' d) | IsCompact K } := by sorry

/-- Exercise 1.4.14 (iv) -/
theorem BorelSigmaAlgebra.generated_by_open_balls (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { B : Set (EuclideanSpace' d) | ∃ x₀ r, B = Metric.ball x₀ r } := by sorry

/-- Exercise 1.4.14 (v) -/
theorem BorelSigmaAlgebra.generated_by_boxes (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by (Box.toSet '' Set.univ) := by sorry

/-- Exercise 1.4.14 (vi) -/
theorem BorelSigmaAlgebra.generated_by_elementary (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { E : Set (EuclideanSpace' d) | IsElementary E }  := by sorry

open Ordinal in
/-- Exercise 1.4.15 (Recursive definition of generated sigma-algebra). -/
def ConcreteSigmaAlgebra.generated_by_eq {X:Type*} (F: Set (Set X)) :
  (ConcreteSigmaAlgebra.generated_by F).measurableSets =
  ⋃ α < ω₁,
  Ordinal.limitRecOn (motive := fun _ ↦ Set (Set X)) α F (fun n G ↦ { E: Set X | (∃ S: Set G, Countable S ∧ E = ⋃ (H:S), H) ∨ (∃ S: Set G, Countable S ∧ E = (⋃ (H:S), H)ᶜ) }) (fun α _ G ↦ ⋃ (β : Ordinal) (h : β < α), G β h) := by sorry

open Cardinal in
/-- Exercise 1.4.16 -/
theorem ConcreteSigmaAlgebra.card_of_generated_by {X:Type*} {F: Set (Set X)} [Infinite F] :
  Cardinal.mk (ConcreteSigmaAlgebra.generated_by F).measurableSets ≤ (Cardinal.mk F) ^ ℵ₀ :=
  by sorry

open Cardinal in
theorem BorelSigmaAlgebra.card (d:ℕ) : Cardinal.mk (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSets ≤ 2 ^ ℵ₀ :=
  by sorry

theorem JordanMeasurable.not_borel {d:ℕ} (hd: d ≥ 1) : ∃ E: Set (EuclideanSpace' d), JordanMeasurable E ∧ ¬ (BorelSigmaAlgebra (EuclideanSpace' d)).measurable E :=
  by sorry

/-- Exercise 1.4.17 -/
theorem BorelSigmaAlgebra.prod {d₁ d₂:ℕ} {E : Set (EuclideanSpace' d₁)} {F : Set (EuclideanSpace' d₂)}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable E)
  (hF: (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable F) :
  (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable ((EuclideanSpace'.prod_equiv d₁ d₂).symm '' (E ×ˢ F))
  :=
  by sorry

/-- Exercise 1.4.18(i) (slice along first factor). -/
theorem BorelSigmaAlgebra.slice_fst {d₁ d₂:ℕ} {E : Set (EuclideanSpace' (d₁+d₂))}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' (d₁+d₂))).measurable E)
  (x₂ : EuclideanSpace' d₂ ) :
  (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable { x₁ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E }
  :=
  by sorry

/-- Exercise 1.4.18(i) (slice along second factor). -/
theorem BorelSigmaAlgebra.slice_snd {d₁ d₂:ℕ} {E : Set (EuclideanSpace' (d₁+d₂))}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' (d₁+d₂))).measurable E)
  (x₁ : EuclideanSpace' d₁ ) :
  (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable { x₂ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E }
  :=
  by sorry

/-- Exercise 1.4.18(ii) -/
example : ∃ (d₁ d₂ : ℕ) (E : Set (EuclideanSpace' (d₁+d₂))) (x₂ : EuclideanSpace' d₂),
  LebesgueMeasurable E ∧
  ¬ LebesgueMeasurable { x₁ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E } := by sorry

/-- Exercise 1.4.19 -/
theorem LebesgueMeasurable.sigmaAlgebra_generated_by {d:ℕ} :
  LebesgueMeasurable.sigmaAlgebra d = ConcreteSigmaAlgebra.generated_by ( (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSets ∪ (IsNull.sigmaAlgebra d).measurableSets) :=
  by sorry

def ConcreteSigmaAlgebra.measurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X := {
  MeasurableSet' := B.measurable
  measurableSet_empty := B.empty_mem
  measurableSet_compl := B.compl_mem
  measurableSet_iUnion := B.countable_union_mem
}

def MeasurableSpace.sigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X := {
  measurable := M.MeasurableSet'
  empty_mem := M.measurableSet_empty
  compl_mem := M.measurableSet_compl
  union_mem := fun E F hE hF => by
    have hunion : E ∪ F = ⋃ n, if n = 0 then E else F := by
      ext x
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro (hx | hx)
        · exact ⟨0, by simp [hx]⟩
        · exact ⟨1, by simp [hx]⟩
      · rintro ⟨n, hx⟩
        by_cases hn : n = 0
        · exact Or.inl (by simpa [hn] using hx)
        · exact Or.inr (by simpa [hn] using hx)
    rw [hunion]
    exact M.measurableSet_iUnion _ (fun n => by
      by_cases hn : n = 0
      · simpa [hn] using hE
      · simpa [hn] using hF)
  countable_union_mem := M.measurableSet_iUnion
}

theorem BorelSigmaAlgebra.le_LebesgueSigmaAlgebra (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) ≤ LebesgueMeasurable.sigmaAlgebra d := by sorry
