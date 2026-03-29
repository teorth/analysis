import Analysis.MeasureTheory.Section_1_4_2

/-!
# Introduction to Measure Theory, Section 1.4.3: Countably additive measures and measure spaces

A companion to (the introduction to) Section 1.4.3 of the book "An introduction to Measure Theory".

Note: initially this section will use custom-notions of concrete sigma algebras and countably additive measures, but will transition to the Mathlib notions of {name}`Measurable` and {name}`MeasureTheory.Measure`, which will be in use going forward. In particular, exercises past this point will be easier
to solve using the Mathlib library for measure theory than the custom results defined here.
-/

/-- Definition 1.4.19 (Finitely additive measure) -/
class FinitelyAdditiveMeasure {X:Type*} (B: ConcreteBooleanAlgebra X) where
  measure : Set X → EReal
  measure_pos : ∀ A : Set X, B.measurable A → 0 ≤ measure A
  measure_empty : measure ∅ = 0
  measure_finite_additive : ∀ E F : Set X, B.measurable E → B.measurable F → Disjoint E F →
    measure (E ∪ F) = measure E + measure F

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.lebesgue (d:ℕ) : FinitelyAdditiveMeasure (LebesgueMeasurable.boolean_algebra d) :=
  {
    measure A := Lebesgue_measure A
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.21 -/
def FinitelyAdditiveMeasure.restrict_alg {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {B':ConcreteBooleanAlgebra X} (hBB': B' ≤ B) : FinitelyAdditiveMeasure B' :=
  {
    measure := μ.measure
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.jordan (d:ℕ) : FinitelyAdditiveMeasure (JordanMeasurable.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (LebesgueMeasurable.gt_jordan_boolean_algebra d)

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.null (d:ℕ) : FinitelyAdditiveMeasure (IsNull.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (IsNull.lt_lebesgue_boolean_algebra d)

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.elem (d:ℕ) : FinitelyAdditiveMeasure (EuclideanSpace'.elementary_boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (by sorry)

open Classical in
/-- Example 1.4.22 (Dirac measure) -/
noncomputable def FinitelyAdditiveMeasure.dirac {X:Type*} (x₀:X) (B: ConcreteBooleanAlgebra X) : FinitelyAdditiveMeasure B :=
  {
    measure := fun A => if x₀ ∈ A then 1 else 0
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.23 (Zero measure) -/
instance FinitelyAdditiveMeasure.instZero {X:Type*} (B: ConcreteBooleanAlgebra X) : Zero (FinitelyAdditiveMeasure B) :=
  {
    zero := {
      measure := fun A => 0
      measure_pos := by sorry
      measure_empty := by sorry
      measure_finite_additive := by sorry
    }
  }

/-- Example 1.4.24 (linear combinations of measures) -/
instance FinitelyAdditiveMeasure.instAdd {X:Type*} {B: ConcreteBooleanAlgebra X} : Add (FinitelyAdditiveMeasure B) :=
  {
    add := fun μ ν =>
      {
        measure := fun A => μ.measure A + ν.measure A
        measure_pos := by sorry
        measure_empty := by sorry
        measure_finite_additive := by sorry
      }
  }

noncomputable instance FinitelyAdditiveMeasure.instSmul {X:Type*} {B: ConcreteBooleanAlgebra X} : SMul ENNReal (FinitelyAdditiveMeasure B) :=
{
    smul := fun c μ =>
        {
        measure := fun A => c * μ.measure A
        measure_pos := by sorry
        measure_empty := by sorry
        measure_finite_additive := by sorry
        }
}

instance FinitelyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteBooleanAlgebra X} : AddCommMonoid (FinitelyAdditiveMeasure B) :=
{
  add_assoc := by sorry,
  zero_add := by sorry,
  add_zero := by sorry,
  add_comm := by sorry
  nsmul := nsmulRec
}

noncomputable instance FinitelyAdditiveMeasure.instDistribMulAction {X:Type*} {B: ConcreteBooleanAlgebra X} : DistribMulAction ENNReal (FinitelyAdditiveMeasure B) :=
{
  smul_zero := by sorry,
  smul_add := by sorry,
  one_smul := by sorry,
  mul_smul := by sorry
}

/-- Example 1.4.25 (Restriction of a measure) -/
def FinitelyAdditiveMeasure.restrict {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (A:Set X) (hA:B.measurable A) : FinitelyAdditiveMeasure (B.restrict A) :=
  {
    measure := fun E => μ.measure E
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.26 (Counting a measure) -/
noncomputable def FinitelyAdditiveMeasure.counting (X:Type*) : FinitelyAdditiveMeasure (⊤  : ConcreteBooleanAlgebra X) :=
  {
    measure := fun E => ENat.card E
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Exercise 1.4.20(i) -/
theorem FinitelyAdditiveMeasure.mono {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {E F : Set X} (hE : B.measurable E) (hF : B.measurable F) (hsub : E ⊆ F) : μ.measure E ≤ μ.measure F :=
by sorry

/-- Exercise 1.4.20(ii) -/
theorem FinitelyAdditiveMeasure.finite_additivity {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {J:Type*} {I: Finset J} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) (hdisj: Set.univ.PairwiseDisjoint E) :
  μ.measure (⋃ j ∈ I, E j) = ∑ j ∈ I, μ.measure (E j) := by sorry

/-- Exercise 1.4.20(iii) -/
theorem FinitelyAdditiveMeasure.finite_subadditivity {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {J:Type*} {I: Finset J} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) :
  μ.measure (⋃ j ∈ I, E j) ≤ ∑ j ∈ I, μ.measure (E j) := by sorry

/-- Exercise 1.4.20(iv) -/
theorem FinitelyAdditiveMeasure.mes_union_add_mes_inter {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (E F : Set X) :
  μ.measure (E ∪ F) + μ.measure (E ∩ F) = μ.measure E + μ.measure F := by sorry

open Classical in
/-- Exercise 1.4.21 -/
theorem FinitelyAdditiveMeasure.finite_atomic_eq {I X: Type*} [Fintype I] {atoms: I → Set X} (h_part: IsPartition atoms) (μ : FinitelyAdditiveMeasure h_part.to_ConcreteBooleanAlgebra) : ∃! c : I → ENNReal, ∀ E, h_part.to_ConcreteBooleanAlgebra.measurable E → μ.measure E = ∑ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), c i := by sorry

/-- Definition 1.4.27 (Countably additive measure) -/
class CountablyAdditiveMeasure {X:Type*} (B: ConcreteSigmaAlgebra X) extends FinitelyAdditiveMeasure B.toConcreteBooleanAlgebra where
  measure_countable_additive : ∀ (E : ℕ → Set X), (∀ n, B.measurable (E n)) → Set.univ.PairwiseDisjoint E →
    measure (⋃ n, E n) = ∑' n, (measure (E n))

def FinitelyAdditiveMeasure.isCountablyAdditive {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) : Prop :=
  B.isSigmaAlgebra ∧ ∀ (E : ℕ → Set X), (∀ n, B.measurable (E n)) → Set.univ.PairwiseDisjoint E →
    μ.measure (⋃ n, E n) = ∑' n, (μ.measure (E n))

def FinitelyAdditiveMeasure.isCountablyAdditive.toCountablyAdditive {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (h: μ.isCountablyAdditive) : CountablyAdditiveMeasure h.1.toSigmaAlgebra :=
  {
    measure := μ.measure
    measure_pos := μ.measure_pos
    measure_empty := μ.measure_empty
    measure_finite_additive := μ.measure_finite_additive
    measure_countable_additive := h.2
  }

/-- Example 1.4.28-/
theorem FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive (d:ℕ) : (FinitelyAdditiveMeasure.lebesgue d).isCountablyAdditive :=
  by sorry

theorem FinitelyAdditiveMeasure.isCountablyAdditive_restrict_alg {X:Type*} {B B': ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (hBB': B' ≤ B) : (μ.toFinitelyAdditiveMeasure.restrict_alg hBB').isCountablyAdditive :=
  by sorry

def CountablyAdditiveMeasure.restrict_alg {X:Type*} {B B': ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (hBB' : B' ≤ B) : CountablyAdditiveMeasure B' :=
  {
    toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure.restrict_alg hBB',
    measure_countable_additive := by sorry
  }

/-- Example 1.4.29-/
theorem FinitelyAdditiveMeasure.dirac_isCountablyAdditive {X:Type*} (x₀:X) (B: ConcreteBooleanAlgebra X) : (FinitelyAdditiveMeasure.dirac x₀ B).isCountablyAdditive :=
  by sorry

/-- Example 1.4.29-/
theorem FinitelyAdditiveMeasure.counting_isCountablyAdditive {X:Type*} : (FinitelyAdditiveMeasure.counting X).isCountablyAdditive :=
  by sorry

/-- Example 1.4.30 -/
def CountablyAdditiveMeasure.restrict {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (A:Set X) (hA:B.measurable A) : CountablyAdditiveMeasure (B.restrict A) :=
  {
    toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure.restrict A hA,
    measure_countable_additive := by sorry
  }

instance CountablyAdditiveMeasure.instZero {X:Type*} (B: ConcreteSigmaAlgebra X) : Zero (CountablyAdditiveMeasure B) :=
  {
    zero := {
      toFinitelyAdditiveMeasure := 0
      measure_countable_additive := by sorry
    }
  }

instance CountablyAdditiveMeasure.instAdd {X:Type*} {B: ConcreteSigmaAlgebra X} : Add (CountablyAdditiveMeasure B) :=
  {
    add := fun μ ν =>
      {
        toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure + ν.toFinitelyAdditiveMeasure
        measure_countable_additive := by sorry
      }
  }

instance CountablyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteSigmaAlgebra X} : AddCommMonoid (CountablyAdditiveMeasure B) :=
{
  add_assoc := by sorry,
  zero_add := by sorry,
  add_zero := by sorry,
  add_comm := by sorry
  nsmul := nsmulRec
}

/-- Exercise 1.4.22(i) -/
noncomputable instance CountablyAdditiveMeasure.instSmul {X:Type*} {B: ConcreteSigmaAlgebra X} : SMul ENNReal (CountablyAdditiveMeasure B) :=
{
    smul := fun c μ =>
        {
        toFinitelyAdditiveMeasure := c • μ.toFinitelyAdditiveMeasure
        measure_countable_additive := by sorry
        }
}

noncomputable instance CountablyAdditiveMeasure.instDistribMulAction {X:Type*} {B: ConcreteSigmaAlgebra X} : DistribMulAction ENNReal (CountablyAdditiveMeasure B) :=
{
  smul_zero := by sorry,
  smul_add := by sorry,
  one_smul := by sorry,
  mul_smul := by sorry
}

/-- Exercise 1.4.22(ii) -/
noncomputable def CountablyAdditiveMeasure.sum {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: ℕ → CountablyAdditiveMeasure B) : CountablyAdditiveMeasure B :=
  {
    toFinitelyAdditiveMeasure := {
      measure := fun A => ∑' n, (μ n).toFinitelyAdditiveMeasure.measure A
      measure_pos := by sorry
      measure_empty := by sorry
      measure_finite_additive := by sorry
    }
    measure_countable_additive := by sorry
  }

open MeasureTheory

noncomputable def CountablyAdditiveMeasure.toMeasure {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) :
  @Measure X B.measurableSpace :=
  let _measurable := B.measurableSpace
  {
      measureOf E := (μ.measure E).toENNReal
      empty := by sorry
      mono := by sorry
      iUnion_nat := by sorry
      m_iUnion := by sorry
      trim_le := by sorry
  }

noncomputable def FinitelyAdditiveMeasure.isCountablyAdditive.toMeasure {X:Type*} {B: ConcreteBooleanAlgebra X} {μ: FinitelyAdditiveMeasure B} (h: μ.isCountablyAdditive) :
  @Measure X h.1.toSigmaAlgebra.measurableSpace := h.toCountablyAdditive.toMeasure

def Measure.toCountablyAdditiveMeasure {X:Type*} [M : MeasurableSpace X] (μ: Measure X) : CountablyAdditiveMeasure M.sigmaAlgebra :=
  {
    toFinitelyAdditiveMeasure := {
      measure E := μ.measureOf E
      measure_pos := by sorry
      measure_empty := by sorry
      measure_finite_additive := by sorry
    }
    measure_countable_additive := by sorry
  }

/-- Exercise 1.4.23(i) -/
theorem Measure.countable_subadditivity {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n)) :
  μ.measureOf (⋃ n, E n) ≤ ∑' n, μ.measureOf (E n) := by sorry

/-- Exercise 1.4.23(ii) -/
theorem Measure.upwards_mono {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  (hmono : Monotone E) : μ (⋃ n, E n) = ⨆ n, μ.measureOf (E n) := by sorry

/-- Exercise 1.4.23(iii) -/
theorem Measure.downwards_mono {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  (hmono : Antitone E) (hfin : ∃ n, μ (E n) < ⊤) : μ (⋂ n, E n) = ⨅ n, μ.measureOf (E n) := by sorry

theorem Measure.downwards_mono_counter : ∃ (X:Type) (M: MeasurableSpace X) (μ: Measure X) (E : ℕ → Set X) (hE: ∀ n, Measurable (E n))
  (hmono : Antitone E), μ (⋂ n, E n) ≠ ⨅ n, μ.measureOf (E n) := by sorry

/-- Exercise 1.4.24 (i) (Dominated convergence for sets) -/
theorem Measure.measurable_of_lim {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  {E' : Set X} (hlim : PointwiseConvergesTo E E') : Measurable E := by sorry

/-- Exercise 1.4.24 (ii) (Dominated convergence for sets) -/
theorem Measure.measure_of_lim {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  {E' F : Set X} (hlim : PointwiseConvergesTo E E') (hF : Measurable F) (hfin : μ F < ⊤) (hcon : ∀ n, E n ⊆ F) :
  Filter.atTop.Tendsto (fun n ↦ μ (E n)) (nhds (μ E')) := by sorry

/-- Exercise 1.4.24 (iii) (Dominated convergence for sets) -/
theorem Measure.measure_of_lim_counter : ∃ (X:Type) (M:MeasurableSpace X) (μ: Measure X) (E : ℕ → Set X) (hE: ∀ n, Measurable (E n))
  (E' F : Set X) (hlim : PointwiseConvergesTo E E') (hF : Measurable F) (hcon : ∀ n, E n ⊆ F),
  ¬ Filter.atTop.Tendsto (fun n ↦ μ (E n)) (nhds (μ E')) := by sorry

/-- Exercise 1.4.25 -/
theorem Measure.on_countable {X:Type*} [Countable X] [M: MeasurableSpace X] (hM: M = ⊤) (μ: Measure X) :
  ∃! c : X → ENNReal, ∀ E : Set X, μ E = ∑' x : E, c x := by sorry

-- Definition 1.4.31
#check Measure.IsComplete

#check NullMeasurableSpace

#check Measure.completion

/-- Exercise 1.4.26 (Completion) -/
theorem Measure.completion_lt {X:Type*} [M : MeasurableSpace X] (μ: Measure X) (M' : MeasurableSpace X) (μ' : @Measure X M')
  (hMM' : M ≤ M') (hμ : ∀ E, M.MeasurableSet' E → μ E = μ' E) : ∀ E : Set X, @NullMeasurableSet X M E μ → (M'.MeasurableSet' E ∧ μ' E = μ.completion E)
   := by sorry

noncomputable def EuclideanSpace'.lebesgueMeasure (d:ℕ) := (FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toMeasure

noncomputable def EuclideanSpace'.borelMeasure (d:ℕ) := ((FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toCountablyAdditive.restrict_alg (BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d)).toMeasure

def Measure.equiv {X:Type*} {M M' : MeasurableSpace X} (μ: @Measure X M) (μ': @Measure X M') : Prop := M = M' ∧ ∀ E, M.MeasurableSet' E → μ E = μ' E

/-- Exercise 1.4.27 -/
theorem EuclideanSpace'.borel_completion_eq_lebesgue {d:ℕ} :
  Measure.equiv (EuclideanSpace'.borelMeasure d).completion (EuclideanSpace'.lebesgueMeasure d) := by sorry

/-- Exercise 1.4.28(i) (Approximation by an algebra) -/
theorem BooleanAlgebra.approx_finite {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace) (hfin: μ Set.univ < ⊤) : ∀ (ε : ℝ) (hε: ε>0) (E : Set X) (hE: (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E),
  ∃ F : Set X, B.measurable F ∧ μ (symmDiff E F) < ENNReal.ofReal ε := by sorry

/-- Exercise 1.4.28(ii) (Approximation by an algebra) -/
theorem BooleanAlgebra.approx_sigma_finite {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace) (hσfin: ∃ A : ℕ → Set X, (∀ n, B.measurable (A n) ∧ μ (A n) < ⊤) ∧ ⋃ n, A n = ⊤) : ∀ (ε : ℝ) (hε: ε>0) (E : Set X) (hE: (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E),
  ∃ F : Set X, B.measurable F ∧ μ (symmDiff E F) < ENNReal.ofReal ε := by sorry
