import Analysis.MeasureTheory.Section_1_3_1
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Introduction to Measure Theory, Section 1.3.2: Measurable functions

A companion to (the introduction to) Section 1.3.2 of the book "An introduction to Measure Theory".

-/

def Unsigned {X Y:Type*} [LE Y] [Zero Y] (f:X → Y) : Prop := ∀ x, f x ≥ 0

def PointwiseConvergesTo {X Y:Type*} [TopologicalSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop := ∀ x, Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (g x))

/-- Definiiton 1.3.8 (Unsigned measurable function) -/
def UnsignedMeasurable {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := Unsigned f ∧ ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseConvergesTo g f)

def EReal.BoundedFunction {X:Type*} (f:X → EReal) : Prop := ∃ M:NNReal, ∀ x, (f x).abs ≤ M

def FiniteMeasureSupport {d:ℕ} {Y:Type*} [Zero Y] (f: EuclideanSpace' d → Y) : Prop := Lebesgue_measure (Support f) < ⊤

def PointwiseAeConvergesTo {d:ℕ} {Y:Type*} [TopologicalSpace Y] (f: ℕ → (EuclideanSpace' d → Y)) (g: EuclideanSpace' d → Y) : Prop := AlmostAlways (fun x ↦ Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (g x)))

/-!
## Helper lemmas for Lemma 1.3.9

The proof follows the book's implication chain. We establish explicit edges and
let `tfae_finish` compute the transitive closure.

**Explicit edges declared:**
- (i) ⟺ (ii): by definition of UnsignedMeasurable
- (ii) ⟹ (iii): pointwise everywhere implies pointwise a.e.
- (iv) ⟹ (ii): monotone sequences in [0,∞] converge to their supremum
- (iii) ⟹ (v): via limsup representation (main technical work)
- (v) ⟺ (vi): countable unions/intersections
- (vi) ⟺ (vii): complementation
- (v) ⟺ (viii): complementation
- (v)-(viii) ⟹ (ix): intervals are intersections of half-intervals
- (ix) ⟹ (x): open sets are countable unions of intervals
- (x) ⟺ (xi): complementation
- (x) ⟹ (vii): {f < λ} = f⁻¹'(Iio λ) and Iio λ is open
- (v)-(xi) ⟹ (iv): construction of approximating sequence

**Derived transitively (by tfae_finish):**
- (ix) ⟹ (v) or (vi): via (ix) → (x) → (vii) → (vi) → (v)
- (x) ⟹ (v)-(ix): via (x) → (vii) → (vi) → (v) → (viii)/(ix)
-/

namespace UnsignedMeasurable.TFAE_helpers

variable {d : ℕ} {f : EuclideanSpace' d → EReal}

-- Statement abbreviations for clarity (using indices as in the book)
private abbrev stmt_i (f : EuclideanSpace' d → EReal) := UnsignedMeasurable f
private abbrev stmt_ii (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (∀ x, Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x)))
private abbrev stmt_iii (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f)
private abbrev stmt_iv (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n) ∧ EReal.BoundedFunction (g n) ∧ FiniteMeasureSupport (g n)) ∧ (∀ x, Monotone (fun n ↦ g n x)) ∧ (∀ x, f x = iSup (fun n ↦ g n x))
private abbrev stmt_v (f : EuclideanSpace' d → EReal) := ∀ t, LebesgueMeasurable {x | f x > t}
private abbrev stmt_vi (f : EuclideanSpace' d → EReal) := ∀ t, LebesgueMeasurable {x | f x ≥ t}
private abbrev stmt_vii (f : EuclideanSpace' d → EReal) := ∀ t, LebesgueMeasurable {x | f x < t}
private abbrev stmt_viii (f : EuclideanSpace' d → EReal) := ∀ t, LebesgueMeasurable {x | f x ≤ t}
private abbrev stmt_ix (f : EuclideanSpace' d → EReal) := ∀ I:BoundedInterval, LebesgueMeasurable (f⁻¹' (Real.toEReal '' I.toSet))
private abbrev stmt_x (f : EuclideanSpace' d → EReal) := ∀ U: Set EReal, IsOpen U → LebesgueMeasurable (f⁻¹' U)
private abbrev stmt_xi (f : EuclideanSpace' d → EReal) := ∀ K: Set EReal, IsClosed K → LebesgueMeasurable (f⁻¹' K)

/-! ### (i) ⟺ (ii): By definition of UnsignedMeasurable -/

private lemma i_iff_ii (hf : Unsigned f) : stmt_i f ↔ stmt_ii f := by
  simp only [UnsignedMeasurable]
  constructor
  · intro ⟨_, g, hg_simple, hg_conv⟩
    exact ⟨g, hg_simple, hg_conv⟩
  · intro ⟨g, hg_simple, hg_conv⟩
    exact ⟨hf, g, hg_simple, hg_conv⟩

/-! ### (ii) ⟹ (iii): Pointwise everywhere implies pointwise a.e. -/

private lemma ii_imp_iii : stmt_ii f → stmt_iii f := by
  intro ⟨g, hg_simple, hg_conv⟩
  refine ⟨g, hg_simple, ?_⟩
  -- AlmostAlways P means IsNull {x | ¬P x}
  -- Since pointwise convergence holds everywhere, {x | ¬Tendsto} = ∅
  simp only [PointwiseAeConvergesTo, AlmostAlways]
  have h_empty : {x | ¬Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hg_conv x
  rw [h_empty]
  exact Lebesgue_outer_measure.of_empty d

/-! ### (iv) ⟹ (ii): Monotone sequences in [0,∞] converge to their supremum -/

private lemma iv_imp_ii : stmt_iv f → stmt_ii f := by
  intro ⟨g, hg_props, hg_mono, hg_sup⟩
  refine ⟨g, fun n => (hg_props n).1, ?_⟩
  intro x
  rw [hg_sup x]
  -- For monotone sequences in EReal, g n x → iSup (g · x)
  exact tendsto_atTop_iSup (hg_mono x)

/-! ### (iii) ⟹ (v): Via limsup representation -/

-- Helper: Set.indicator' equals 1 when x ∈ E
private lemma Set.indicator'_eq_one' {X : Type*} {E : Set X} {x : X} (hx : x ∈ E) :
    ((E.indicator' x : ℝ) : EReal) = 1 := by
  classical
  rw [Set.indicator'_apply, if_pos hx]
  rfl

-- Helper: Set.indicator' equals 0 when x ∉ E
private lemma Set.indicator'_eq_zero' {X : Type*} {E : Set X} {x : X} (hx : x ∉ E) :
    ((E.indicator' x : ℝ) : EReal) = 0 := by
  classical
  rw [Set.indicator'_apply, if_neg hx]
  rfl

-- Level sets of simple functions are Lebesgue measurable
private lemma UnsignedSimpleFunction.levelset_gt_LebesgueMeasurable
    {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g) (t : EReal) :
    LebesgueMeasurable {x | g x > t} := by
  obtain ⟨k, c, E, hE_props, heq⟩ := hg
  -- For each subset S of Fin k, define the "atom" R_S where x ∈ E_i iff i ∈ S
  let R : Finset (Fin k) → Set (EuclideanSpace' d) :=
    fun S => (⋂ i ∈ S, E i) ∩ (⋂ i ∈ Sᶜ, (E i)ᶜ)
  -- Each R_S is measurable
  have hR_meas : ∀ S, LebesgueMeasurable (R S) := by
    intro S
    apply LebesgueMeasurable.inter
    · apply LebesgueMeasurable.finset_inter; intro i _; exact (hE_props i).1
    · apply LebesgueMeasurable.finset_inter; intro i _; exact (hE_props i).1.complement
  -- On R_S, g is constant with value ∑_{i ∈ S} c_i
  have hg_const : ∀ S x, x ∈ R S → g x = ∑ i ∈ S, c i := by
    intro S x hx
    rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply]
    have h_split : ∑ i : Fin k, c i • EReal.indicator (E i) x =
                   ∑ i ∈ S, c i • EReal.indicator (E i) x +
                   ∑ i ∈ Sᶜ, c i • EReal.indicator (E i) x := by
      rw [← Finset.sum_add_sum_compl S]
    rw [h_split]
    simp only [R, Set.mem_inter_iff, Set.mem_iInter] at hx
    obtain ⟨hx_in, hx_out⟩ := hx
    have h_in : ∀ i ∈ S, EReal.indicator (E i) x = 1 := by
      intro i hi; have hxi : x ∈ E i := hx_in i hi
      simp only [EReal.indicator, Real.EReal_fun]; exact Set.indicator'_eq_one' hxi
    have h_out : ∀ i ∈ Sᶜ, EReal.indicator (E i) x = 0 := by
      intro i hi; have hxi : x ∉ E i := hx_out i hi
      simp only [EReal.indicator, Real.EReal_fun]; exact Set.indicator'_eq_zero' hxi
    calc ∑ i ∈ S, c i • EReal.indicator (E i) x + ∑ i ∈ Sᶜ, c i • EReal.indicator (E i) x
        = ∑ i ∈ S, c i • (1 : EReal) + ∑ i ∈ Sᶜ, c i • (0 : EReal) := by
          congr 1
          · exact Finset.sum_congr rfl (fun i hi => by rw [h_in i hi])
          · exact Finset.sum_congr rfl (fun i hi => by rw [h_out i hi])
      _ = ∑ i ∈ S, c i + 0 := by simp [smul_eq_mul]
      _ = ∑ i ∈ S, c i := add_zero _
  -- Every x belongs to exactly one R_S
  have h_partition : ∀ x, ∃! S, x ∈ R S := by
    intro x
    have hDec : DecidablePred (fun i => x ∈ E i) := Classical.decPred _
    let S := (Finset.univ : Finset (Fin k)).filter (fun i => x ∈ E i)
    use S
    constructor
    · simp only [R, Set.mem_inter_iff, Set.mem_iInter, S]
      constructor
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; exact hi
      · intro i hi; simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hi; exact hi
    · intro T hT
      ext i
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [R, Set.mem_inter_iff, Set.mem_iInter] at hT
      obtain ⟨hT_in, hT_out⟩ := hT
      constructor
      · intro hi; exact hT_in i hi
      · intro hxi; by_contra hni
        have hni' : i ∈ Tᶜ := Finset.mem_compl.mpr hni
        exact hT_out i hni' hxi
  -- {g > t} = ⋃_{S : ∑_{i ∈ S} c_i > t} R_S
  have h_eq : {x | g x > t} = ⋃ S ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun S => ∑ i ∈ S, c i > t), R S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hgx
      obtain ⟨S, hxS, _⟩ := h_partition x
      refine ⟨S, ?_, hxS⟩; rw [hg_const S x hxS] at hgx; exact hgx
    · intro ⟨S, hS_gt, hxS⟩; rw [hg_const S x hxS]; exact hS_gt
  rw [h_eq]
  apply LebesgueMeasurable.finset_union; intro S _; exact hR_meas S

-- The limsup set for (iii) ⟹ (v)
private def limsupSet (g : ℕ → EuclideanSpace' d → EReal) (t : EReal) : Set (EuclideanSpace' d) :=
  ⋃ (M : ℕ), ⋂ (N : ℕ), ⋃ n ∈ {n | n ≥ N}, {x | g n x > t + 1 / (M + 1)}

-- The limsup set is Lebesgue measurable when each g_n is a simple function
private lemma limsupSet_LebesgueMeasurable {g : ℕ → EuclideanSpace' d → EReal}
    (hg : ∀ n, UnsignedSimpleFunction (g n)) (t : EReal) :
    LebesgueMeasurable (limsupSet g t) := by
  apply LebesgueMeasurable.countable_union
  intro M
  apply LebesgueMeasurable.countable_inter
  intro N
  apply LebesgueMeasurable.countable_union
  intro n
  by_cases hn : n ≥ N
  · convert UnsignedSimpleFunction.levelset_gt_LebesgueMeasurable (hg n) (t + 1 / (M + 1))
    ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, and_iff_right_iff_imp]; intro _; exact hn
  · convert LebesgueMeasurable.empty
    ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro h; exact absurd h hn

-- This is the main technical work of the proof
private lemma iii_imp_v : stmt_iii f → stmt_v f := by
  intro ⟨g, hg_simple, hg_ae_conv⟩ t
  -- The null set where convergence fails
  let N := {x | ¬Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))}
  have hN_null : IsNull N := hg_ae_conv
  -- The limsup set E
  let E := limsupSet g t
  have hE_meas : LebesgueMeasurable E := limsupSet_LebesgueMeasurable hg_simple t
  -- Show {f > t} ∩ Nᶜ = E ∩ Nᶜ (they agree where convergence holds)
  -- The key insight: f(x) = lim g_n(x) = lim sup g_n(x) a.e.
  -- So {f > λ} = ⋃_{M≥1} ⋂_{N≥1} ⋃_{n≥N} {g_n > λ + 1/M} outside a null set
  have h_ae_eq : {x | f x > t} ∩ Nᶜ = E ∩ Nᶜ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, N]
    push_neg
    constructor
    · -- f x > t ∧ converges → x ∈ E ∧ converges
      intro ⟨hfx, hconv⟩
      refine ⟨?_, hconv⟩
      -- Since f(x) > t and g_n(x) → f(x), we can find M such that f(x) > t + 1/M
      -- Then eventually g_n(x) > t + 1/M, which means x ∈ limsupSet
      simp only [E, limsupSet, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
      -- The detailed analysis argument uses Filter.Tendsto properties
      -- For a limit f(x), if f(x) > t, then ∃ε>0 with f(x) > t+ε
      -- Choose M with 1/M < ε, then eventually g_n(x) > t + 1/M

      -- Case 1: t = ⊥
      rcases eq_bot_or_bot_lt t with rfl | ht_ne_bot
      · -- t = ⊥: threshold = ⊥ + eps = ⊥ for any M, and g n x > ⊥ since g n x ≥ 0
        use 0
        intro N
        use N, le_refl N
        simp only [EReal.bot_add, gt_iff_lt]
        -- g N x ≥ 0 > ⊥
        have hg_nonneg : g N x ≥ 0 := by
          obtain ⟨k, c, E, hE_props, heq⟩ := hg_simple N
          rw [heq]
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          apply Finset.sum_nonneg
          intro i _
          apply mul_nonneg (hE_props i).2
          simp only [EReal.indicator, Real.EReal_fun]
          exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
        calc (⊥ : EReal) < 0 := EReal.bot_lt_zero
             _ ≤ g N x := hg_nonneg
      -- Case 2: f x = ⊤
      rcases eq_top_or_lt_top (f x) with hfx_top | hfx_lt_top
      · -- f x = ⊤: g_n → ⊤, so eventually g_n x > any threshold
        use 0
        intro N
        -- Since f x = ⊤ and f x > t, we have t < ⊤
        have ht_lt_top' : t < ⊤ := lt_of_lt_of_eq hfx hfx_top
        -- Therefore t + 1 < ⊤ (since 1 is finite)
        have h_t1_lt_top : t + 1 < ⊤ := EReal.add_lt_top (ne_top_of_lt ht_lt_top') (EReal.coe_ne_top 1)
        -- Show g n x > t + 1 for some n ≥ N using that g n → ⊤
        rw [hfx_top] at hconv
        -- Set.Ioi (t + 1) is a neighborhood of ⊤
        have h_mem : Set.Ioi (t + 1) ∈ nhds (⊤ : EReal) := Ioi_mem_nhds h_t1_lt_top
        have h_event : ∀ᶠ n in Filter.atTop, g n x ∈ Set.Ioi (t + 1) := hconv h_mem
        rw [Filter.eventually_atTop] at h_event
        obtain ⟨N₀, hN₀⟩ := h_event
        use max N₀ N, le_max_right _ _
        have h_n_mem := hN₀ (max N₀ N) (le_max_left _ _)
        simp only [Set.mem_Ioi, Nat.cast_zero, zero_add, gt_iff_lt] at h_n_mem ⊢
        calc t + 1 / 1 = t + 1 := by rw [div_one]
             _ < g (max N₀ N) x := h_n_mem
      -- Case 3: t < ⊤ and f x < ⊤, both are finite or f x > t means t < f x < ⊤
      rcases eq_top_or_lt_top t with rfl | ht_lt_top
      · -- t = ⊤: but hfx says f x > ⊤, impossible
        exfalso; exact (not_lt.mpr le_top) hfx
      -- Now ⊥ < t < ⊤ and f x > t, with f x < ⊤
      -- f x is finite since f x < ⊤ and f x > t > ⊥
      have hfx_ne_top : f x ≠ ⊤ := ne_top_of_lt hfx_lt_top
      have hfx_ne_bot : f x ≠ ⊥ := by
        intro h_eq_bot
        rw [h_eq_bot] at hfx
        exact not_lt_bot hfx
      have ht_ne_top : t ≠ ⊤ := ne_top_of_lt ht_lt_top
      have ht_ne_bot' : t ≠ ⊥ := ne_of_gt ht_ne_bot
      -- Extract real numbers
      obtain ⟨f', hf'⟩ : ∃ f' : ℝ, (f' : EReal) = f x := ⟨(f x).toReal, EReal.coe_toReal hfx_ne_top hfx_ne_bot⟩
      obtain ⟨t', ht'⟩ : ∃ t' : ℝ, (t' : EReal) = t := ⟨t.toReal, EReal.coe_toReal ht_ne_top ht_ne_bot'⟩
      -- Both f' and t' are real numbers with f' > t'
      have hf't' : f' > t' := by
        rw [← hf', ← ht'] at hfx
        exact EReal.coe_lt_coe_iff.mp hfx
      have hgap_pos : f' - t' > 0 := sub_pos.mpr hf't'
      -- Find M such that 1/(M+1) < f' - t'
      obtain ⟨M, hM⟩ := exists_nat_gt (1 / (f' - t'))
      use M
      intro N
      -- Show t' + 1/(M+1) < f'
      have h_lt : (t' : EReal) + 1 / ((M : EReal) + 1) < f' := by
        have hM1_pos : (M : ℝ) + 1 > 0 := by positivity
        have h1 : (1 : ℝ) / (M + 1) < f' - t' := by
          calc (1 : ℝ) / (M + 1) < 1 / (1 / (f' - t')) := by
                 apply div_lt_div_of_pos_left
                 · norm_num
                 · rw [one_div_pos]; exact hgap_pos
                 · calc 1 / (f' - t') < M := hM
                        _ < M + 1 := by exact_mod_cast Nat.lt_succ_self M
               _ = f' - t' := one_div_one_div (f' - t')
        have h2 : t' + 1 / (M + 1) < f' := by linarith
        -- Coerce to EReal
        have h_coe : ((t' : EReal) + 1 / ((M : EReal) + 1)) = ((t' + 1 / (M + 1) : ℝ) : EReal) := by
          rw [EReal.coe_add, EReal.coe_div]
          simp only [EReal.coe_one, EReal.coe_add, EReal.coe_natCast]
        rw [h_coe]
        exact EReal.coe_lt_coe_iff.mpr h2

      -- By convergence, eventually g_n(x) > t' + 1/(M+1)
      have h_event : ∀ᶠ n in Filter.atTop, g n x > (t' : EReal) + 1 / ((M : EReal) + 1) := by
        have h_mem : Set.Ioi ((t' : EReal) + 1 / ((M : EReal) + 1)) ∈ nhds (f x) := by
          rw [← hf']
          exact Ioi_mem_nhds h_lt
        exact hconv h_mem
      rw [Filter.eventually_atTop] at h_event
      obtain ⟨N₀, hN₀⟩ := h_event
      refine ⟨max N₀ N, le_max_right _ _, ?_⟩
      rw [← ht']
      exact hN₀ _ (le_max_left _ _)
    · -- x ∈ E ∧ converges → f x > t ∧ converges
      intro ⟨hE_mem, hconv⟩
      refine ⟨?_, hconv⟩
      -- If x ∈ limsupSet g t, then for some M, infinitely often g_n(x) > t + 1/M
      -- Since g_n(x) → f(x), limsup g_n(x) = f(x), so f(x) ≥ t + 1/M > t
      simp only [E, limsupSet, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at hE_mem
      -- hE_mem : ∃ M, ∀ N, ∃ n ≥ N, g n x > t + 1/(M+1)
      obtain ⟨M, hM⟩ := hE_mem
      -- Set threshold := t + 1/(M+1)
      set threshold := t + 1 / ((M : EReal) + 1) with h_threshold
      -- Handle edge cases first
      rcases eq_top_or_lt_top t with rfl | ht_ne_top
      · -- t = ⊤: threshold = ⊤ + eps = ⊤, and hM says g n x > ⊤, impossible
        exfalso
        obtain ⟨n, _, hn_gt⟩ := hM 0
        have h_threshold_eq_top : threshold = ⊤ := by
          rw [h_threshold]
          apply EReal.top_add_of_ne_bot
          intro h_eq
          have h_denom_ne_top : (M : EReal) + 1 ≠ ⊤ := EReal.add_ne_top (EReal.natCast_ne_top M) (EReal.coe_ne_top 1)
          have h_pos : (0 : EReal) < 1 / ((M : EReal) + 1) := by
            apply EReal.div_pos (EReal.coe_pos.mpr one_pos)
            calc (0 : EReal) < 1 := EReal.coe_pos.mpr one_pos
                 _ ≤ (M : EReal) + 1 := le_add_of_nonneg_left (EReal.coe_nonneg.mpr (Nat.cast_nonneg M))
            exact h_denom_ne_top
          rw [h_eq] at h_pos
          exact not_lt_bot h_pos
        rw [h_threshold_eq_top] at hn_gt
        exact (not_lt.mpr le_top) hn_gt
      rcases eq_bot_or_bot_lt t with rfl | ht_ne_bot
      · -- t = ⊥: threshold = ⊥ + eps = ⊥, need to show f x > ⊥
        -- Since g_n(x) ≥ 0 and g_n(x) → f(x), we have f(x) ≥ 0 > ⊥
        have hg_nonneg : ∀ n, g n x ≥ 0 := fun n => by
          obtain ⟨k, c, E, hE_props, heq⟩ := hg_simple n
          rw [heq]
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          apply Finset.sum_nonneg
          intro i _
          apply mul_nonneg (hE_props i).2
          simp only [EReal.indicator, Real.EReal_fun]
          exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
        -- g n x ≥ 0 for all n, and g n x → f x, so f x ≥ 0
        have h_limit_nonneg : f x ≥ 0 := by
          by_contra h_neg
          push_neg at h_neg
          have h_mem : Set.Iio 0 ∈ nhds (f x) := Iio_mem_nhds h_neg
          have h_event : ∀ᶠ n in Filter.atTop, g n x < 0 := hconv h_mem
          rw [Filter.eventually_atTop] at h_event
          obtain ⟨N₀, hN₀⟩ := h_event
          have := hN₀ N₀ (le_refl _)
          exact (not_lt.mpr (hg_nonneg N₀)) this
        calc (⊥ : EReal) < 0 := EReal.bot_lt_zero
             _ ≤ f x := h_limit_nonneg
      -- Now ⊥ < t < ⊤ (t is a finite real)
      by_contra h_not_gt
      push_neg at h_not_gt
      -- h_not_gt : f x ≤ t
      -- Derive contradiction: if f x ≤ t, eventually g_n x < threshold, but frequently > threshold
      have h_denom_ne_top : (M : EReal) + 1 ≠ ⊤ := EReal.add_ne_top (EReal.natCast_ne_top M) (EReal.coe_ne_top 1)
      have h_eps_pos : (1 : EReal) / ((M : EReal) + 1) > 0 := by
        apply EReal.div_pos (EReal.coe_pos.mpr one_pos)
        calc (0 : EReal) < 1 := EReal.coe_pos.mpr one_pos
             _ ≤ (M : EReal) + 1 := le_add_of_nonneg_left (EReal.coe_nonneg.mpr (Nat.cast_nonneg M))
        exact h_denom_ne_top
      -- eps is finite: just use that eps > 0 is positive and less than or equal to 1
      -- (h_eps_ne_top is not needed for the proof below, we can skip this)
      -- t < threshold using add_lt_add for finite values
      have h_t_lt : t < threshold := by
        rw [h_threshold]
        -- t is finite, so we can work with coercions
        obtain ⟨t', rfl⟩ : ∃ t' : ℝ, (t' : EReal) = t := by
          induction t using EReal.rec with
          | bot => exact absurd rfl (ne_of_gt ht_ne_bot)
          | top => exact absurd rfl (ne_of_lt ht_ne_top)
          | coe r => exact ⟨r, rfl⟩
        conv_lhs => rw [← add_zero (t' : EReal)]
        exact EReal.add_lt_add_left_coe h_eps_pos t'
      -- f x < threshold
      have h_fx_lt : f x < threshold := lt_of_le_of_lt h_not_gt h_t_lt
      -- By convergence, eventually g_n x < threshold
      have h_event : ∀ᶠ n in Filter.atTop, g n x < threshold := hconv (Iio_mem_nhds h_fx_lt)
      rw [Filter.eventually_atTop] at h_event
      obtain ⟨N₀, hN₀⟩ := h_event
      -- But by hM, there exists n ≥ N₀ with g n x > threshold
      obtain ⟨n, hn_ge, hn_gt⟩ := hM N₀
      exact (lt_irrefl _) (lt_trans (hN₀ n hn_ge) hn_gt)
  exact LebesgueMeasurable.of_ae_eq hE_meas hN_null h_ae_eq

/-! ### (v) ⟹ (vi): {f ≥ λ} = ⋂_{n≥1} {f > λ - 1/n} -/

-- Helper: if x > n for all n ∈ ℕ, then x = ⊤
private lemma EReal.eq_top_of_forall_nat_lt {x : EReal} (h : ∀ n : ℕ, x > n) : x = ⊤ := by
  induction x using EReal.rec with
  | bot =>
    exfalso
    have h0 : (⊥ : EReal) > (0 : ℕ) := h 0
    simp only [Nat.cast_zero, gt_iff_lt, not_lt_bot] at h0
  | top => rfl
  | coe r =>
    exfalso
    have h1 : (r : EReal) > (⌈r⌉₊ : ℕ) := h ⌈r⌉₊
    have h1' : r > (⌈r⌉₊ : ℕ) := by
      simp only [gt_iff_lt] at h1 ⊢
      rwa [show ((⌈r⌉₊ : ℕ) : EReal) = ((⌈r⌉₊ : ℕ) : ℝ) by norm_cast,
           EReal.coe_lt_coe_iff] at h1
    have h2 : r ≤ ⌈r⌉₊ := Nat.le_ceil r
    linarith

private lemma v_imp_vi : stmt_v f → stmt_vi f := by
  intro hv t
  -- Handle cases based on t
  rcases eq_bot_or_bot_lt t with rfl | ht_bot
  · -- t = ⊥: {f ≥ ⊥} = Set.univ
    have h_eq : {x | f x ≥ ⊥} = Set.univ := by ext x; simp
    rw [h_eq, ← Set.compl_empty]
    exact LebesgueMeasurable.empty.complement
  rcases eq_top_or_lt_top t with rfl | ht_top
  · -- t = ⊤: {f ≥ ⊤} = {f = ⊤} = ⋂_{n ∈ ℕ} {f > n}
    have h_eq : {x | f x ≥ ⊤} = ⋂ (n : ℕ), {x | f x > n} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, ge_iff_le]
      constructor
      · intro hfx n
        simp only [gt_iff_lt, top_le_iff.mp hfx]
        apply EReal.coe_lt_top
      · intro hfx
        exact top_le_iff.mpr (EReal.eq_top_of_forall_nat_lt hfx)
    exact h_eq ▸ LebesgueMeasurable.countable_inter (fun n => hv _)
  · -- t is finite: use {f ≥ t} = ⋂_{n≥1} {f > t - 1/(n+1)}
    -- Since t < ⊤ and ⊥ < t, we know t is a real number
    induction t using EReal.rec with
    | bot => exact (not_lt.mpr le_rfl ht_bot).elim
    | top => exact (not_lt.mpr le_rfl ht_top).elim
    | coe t' =>
      -- Use {f ≥ t'} = ⋂_n {f > (t' - 1/(n+1) : ℝ)}
      have h_eq : {x | f x ≥ (t' : EReal)} = ⋂ (n : ℕ), {x | f x > ((t' - 1 / (n + 1)) : ℝ)} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, ge_iff_le, gt_iff_lt]
        constructor
        · intro hfx n
          have h1 : (0 : ℝ) < 1 / (n + 1) := by positivity
          have h2 : (t' - 1 / (n + 1) : ℝ) < t' := by linarith
          have h3 : ((t' - 1 / (n + 1)) : EReal) < (t' : EReal) := EReal.coe_lt_coe_iff.mpr h2
          exact lt_of_lt_of_le h3 hfx
        · intro hfx
          by_contra h
          push_neg at h
          -- f x < t'
          have hfx_lt_t' : f x < (t' : EReal) := h
          -- Get a witness for f x being a real
          have hfx_ne_bot : f x ≠ ⊥ := by
            intro hfx_eq_bot
            have hbot : ((t' - 1 / ((0 : ℕ) + 1)) : ℝ) < (⊥ : EReal) := by
              simp only [Nat.cast_zero, zero_add, div_one]
              rw [← hfx_eq_bot]
              convert hfx 0 using 2
              simp
            exact not_lt_bot hbot
          have hfx_ne_top : f x ≠ ⊤ := ne_top_of_lt hfx_lt_t'
          -- So f x is a real
          have hr : f x = (f x).toReal := (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm
          set r := (f x).toReal with hr_def
          rw [hr] at hfx_lt_t' hfx
          have hr_lt_t' : r < t' := EReal.coe_lt_coe_iff.mp hfx_lt_t'
          have hdiff_pos : 0 < t' - r := by linarith
          obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t' - r))
          have h_n_pos : (0 : ℝ) < n := by
            by_cases hn0 : n = 0
            · subst hn0; simp at hn; linarith
            · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
          have hn' : 1 / ((n : ℝ) + 1) < t' - r := by
            calc 1 / ((n : ℝ) + 1) < 1 / (n : ℝ) := by
                  apply one_div_lt_one_div_of_lt h_n_pos; linarith
              _ < 1 / (1 / (t' - r)) := by
                  apply one_div_lt_one_div_of_lt (one_div_pos.mpr hdiff_pos) hn
              _ = t' - r := one_div_one_div (t' - r)
          -- So (t' - 1/(n+1) : ℝ) > r
          have hcontra := hfx n
          have hcontra' := EReal.coe_lt_coe_iff.mp hcontra
          linarith
      rw [h_eq]
      exact LebesgueMeasurable.countable_inter (fun n => hv _)

/-! ### (vi) ⟹ (v): {f > λ} = ⋃_{q ∈ ℚ, q > λ} {f ≥ q} -/

private lemma vi_imp_v : stmt_vi f → stmt_v f := by
  intro hvi t
  -- {f > t} = ⋃_{q : ℚ, q > t} {f ≥ q}
  -- Since rationals are dense, for any x with f x > t, there exists q ∈ ℚ with t < q ≤ f x
  -- Use encoding of ℚ to ℕ for countable union (via Encodable ℚ)
  let F : ℕ → Set (EuclideanSpace' d) := fun n =>
    match @Encodable.decode ℚ _ n with
    | some q => if (t < ((q : ℝ) : EReal)) then {x | f x ≥ ((q : ℝ) : EReal)} else ∅
    | none => ∅
  have hF_eq : ∀ n, F n = match @Encodable.decode ℚ _ n with
    | some q => if (t < ((q : ℝ) : EReal)) then {x | f x ≥ ((q : ℝ) : EReal)} else ∅
    | none => ∅ := fun _ => rfl
  have h_eq : {x | f x > t} = ⋃ n, F n := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hfx
      -- f x > t, so there exists q ∈ ℚ with t < q < f x
      obtain ⟨q, hq1, hq2⟩ := EReal.exists_rat_btwn_of_lt hfx
      use Encodable.encode q  -- encode q as ℕ
      rw [hF_eq, Encodable.encodek]
      simp only [hq1, ite_true, Set.mem_setOf_eq]
      exact le_of_lt hq2
    · intro ⟨n, hn⟩
      rw [hF_eq] at hn
      cases hd : @Encodable.decode ℚ _ n with
      | none => simp only [hd, Set.mem_empty_iff_false] at hn
      | some q =>
        simp only [hd] at hn
        by_cases h : t < ((q : ℝ) : EReal)
        · simp only [h, ite_true, Set.mem_setOf_eq] at hn
          calc t < ((q : ℝ) : EReal) := h
            _ ≤ f x := hn
        · simp only [h, ite_false, Set.mem_empty_iff_false] at hn
  rw [h_eq]
  -- This is a countable union of measurable sets
  apply LebesgueMeasurable.countable_union
  intro n
  rw [hF_eq]
  cases hd : @Encodable.decode ℚ _ n with
  | none => exact LebesgueMeasurable.empty
  | some q =>
    simp only
    split_ifs with h
    · exact hvi ((q : ℝ) : EReal)
    · exact LebesgueMeasurable.empty

/-! ### (v) ⟹ (viii): {f ≤ t} = {f > t}ᶜ -/

private lemma v_imp_viii : stmt_v f → stmt_viii f := by
  intro hv t
  have h_eq : {x | f x ≤ t} = {x | f x > t}ᶜ := by ext x; simp [not_lt]
  rw [h_eq]
  exact (hv t).complement

/-! ### (vi) ⟹ (vii): {f < t} = {f ≥ t}ᶜ -/

private lemma vi_imp_vii : stmt_vi f → stmt_vii f := by
  intro hvi t
  have h_eq : {x | f x < t} = {x | f x ≥ t}ᶜ := by ext x; simp [not_le]
  rw [h_eq]
  exact (hvi t).complement

/-! ### (vii) ⟹ (vi): {f ≥ t} = {f < t}ᶜ -/

private lemma vii_imp_vi : stmt_vii f → stmt_vi f := by
  intro hvii t
  have h_eq : {x | f x ≥ t} = {x | f x < t}ᶜ := by ext x; simp [not_lt]
  rw [h_eq]
  exact (hvii t).complement

/-! ### (viii) ⟹ (v): {f > t} = {f ≤ t}ᶜ -/

private lemma viii_imp_v : stmt_viii f → stmt_v f := by
  intro hviii t
  have h_eq : {x | f x > t} = {x | f x ≤ t}ᶜ := by ext x; simp [not_le]
  rw [h_eq]
  exact (hviii t).complement

/-! ### (v)-(viii) ⟹ (ix): Intervals are intersections of half-intervals -/

private lemma v_to_viii_imp_ix (hv : stmt_v f) (hvi : stmt_vi f) (hvii : stmt_vii f) (hviii : stmt_viii f) :
    stmt_ix f := by
  intro I
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ioo a b) = {x | f x > a} ∩ {x | f x < b} := by
      rw [EReal.image_coe_Ioo]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_inter_iff, Set.mem_setOf_eq, gt_iff_lt]
    rw [h_eq]
    exact (hv _).inter (hvii _)
  | Icc a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Icc a b) = {x | f x ≥ a} ∩ {x | f x ≤ b} := by
      rw [EReal.image_coe_Icc]
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_inter_iff, Set.mem_setOf_eq, ge_iff_le]
    rw [h_eq]
    exact (hvi _).inter (hviii _)
  | Ioc a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ioc a b) = {x | f x > a} ∩ {x | f x ≤ b} := by
      rw [EReal.image_coe_Ioc]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_inter_iff, Set.mem_setOf_eq, gt_iff_lt]
    rw [h_eq]
    exact (hv _).inter (hviii _)
  | Ico a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ico a b) = {x | f x ≥ a} ∩ {x | f x < b} := by
      rw [EReal.image_coe_Ico]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_inter_iff, Set.mem_setOf_eq, ge_iff_le]
    rw [h_eq]
    exact (hvi _).inter (hvii _)

/-! ### (ix) ⟹ (x): Open sets are countable unions of intervals -/

-- For unsigned f, f⁻¹'({⊥}) = ∅
private lemma unsigned_preimage_bot_empty (hf : Unsigned f) : f⁻¹' {⊥} = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro hfx
  have h := hf x
  rw [hfx] at h
  simp only [ge_iff_le] at h
  exact not_le.mpr EReal.bot_lt_zero h

-- The embedded reals ℝ as a subset of EReal
private lemma ereal_reals_eq_iUnion :
    (Set.range Real.toEReal : Set EReal) = ⋃ (n : ℕ), Real.toEReal '' Set.Ioo (-(n:ℝ) - 1) (n + 1) := by
  ext x
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_image, Set.mem_Ioo]
  constructor
  · intro ⟨r, hr⟩
    use ⌈|r|⌉₊, r
    constructor
    · constructor
      · have h1 : -|r| ≤ r := neg_abs_le r
        have h2 : |r| ≤ ⌈|r|⌉₊ := Nat.le_ceil |r|
        linarith
      · have h1 : r ≤ |r| := le_abs_self r
        have h2 : |r| ≤ ⌈|r|⌉₊ := Nat.le_ceil |r|
        linarith
    · exact hr
  · intro ⟨_, r, _, hr⟩
    exact ⟨r, hr⟩

-- ℝ embedded in EReal has Lebesgue measurable preimage
private lemma measurable_preimage_reals (hix : stmt_ix f) : LebesgueMeasurable (f⁻¹' (Set.range Real.toEReal)) := by
  rw [ereal_reals_eq_iUnion, Set.preimage_iUnion]
  apply LebesgueMeasurable.countable_union
  intro n
  exact hix (BoundedInterval.Ioo (-(n:ℝ) - 1) (n + 1))

-- {⊤} as complement of ℝ ∪ {⊥}
private lemma ereal_top_singleton_eq : ({⊤} : Set EReal) = (Set.range Real.toEReal ∪ {⊥})ᶜ := by
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_union, Set.mem_range]
  constructor
  · intro hx
    rw [hx]
    push_neg
    constructor
    · intro r hr
      exact EReal.coe_ne_top r hr
    · intro h; exact absurd h.symm (ne_of_lt bot_lt_top)
  · intro hx
    push_neg at hx
    induction x using EReal.rec with
    | bot => exact (hx.2 rfl).elim
    | top => rfl
    | coe r => exact (hx.1 r rfl).elim

-- For unsigned f, f⁻¹'({⊤}) is Lebesgue measurable
private lemma measurable_preimage_top (hf : Unsigned f) (hix : stmt_ix f) : LebesgueMeasurable (f⁻¹' {⊤}) := by
  rw [ereal_top_singleton_eq, Set.preimage_compl]
  apply LebesgueMeasurable.complement
  rw [Set.preimage_union]
  apply LebesgueMeasurable.union
  · exact measurable_preimage_reals hix
  · rw [unsigned_preimage_bot_empty hf]
    exact LebesgueMeasurable.empty

-- The intersection of an open set with ℝ can be expressed using countable intervals
private lemma open_inter_reals_eq_countable_union (U : Set EReal) (hU : IsOpen U) :
    ∃ S : Set (Set ℝ), S.Countable ∧ (∀ I ∈ S, ∃ a b, I = Set.Ioo a b) ∧
    U ∩ Set.range Real.toEReal = ⋃ I ∈ S, Real.toEReal '' I := by
  let V : Set ℝ := Real.toEReal ⁻¹' U
  have hV_open : IsOpen V := hU.preimage continuous_coe_real_ereal
  let RatIntervals := {I : Set ℝ | ∃ (a b : ℚ), I = Set.Ioo (a : ℝ) b ∧ I ⊆ V}
  have hRI_count : RatIntervals.Countable := by
    have h : RatIntervals ⊆ Set.range (fun p : ℚ × ℚ => Set.Ioo (p.1 : ℝ) p.2) := by
      intro I hI
      obtain ⟨a, b, hab, _⟩ := hI
      exact ⟨(a, b), hab.symm⟩
    exact Set.Countable.mono h (Set.countable_range _)
  have hRI_intervals : ∀ I ∈ RatIntervals, ∃ a b, I = Set.Ioo a b := by
    intro I hI
    obtain ⟨a, b, hab, _⟩ := hI
    exact ⟨a, b, hab⟩
  have hRI_union : V = ⋃ I ∈ RatIntervals, I := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open x hx
      obtain ⟨a, ha_lo, ha_hi⟩ := exists_rat_btwn (by linarith : x - ε / 2 < x)
      obtain ⟨b, hb_lo, hb_hi⟩ := exists_rat_btwn (by linarith : x < x + ε / 2)
      refine ⟨Set.Ioo a b, ?_, ?_⟩
      · refine ⟨a, b, rfl, ?_⟩
        intro y hy
        apply hε_ball
        rw [Metric.mem_ball, Real.dist_eq]
        simp only [Set.mem_Ioo] at hy
        have h1 : y - x < ε / 2 := by linarith [hy.2]
        have h2 : x - y < ε / 2 := by linarith [hy.1]
        rw [abs_lt]
        constructor <;> linarith
      · simp only [Set.mem_Ioo]
        exact ⟨ha_hi, hb_lo⟩
    · intro ⟨I, hI, hxI⟩
      obtain ⟨_, _, _, hI_sub⟩ := hI
      exact hI_sub hxI
  use RatIntervals
  refine ⟨hRI_count, hRI_intervals, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion, Set.mem_image]
  constructor
  · intro ⟨hy_U, r, hr⟩
    have hr_V : r ∈ V := by
      show Real.toEReal r ∈ U
      rw [hr]; exact hy_U
    rw [hRI_union] at hr_V
    simp only [Set.mem_iUnion] at hr_V
    obtain ⟨I, hI_mem, hr_I⟩ := hr_V
    exact ⟨I, hI_mem, r, hr_I, hr⟩
  · intro ⟨I, hI_mem, r, hr_I, hr⟩
    constructor
    · obtain ⟨_, _, _, hI_sub⟩ := hI_mem
      have : r ∈ V := hI_sub hr_I
      rw [← hr]
      exact this
    · exact ⟨r, hr⟩

private lemma ix_imp_x (hf : Unsigned f) : stmt_ix f → stmt_x f := by
  intro hix U hU
  -- Decompose U = (U ∩ ℝ) ∪ (U ∩ {⊤}) ∪ (U ∩ {⊥})
  have hU_decomp : U = (U ∩ Set.range Real.toEReal) ∪ (U ∩ {⊤}) ∪ (U ∩ {⊥}) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro hx
      induction x using EReal.rec with
      | bot => right; exact ⟨hx, rfl⟩
      | top => left; right; exact ⟨hx, rfl⟩
      | coe r => left; left; exact ⟨hx, r, rfl⟩
    · intro hx
      rcases hx with (⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩ <;> exact hx
  rw [hU_decomp, Set.preimage_union, Set.preimage_union]
  apply LebesgueMeasurable.union
  apply LebesgueMeasurable.union
  -- Part 1: f⁻¹'(U ∩ ℝ) is Lebesgue measurable
  · obtain ⟨S, hS_count, hS_intervals, hS_eq⟩ := open_inter_reals_eq_countable_union U hU
    rw [hS_eq, Set.preimage_iUnion₂]
    -- Use countable encoding of S
    haveI : Countable S := hS_count.to_subtype
    haveI e : Encodable S := Encodable.ofCountable S
    let E' : ℕ → Set (EuclideanSpace' d) := fun n =>
      match @Encodable.decode S e n with
      | some p => f⁻¹' (Real.toEReal '' p.val)
      | none => ∅
    have h_eq' : ⋃ (I : Set ℝ) (_ : I ∈ S), f⁻¹' (Real.toEReal '' I) = ⋃ n, E' n := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_preimage, E']
      constructor
      · intro ⟨I, hI, hx⟩
        use @Encodable.encode S e ⟨I, hI⟩
        simp only [Encodable.encodek]
        exact hx
      · intro ⟨n, hn⟩
        cases hd : @Encodable.decode S e n with
        | none => simp only [hd, Set.mem_empty_iff_false] at hn
        | some p =>
          simp only [hd] at hn
          exact ⟨p.val, p.property, hn⟩
    rw [h_eq']
    apply LebesgueMeasurable.countable_union
    intro n
    simp only [E']
    cases hd : @Encodable.decode S e n with
    | none => exact LebesgueMeasurable.empty
    | some p =>
      simp only
      obtain ⟨a, b, hab⟩ := hS_intervals p.val p.property
      rw [hab]
      exact hix (BoundedInterval.Ioo a b)
  -- Part 2: f⁻¹'(U ∩ {⊤}) is Lebesgue measurable
  · by_cases htop : ⊤ ∈ U
    · have h_eq : U ∩ {⊤} = {⊤} := Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr htop)
      rw [h_eq]
      exact measurable_preimage_top hf hix
    · have h_eq : U ∩ {⊤} = ∅ := Set.inter_singleton_eq_empty.mpr htop
      rw [h_eq, Set.preimage_empty]
      exact LebesgueMeasurable.empty
  -- Part 3: f⁻¹'(U ∩ {⊥}) is Lebesgue measurable (empty for unsigned f)
  · rw [Set.preimage_inter, unsigned_preimage_bot_empty hf, Set.inter_empty]
    exact LebesgueMeasurable.empty

/-! ### (x) ⟺ (xi): Complementation -/

private lemma x_iff_xi : stmt_x f ↔ stmt_xi f := by
  constructor
  · intro hx K hK
    have h_eq : f⁻¹' K = (f⁻¹' Kᶜ)ᶜ := by simp
    rw [h_eq]
    exact (hx _ hK.isOpen_compl).complement
  · intro hxi U hU
    have h_eq : f⁻¹' U = (f⁻¹' Uᶜ)ᶜ := by simp
    rw [h_eq]
    exact (hxi _ hU.isClosed_compl).complement

/-! ### (x) ⟹ (vii): {f < λ} = f⁻¹'(Iio λ) and Iio λ is open -/

private lemma x_imp_vii : stmt_x f → stmt_vii f := by
  intro hx t
  have h_open : IsOpen (Set.Iio t) := isOpen_Iio
  have h_eq : {x | f x < t} = f⁻¹' (Set.Iio t) := rfl
  rw [h_eq]
  exact hx _ h_open

/-! ### (v)-(xi) ⟹ (iv): Construction of approximating sequence -/

-- Helper: the norm ball centered at origin is Lebesgue measurable
private lemma normBall_LebesgueMeasurable (r : ℝ) :
    LebesgueMeasurable {x : EuclideanSpace' d | ‖x‖ ≤ r} := by
  have h : {x : EuclideanSpace' d | ‖x‖ ≤ r} = Metric.closedBall 0 r := by
    ext x; simp [Metric.closedBall, dist_zero_right]
  rw [h]
  exact LebesgueMeasurable.closedBall 0 r

-- The approximating function: f_n(x) = floor(min(f(x), n) * 2^n) / 2^n when |x| ≤ n, else 0
-- This is the largest k·2^{-n} ≤ min(f(x), n)
private noncomputable def approx_fn (f : EuclideanSpace' d → EReal) (n : ℕ) (x : EuclideanSpace' d) : EReal :=
  if ‖x‖ ≤ n then
    let t := min (f x) n
    if t = ⊥ then 0  -- won't happen for unsigned f
    else if t = ⊤ then n  -- t = min(⊤, n) = n, so this case shouldn't trigger
    else
      let r := t.toReal
      if r < 0 then 0  -- won't happen for unsigned f
      else ((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ)
  else 0

-- Key lemma: approx_fn takes values in {k/2^n : k = 0, 1, ..., n·2^n}
private lemma approx_fn_values (f : EuclideanSpace' d → EReal) (hf : Unsigned f) (n : ℕ) (x : EuclideanSpace' d) :
    ∃ k : ℕ, k ≤ n * 2^n ∧ approx_fn f n x = ((k : ℕ) : ℝ) / (2^n : ℝ) := by
  simp only [approx_fn]
  split_ifs with hnorm hbot htop hneg
  · -- t = ⊥ case (won't happen)
    use 0; simp
  · -- t = ⊤ case: min(f x, n) = ⊤ is impossible since min(f x, n) ≤ n
    exfalso
    have h1 : min (f x) ↑n ≤ ↑n := min_le_right _ _
    rw [htop] at h1
    exact not_le.mpr (EReal.coe_lt_top n) h1
  · -- r < 0 case (won't happen for unsigned)
    use 0; simp
  · -- normal case
    use ⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊
    constructor
    · -- Need to show floor ≤ n * 2^n
      have h_min_le : (min (f x) ↑n).toReal ≤ n := by
        have h1 : min (f x) ↑n ≤ ↑n := min_le_right _ _
        have h2 : min (f x) ↑n ≠ ⊤ := htop
        have h3 : min (f x) ↑n ≠ ⊥ := hbot
        have h4 : (↑n : EReal) ≠ ⊤ := EReal.coe_ne_top n
        exact EReal.toReal_le_toReal h1 h3 h4
      have h_prod_le : (min (f x) ↑n).toReal * 2^n ≤ (n : ℝ) * 2^n := by
        apply mul_le_mul_of_nonneg_right h_min_le
        exact pow_nonneg (by norm_num) n
      have h_nonneg : 0 ≤ (min (f x) ↑n).toReal * 2^n := by
        apply mul_nonneg
        · have h1 : 0 ≤ min (f x) ↑n := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
          exact EReal.toReal_nonneg h1
        · exact pow_nonneg (by norm_num) n
      have h_floor_le : (⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℝ) ≤ n * 2^n := by
        calc (⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℝ)
            ≤ (min (f x) ↑n).toReal * 2 ^ n := Nat.floor_le h_nonneg
          _ ≤ (n : ℝ) * 2^n := h_prod_le
      exact_mod_cast h_floor_le
    · rfl
  · -- |x| > n case
    use 0; simp

-- Helper: approx_fn is always nonnegative for unsigned functions
private lemma approx_fn_nonneg (f : EuclideanSpace' d → EReal) (_hf : Unsigned f)
    (n : ℕ) (x : EuclideanSpace' d) : approx_fn f n x ≥ 0 := by
  simp only [approx_fn]
  split_ifs with hnorm hbot htop hneg
  · exact le_refl 0  -- t = ⊥ case
  · exact EReal.coe_nonneg.mpr (Nat.cast_nonneg n)  -- t = ⊤ case
  · exact le_refl 0  -- r < 0 case
  · exact EReal.coe_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) n))
  · exact le_refl 0  -- |x| > n case

-- Helper: floor approximation converges to the value as iSup
-- For r ≥ 0: r = ⨆ n, ⌊r * 2^n⌋₊ / 2^n (in EReal)
private lemma floor_approx_iSup_eq (r : ℝ) (hr : r ≥ 0) :
    (r : EReal) = ⨆ n : ℕ, (((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) := by
  -- Define the approximating function for cleaner notation
  let f : ℕ → ℝ := fun n => ((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ)
  change (r : EReal) = ⨆ n : ℕ, (f n : EReal)
  apply le_antisymm
  · -- Upper bound: r ≤ iSup
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    -- Find N such that 1/2^N < ε using (1/2)^n → 0
    have h_tendsto : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rw [Metric.tendsto_atTop] at h_tendsto
    obtain ⟨N, hN⟩ := h_tendsto ε hε
    specialize hN N (le_refl N)
    simp only [Real.dist_eq, sub_zero, abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 1/2) N)] at hN
    have h2N_pos : (2 : ℝ)^N > 0 := pow_pos (by norm_num) N
    have h_eps : (1 : ℝ) / 2^N < ε := by
      convert hN using 1
      rw [one_div, ← inv_pow, inv_eq_one_div]
    -- floor approx bound: r - 1/2^N < f N
    have h_floor_bound : r - 1/2^N < f N := by
      simp only [f]
      have h1 : r * 2^N - 1 < (⌊r * 2^N⌋₊ : ℝ) := Nat.sub_one_lt_floor (r * 2^N)
      calc r - 1/2^N = (r * 2^N - 1) / 2^N := by field_simp
           _ < (⌊r * 2^N⌋₊ : ℝ) / 2^N := by apply div_lt_div_of_pos_right h1 h2N_pos
    have h_le_iSup : (f N : EReal) ≤ ⨆ n : ℕ, (f n : EReal) := le_iSup_of_le N (le_refl _)
    -- r ≤ f N + ε
    have h3 : r ≤ f N + ε := by linarith
    calc (r : EReal) ≤ (f N + ε : ℝ) := EReal.coe_le_coe_iff.mpr h3
         _ = (f N : EReal) + (ε : EReal) := by rw [← EReal.coe_add]
         _ ≤ (⨆ n : ℕ, (f n : EReal)) + ε := add_le_add_left h_le_iSup ε
  · -- Lower bound: iSup ≤ r
    apply iSup_le
    intro n
    have h2n_pos : (2 : ℝ)^n > 0 := pow_pos (by norm_num) n
    have h_floor_le : f n ≤ r := by
      simp only [f]
      calc (⌊r * 2^n⌋₊ : ℝ) / 2^n ≤ (r * 2^n) / 2^n := by
             apply div_le_div_of_nonneg_right (Nat.floor_le (mul_nonneg hr (le_of_lt h2n_pos))) (le_of_lt h2n_pos)
           _ = r := by field_simp
    exact EReal.coe_le_coe_iff.mpr h_floor_le

-- Helper: approx_fn simplifies to floor formula when f x is finite and r ≤ n
private lemma approx_fn_eq_floor_when_finite (f : EuclideanSpace' d → EReal) (_hf : Unsigned f)
    (n : ℕ) (x : EuclideanSpace' d) (hn : ‖x‖ ≤ n) (r : ℝ) (hr : f x = r) (hr_nonneg : r ≥ 0)
    (hrn : r ≤ n) :
    approx_fn f n x = (((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) := by
  simp only [approx_fn, hn, ite_true, hr]
  have h_min : min (r : EReal) n = r := min_eq_left (EReal.coe_le_coe_iff.mpr hrn)
  have h_min_ne_bot : min (r : EReal) n ≠ ⊥ := by simp [h_min, EReal.coe_ne_bot]
  have h_min_ne_top : min (r : EReal) n ≠ ⊤ := by simp [h_min, EReal.coe_ne_top]
  have h_toReal : (min (r : EReal) n).toReal = r := by
    simp [h_min, EReal.toReal_coe]
  have h_nonneg : ¬(min (r : EReal) n).toReal < 0 := by simp [h_toReal, hr_nonneg]
  simp only [h_min_ne_bot, ite_false, h_min_ne_top, h_toReal]
  simp only [not_lt.mpr hr_nonneg, ite_false]

-- Helper: (n * 2^n) / 2^n = n in EReal
private lemma mul_pow2_div_pow2_eq (n : ℕ) :
    ((n * 2^n : ℕ) : EReal) / ((2^n : ℕ) : EReal) = ((n : ℕ) : EReal) := by
  have h2n_ne : (2^n : ℕ) ≠ 0 := pow_ne_zero n (by norm_num)
  have h2n_ne_bot : ((2^n : ℕ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have h2n_ne_top : ((2^n : ℕ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have h2n_ne_zero : ((2^n : ℕ) : EReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact h2n_ne
  rw [show ((n * 2^n : ℕ) : EReal) = ((n : ℕ) : EReal) * ((2^n : ℕ) : EReal) by push_cast; ring_nf]
  rw [mul_div_assoc, EReal.div_self h2n_ne_bot h2n_ne_top h2n_ne_zero, mul_one]

-- Helper: Extract equality from EReal division equality with 2^n denominator
private lemma ereal_div_pow2_eq_imp_eq (j k n : ℕ)
    (h : (((j : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
         (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal)) :
    j = k := by
  have h2n_pos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
  have h2n_ne : ((2^n : ℕ) : ℝ) ≠ 0 := by positivity
  have h_real : ((j : ℕ) : ℝ) / (2^n : ℕ) = ((k : ℕ) : ℝ) / (2^n : ℕ) := by
    have hlhs : (((j : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                (((j : ℕ) : ℝ) / ((2^n : ℕ) : ℝ) : EReal) := by norm_cast
    have hrhs : (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                (((k : ℕ) : ℝ) / ((2^n : ℕ) : ℝ) : EReal) := by norm_cast
    rw [hlhs, hrhs] at h
    exact EReal.coe_eq_coe_iff.mp h
  have h_eq : ((j : ℕ) : ℝ) = ((k : ℕ) : ℝ) := by
    rw [div_eq_div_iff h2n_ne h2n_ne] at h_real
    exact mul_right_cancel₀ h2n_ne h_real
  exact Nat.cast_injective h_eq

-- Each level set of approx_fn is LebesgueMeasurable
-- The key observation: level sets are Boolean combinations of:
-- - {‖x‖ ≤ n} which is closed, hence LebesgueMeasurable
-- - {‖x‖ > n} which is open, hence LebesgueMeasurable
-- - {f x ≥ t} which is LebesgueMeasurable by hvi
-- - {f x < t} which is LebesgueMeasurable by hvii
private lemma approx_fn_levelset_LebesgueMeasurable (hf : Unsigned f) (hvi : stmt_vi f)
    (hvii : stmt_vii f) (n : ℕ) (v : EReal) :
    LebesgueMeasurable {x | approx_fn f n x = v} := by
  -- Helper: ball and outside ball are Lebesgue measurable
  have ball_leb : LebesgueMeasurable {x : EuclideanSpace' d | ‖x‖ ≤ (n : ℝ)} := normBall_LebesgueMeasurable n
  have outside_leb : LebesgueMeasurable {x : EuclideanSpace' d | ‖x‖ > (n : ℝ)} :=
    (isOpen_lt continuous_const continuous_norm).measurable

  by_cases hv_range : v ∈ Set.range (approx_fn f n)
  swap
  · -- v not in range: level set is empty
    convert LebesgueMeasurable.empty
    ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h; exact hv_range ⟨x, h⟩

  -- v is in range: the level set is a Boolean combination of measurable sets
  -- Decompose into inside/outside ball
  have h_split : {x | approx_fn f n x = v} =
      ({x | ‖x‖ ≤ (n:ℝ)} ∩ {x | approx_fn f n x = v}) ∪
      ({x | ‖x‖ > (n:ℝ)} ∩ {x | approx_fn f n x = v}) := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    by_cases h : ‖x‖ ≤ n <;> simp [h, lt_of_not_ge]
  rw [h_split]
  apply LebesgueMeasurable.union

  -- Inside ball case: Show {‖x‖ ≤ n} ∩ {approx_fn = v} is LebesgueMeasurable
  -- Strategy: Show this is a Boolean combination of:
  -- - {‖x‖ ≤ n} which is LebesgueMeasurable (closed ball)
  -- - {f x ≥ t} for various thresholds t (LebesgueMeasurable by hvi)
  -- - {f x < t} for various thresholds t (LebesgueMeasurable by hvii)
  · obtain ⟨x₀, hx₀⟩ := hv_range
    obtain ⟨k, hk_bound, hk_eq⟩ := approx_fn_values f hf n x₀
    have hv_eq : v = ((k : ℕ) : ℝ) / (2^n : ℝ) := by rw [← hx₀, hk_eq]
    have h2n_pos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
    have h2n_ne : (2^n : ℝ) ≠ 0 := ne_of_gt h2n_pos
    by_cases hk_max : k = n * 2^n
    · -- k = n * 2^n: level set inside ball equals {‖x‖ ≤ n} ∩ {f x ≥ n}
      have hv_eq_n : v = n := by
        rw [hv_eq, hk_max]
        conv_lhs => rw [show ((n * 2^n : ℕ) : ℝ) = (n : ℝ) * 2^n by simp [Nat.cast_mul, Nat.cast_pow]]
        rw [← EReal.coe_div]; congr 1; field_simp
      have h_eq : {x | ‖x‖ ≤ (n:ℝ)} ∩ {x | approx_fn f n x = v} =
          {x | ‖x‖ ≤ n} ∩ {x | f x ≥ (n : EReal)} := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro ⟨hnorm, hval⟩
          rw [hv_eq_n] at hval
          refine ⟨hnorm, ?_⟩
          simp only [approx_fn, hnorm, ite_true] at hval
          split_ifs at hval with hbot htop hneg
          · exfalso
            have h_min_ge : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            rw [hbot] at h_min_ge; exact not_le.mpr EReal.bot_lt_zero h_min_ge
          · grind
          · exfalso
            have h_min_ge : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            exact not_le.mpr hneg (EReal.toReal_nonneg h_min_ge)
          · -- floor(...)/2^n = n means floor(...) = n*2^n
            -- First normalize the coercions in hval
            have hval' : (((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) = (n : EReal) := by
              have h1 : ((2^n : ℕ) : EReal) = ((2^n : ℕ) : ℝ) := EReal.coe_natCast.symm
              have h2 : ((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : EReal) =
                  ((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : ℝ) := EReal.coe_natCast.symm
              simp only [← EReal.coe_div] at hval; exact hval
            have h_coe := EReal.coe_eq_coe_iff.mp hval'
            have h_floor : ⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ = n * 2^n := by
              field_simp at h_coe
              have h_coe' : (⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℝ) = ((n * 2^n : ℕ) : ℝ) := by
                push_cast; linarith
              exact Nat.cast_injective h_coe'
            have h_min_nonneg : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            have h_prod_nonneg := mul_nonneg (EReal.toReal_nonneg h_min_nonneg) (le_of_lt h2n_pos)
            have h_prod_ge : (min (f x) ↑n).toReal * 2^n ≥ n * 2^n := by
              have := Nat.floor_le h_prod_nonneg; rw [h_floor] at this; exact_mod_cast this
            have h_toReal_ge : (min (f x) ↑n).toReal ≥ n := by nlinarith
            have h_min_le : (min (f x) ↑n).toReal ≤ n := by
              have h_le := min_le_right (f x) ↑n
              have := EReal.toReal_le_toReal h_le hbot (EReal.coe_ne_top n)
              simp only at this; exact this
            have h_min_eq_n : (min (f x) ↑n).toReal = n := le_antisymm h_min_le h_toReal_ge
            by_contra hcontra; push_neg at hcontra
            have h_min_eq : min (f x) ↑n = f x := min_eq_left (le_of_lt hcontra)
            rw [h_min_eq] at h_min_eq_n
            have h_fx_ne_top : f x ≠ ⊤ := by intro heq; rw [heq] at hcontra; exact not_lt.mpr le_top hcontra
            have h_fx_ne_bot : f x ≠ ⊥ := by intro heq; rw [h_min_eq] at hbot; exact hbot heq
            rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot] at hcontra
            have hcontra' : (f x).toReal < (n : ℝ) := EReal.coe_lt_coe_iff.mp hcontra
            rw [h_min_eq_n] at hcontra'
            exact lt_irrefl (n : ℝ) hcontra'
        · intro ⟨hnorm, hfx_ge⟩
          refine ⟨hnorm, ?_⟩
          simp only [approx_fn, hnorm, ite_true]
          have h_min_eq : min (f x) ↑n = ↑n := min_eq_right hfx_ge
          split_ifs with hbot htop hneg
          · exfalso; rw [h_min_eq] at hbot; exact EReal.coe_ne_bot n hbot
          · exfalso; rw [h_min_eq] at htop; exact EReal.coe_ne_top n htop
          · exfalso; rw [h_min_eq] at hneg
            have h_toReal : (↑n : EReal).toReal = (n : ℝ) := by
              rw [show (↑n : EReal) = ↑(n : ℝ) from EReal.coe_natCast.symm, EReal.toReal_coe]
            rw [h_toReal] at hneg; exact not_lt.mpr (Nat.cast_nonneg n) hneg
          · rw [h_min_eq, hv_eq_n]
            have h_toReal : (↑n : EReal).toReal = (n : ℝ) := by
              rw [show (↑n : EReal) = ↑(n : ℝ) from EReal.coe_natCast.symm, EReal.toReal_coe]
            rw [h_toReal]
            have h_floor : ⌊(n : ℝ) * 2 ^ n⌋₊ = n * 2^n := by
              rw [show ((n : ℕ) : ℝ) * 2 ^ n = ((n * 2^n : ℕ) : ℝ) by
                simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]]
              exact Nat.floor_natCast (n * 2^n)
            rw [h_floor]
            -- Goal: ↑↑(n * 2 ^ n) / ↑(2 ^ n) = ↑n
            -- Use EReal.coe_natCast to normalize coercions
            simp only [← EReal.coe_natCast, ← EReal.coe_div, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            grind
      rw [h_eq]
      exact ball_leb.inter (hvi n)
    · -- k < n * 2^n: level set is {‖x‖ ≤ n} ∩ {f x ≥ k/2^n} ∩ {f x < (k+1)/2^n}
      have hk_lt : k < n * 2^n := Nat.lt_of_le_of_ne hk_bound hk_max
      have h_le := hvi (((k : ℕ) : ℝ) / (2^n : ℝ))
      have h_lt := hvii ((((k + 1) : ℕ) : ℝ) / (2^n : ℝ))
      have h_eq : {x | ‖x‖ ≤ (n:ℝ)} ∩ {x | approx_fn f n x = v} =
          {x | ‖x‖ ≤ n} ∩ ({x | f x ≥ (((k : ℕ) : ℝ) / (2^n : ℝ) : EReal)} ∩
          {x | f x < ((((k + 1) : ℕ) : ℝ) / (2^n : ℝ) : EReal)}) := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro ⟨hnorm, hval⟩
          rw [hv_eq] at hval
          simp only [approx_fn, hnorm, ite_true] at hval
          split_ifs at hval with hbot htop hneg
          · exfalso
            have h_min_ge : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            rw [hbot] at h_min_ge; exact not_le.mpr EReal.bot_lt_zero h_min_ge
          · exact absurd (htop ▸ min_le_right (f x) (↑n : EReal)) (not_le.mpr (EReal.coe_lt_top n))
          · exfalso
            have h_min_ge : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            exact not_le.mpr hneg (EReal.toReal_nonneg h_min_ge)
          · -- Normal case: Show floor = k and derive bounds
            have hval' : (((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) =
                (((k : ℕ) : ℝ) / (2^n : ℝ) : EReal) := by
              have h1 : ((2^n : ℕ) : EReal) = ((2^n : ℕ) : ℝ) := EReal.coe_natCast.symm
              have h2 : ((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : EReal) =
                  ((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : ℝ) := EReal.coe_natCast.symm
              have h3 : ((k : ℕ) : EReal) = ((k : ℕ) : ℝ) := EReal.coe_natCast.symm
              simp only [← EReal.coe_div] at hval; exact hval
            have h_coe := EReal.coe_eq_coe_iff.mp hval'
            have h_floor : ⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ = k := by
              field_simp at h_coe; exact Nat.cast_injective h_coe
            have h_min_nonneg : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            have h_prod_nonneg := mul_nonneg (EReal.toReal_nonneg h_min_nonneg) (le_of_lt h2n_pos)
            -- Get bounds on (min (f x) n).toReal
            have h_ge : (min (f x) ↑n).toReal ≥ (k : ℝ) / 2^n := by
              have := Nat.floor_le h_prod_nonneg; rw [h_floor] at this
              calc (k : ℝ) / 2^n = (k : ℝ) * (2^n)⁻¹ := by ring
                _ ≤ (min (f x) ↑n).toReal * 2^n * (2^n)⁻¹ := by
                  apply mul_le_mul_of_nonneg_right this (inv_nonneg.mpr (le_of_lt h2n_pos))
                _ = (min (f x) ↑n).toReal := by field_simp
            have h_lt' : (min (f x) ↑n).toReal * 2^n < k + 1 := by
              have := Nat.lt_floor_add_one ((min (f x) ↑n).toReal * 2^n)
              rw [h_floor] at this; exact_mod_cast this
            have h_toReal_lt : (min (f x) ↑n).toReal < ((k + 1) : ℝ) / 2^n := by
              calc (min (f x) ↑n).toReal = (min (f x) ↑n).toReal * 2^n / 2^n := by field_simp
                _ < ((k + 1) : ℝ) / 2^n := div_lt_div_of_pos_right h_lt' h2n_pos
            -- Show (k+1)/2^n ≤ n
            have h_val_le_n : ((k + 1) : ℝ) / 2^n ≤ n := by
              have h1 : (k + 1 : ℕ) ≤ n * 2^n := by omega
              have h1' : ((k + 1) : ℝ) ≤ (n * 2^n : ℝ) := by exact_mod_cast h1
              calc ((k + 1) : ℝ) / 2^n ≤ (n * 2^n : ℝ) / 2^n := div_le_div_of_nonneg_right h1' (le_of_lt h2n_pos)
                _ = n := by field_simp
            have h_fx_lt_n : f x < ↑n := by
              by_cases h_fx_le_n : f x ≤ n
              · have h_min_eq : min (f x) ↑n = f x := min_eq_left h_fx_le_n
                rw [h_min_eq] at h_toReal_lt
                by_cases h_fx_top : f x = ⊤
                · rw [h_fx_top] at h_fx_le_n; exact absurd h_fx_le_n (not_le.mpr (EReal.coe_lt_top n))
                · have h_fx_ne_bot : f x ≠ ⊥ := by intro heq; rw [h_min_eq] at hbot; exact hbot heq
                  rw [← EReal.coe_toReal h_fx_top h_fx_ne_bot]
                  rw [show (↑n : EReal) = ↑(n : ℝ) from EReal.coe_natCast.symm]
                  rw [EReal.coe_lt_coe_iff]
                  have h_k1_eq : (↑k + 1 : ℝ) = ((k + 1) : ℕ) := by simp only [Nat.cast_add, Nat.cast_one]
                  have h_val_le_n' : ((k + 1) : ℕ) / 2^n ≤ (n : ℝ) := by rw [← h_k1_eq]; exact h_val_le_n
                  calc (f x).toReal < (↑k + 1) / 2^n := h_toReal_lt
                    _ = ((k + 1) : ℕ) / 2^n := by rw [h_k1_eq]
                    _ ≤ n := h_val_le_n'
              · -- h_fx_le_n : ¬(f x ≤ n), i.e., n < f x
                push_neg at h_fx_le_n
                -- min(f x, n) = n when f x > n
                have h_min : min (f x) ↑n = ↑n := min_eq_right (le_of_lt h_fx_le_n)
                -- h_toReal_lt : (min (f x) n).toReal < (↑k + 1) / 2^n
                -- Becomes: n.toReal < (↑k + 1) / 2^n
                rw [h_min] at h_toReal_lt
                have h_n_toReal : (↑n : EReal).toReal = (n : ℝ) := by
                  rw [show (↑n : EReal) = ↑(n : ℝ) from EReal.coe_natCast.symm, EReal.toReal_coe]
                rw [h_n_toReal] at h_toReal_lt
                exfalso; linarith [h_val_le_n]
            have h_min_eq : min (f x) ↑n = f x := min_eq_left (le_of_lt h_fx_lt_n)
            rw [h_min_eq] at h_ge h_toReal_lt
            have h_fx_ne_top : f x ≠ ⊤ := by intro heq; rw [heq] at h_fx_lt_n; exact not_lt.mpr le_top h_fx_lt_n
            have h_fx_ne_bot : f x ≠ ⊥ := by intro heq; rw [h_min_eq] at hbot; exact hbot heq
            refine ⟨hnorm, ?_, ?_⟩
            · -- Show f x ≥ k / 2^n
              rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot]
              have hk_coe : ((k : ℕ) : EReal) = ((k : ℕ) : ℝ) := EReal.coe_natCast.symm
              have h2n_coe : ((2^n : ℕ) : EReal) = ((2^n : ℕ) : ℝ) := EReal.coe_natCast.symm
              simp only [← EReal.coe_div, ge_iff_le, EReal.coe_le_coe_iff]; exact h_ge
            · -- Show f x < (k + 1) / 2^n
              rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot]
              have h_k1_eq : (↑k + 1 : ℝ) = ((k + 1) : ℕ) := by simp only [Nat.cast_add, Nat.cast_one]
              have h_toReal_lt' : (f x).toReal < ((k + 1) : ℕ) / 2^n := by rw [← h_k1_eq]; exact h_toReal_lt
              simp only [← EReal.coe_div, EReal.coe_lt_coe_iff]; exact h_toReal_lt'
        · intro ⟨hnorm, hfx_ge, hfx_lt⟩
          refine ⟨hnorm, ?_⟩
          rw [hv_eq]; simp only [approx_fn, hnorm, ite_true]
          -- From hfx_lt: f x < (k+1)/2^n ≤ n, so min(f x, n) = f x
          have h_val_le_n : ((k + 1) : ℝ) / 2^n ≤ n := by
            have h1 : (k + 1 : ℕ) ≤ n * 2^n := by omega
            have h1' : ((k + 1) : ℝ) ≤ (n * 2^n : ℝ) := by exact_mod_cast h1
            calc ((k + 1) : ℝ) / 2^n ≤ (n * 2^n : ℝ) / 2^n := div_le_div_of_nonneg_right h1' (le_of_lt h2n_pos)
              _ = n := by field_simp
          have h_fx_lt_n : f x < ↑n := by
            -- f x < ↑↑(k+1) / ↑(2^n) and (k+1)/2^n ≤ n, so f x < n
            -- h_in_real lifts h_val_le_n to the correct form
            have h_in_real : (((k + 1 : ℕ) : ℝ) / ((2^n : ℕ) : ℝ)) ≤ (n : ℝ) := by
              simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
              exact h_val_le_n
            -- Use refine to infer goal type from hfx_lt (which has ↑(2^n) as coerced Nat)
            refine lt_of_lt_of_le hfx_lt ?h_bound
            -- Goal now: ↑↑(k+1) / ↑(2^n) ≤ ↑n (with ↑(2^n) as coerced Nat!)
            case h_bound =>
              simp_rw [EReal.coe_natCast.symm, ← EReal.coe_div, EReal.coe_le_coe_iff]
              convert h_in_real using 2
              -- Goal: 2 ^ n = ↑(2 ^ n) in ℝ - Real power vs coerced Nat power
              simp only [Nat.cast_pow, Nat.cast_ofNat]
          have h_min_eq : min (f x) ↑n = f x := min_eq_left (le_of_lt h_fx_lt_n)
          rw [h_min_eq]
          have h_fx_ne_top : f x ≠ ⊤ := by intro heq; rw [heq] at h_fx_lt_n; exact not_lt.mpr le_top h_fx_lt_n
          have h_fx_ne_bot : f x ≠ ⊥ := fun heq => not_le.mpr EReal.bot_lt_zero (heq ▸ hf x)
          split_ifs with hbot' htop'
          · exfalso; exact h_fx_ne_bot hbot'
          · exfalso
            have h_fx_ge : f x ≥ 0 := hf x
            exact not_lt.mpr (EReal.toReal_nonneg h_fx_ge) htop'
          · -- Show floor((f x).toReal * 2^n) = k
            rw [← EReal.coe_div] at hfx_ge hfx_lt
            have h_ge' : (f x).toReal ≥ (k : ℝ) / 2^n := by
              rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot] at hfx_ge
              exact EReal.coe_le_coe_iff.mp hfx_ge
            have h_lt' : (f x).toReal < ((k + 1) : ℝ) / 2^n := by
              rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot] at hfx_lt
              rw [Nat.cast_add_one] at hfx_lt
              exact EReal.coe_lt_coe_iff.mp hfx_lt
            have h_prod_ge : (f x).toReal * 2^n ≥ k := by
              calc (f x).toReal * 2^n ≥ ((k : ℝ) / 2^n) * 2^n := by nlinarith
                _ = k := by field_simp
            have h_prod_lt : (f x).toReal * 2^n < k + 1 := by
              calc (f x).toReal * 2^n < (((k + 1) : ℝ) / 2^n) * 2^n := by nlinarith
                _ = k + 1 := by field_simp
            have h_floor : ⌊(f x).toReal * 2 ^ n⌋₊ = k := by
              have h_nonneg : 0 ≤ (f x).toReal * 2 ^ n := by
                apply mul_nonneg
                · exact EReal.toReal_nonneg (hf x)
                · exact pow_nonneg (by norm_num) n
              rw [Nat.floor_eq_iff h_nonneg]
              constructor <;> linarith
            have h1 : ((2^n : ℕ) : EReal) = ((2^n : ℕ) : ℝ) := EReal.coe_natCast.symm
            have h2 : ((k : ℕ) : EReal) = ((k : ℕ) : ℝ) := EReal.coe_natCast.symm
            simp only [h_floor, ← EReal.coe_div]
      rw [h_eq]
      exact ball_leb.inter (h_le.inter h_lt)

  -- Outside ball case: {‖x‖ > n} ∩ {approx_fn = v} = {‖x‖ > n} if v = 0, else ∅
  · have h_eq : {x | ‖x‖ > (n:ℝ)} ∩ {x | approx_fn f n x = v} =
        if v = 0 then {x | ‖x‖ > (n:ℝ)} else ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, approx_fn]
      constructor
      · intro ⟨hn, hv⟩
        have hn' : ¬ ‖x‖ ≤ (n:ℝ) := not_le.mpr hn
        simp only [hn', ite_false] at hv
        split_ifs <;> [exact hn; exact absurd hv.symm ‹_›]
      · intro h
        split_ifs at h with hv0
        · have hn : ‖x‖ > (n:ℝ) := h
          have hn' : ¬ ‖x‖ ≤ (n:ℝ) := not_le.mpr hn
          exact ⟨hn, by simp only [hn', ite_false, hv0]⟩
        · exact absurd h id
    rw [h_eq]
    split_ifs <;> [exact outside_leb; exact LebesgueMeasurable.empty]

-- The main construction lemma
private lemma v_to_xi_imp_iv (hf : Unsigned f) (hvi : stmt_vi f) (hvii : stmt_vii f) :
    stmt_iv f := by
  -- Construct f_n(x) = largest k·2^{-n} ≤ min(f(x), n) when |x| ≤ n, else 0
  use approx_fn f
  constructor
  · -- Each approx_fn f n is a simple function, bounded, with finite measure support
    intro n
    constructor
    · -- UnsignedSimpleFunction (approx_fn f n)
      -- Strategy: use the indicator sum representation directly
      -- approx_fn f n = sum over k from 0 to n*2^n of (k/2^n) • indicator{approx_fn f n = k/2^n}
      let K := n * 2^n + 1
      let c : Fin K → EReal := fun i => if i.val = n * 2^n then n else ((i.val : ℕ) : ℝ) / (2^n : ℝ)
      let E : Fin K → Set (EuclideanSpace' d) := fun i => {x | approx_fn f n x = c i}
      use K, c, E
      constructor
      · intro i
        constructor
        · -- LebesgueMeasurable (E i) - Use the helper lemma
          simp only [E]
          exact approx_fn_levelset_LebesgueMeasurable hf hvi hvii n (c i)
        · -- c i ≥ 0
          simp only [c]
          split_ifs with hi
          · exact EReal.coe_nonneg.mpr (Nat.cast_nonneg n)
          · have h2n_pos : (2^n : ℝ) > 0 := pow_pos (by norm_num) n
            have h_nonneg : (0 : ℝ) ≤ (i.val : ℝ) / 2^n := div_nonneg (Nat.cast_nonneg i.val) (le_of_lt h2n_pos)
            exact EReal.coe_nonneg.mpr h_nonneg
      · -- approx_fn f n = sum c i • indicator (E i)
        ext x
        simp only [Finset.sum_apply, Pi.smul_apply, EReal.indicator]
        -- Find which i has x ∈ E i
        obtain ⟨k, hk_bound, hk_eq⟩ := approx_fn_values f hf n x
        have h_unique : ∃! i : Fin K, x ∈ E i := by
          by_cases hk_max : k = n * 2^n
          · use ⟨n * 2^n, by omega⟩
            simp only [E, c, Set.mem_setOf_eq]
            constructor
            · simp only [hk_max] at hk_eq
              simp only [ite_true]
              rw [hk_eq]
              -- Use helper lemma, then normalize coercions
              convert mul_pow2_div_pow2_eq n using 2
              simp only [← EReal.coe_natCast, Nat.cast_pow, Nat.cast_ofNat, EReal.coe_pow]
            · intro j hj
              -- hj : approx_fn f n x = if ↑j = n * 2^n then ↑n else ↑↑↑j / ↑(2^n)
              -- The simp didn't make progress because E is not in scope for hj after previous simp
              ext; simp only
              by_cases hj_max : j.val = n * 2^n
              · exact hj_max
              · -- j.val ≠ n*2^n, but we'll show they must be equal from hj and hk_eq
                simp only [hj_max, ↓reduceIte] at hj
                rw [hk_max] at hk_eq
                exfalso; apply hj_max
                have h_eq_ereal : (((j.val : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                                  (((n * 2^n : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) := by
                  convert hj.symm.trans hk_eq using 2 <;> norm_cast
                exact ereal_div_pow2_eq_imp_eq j.val (n * 2^n) n h_eq_ereal
          · use ⟨k, by omega⟩
            simp only [E, c, Set.mem_setOf_eq]
            constructor
            · have h_c_val : (if k = n * 2^n then (n : EReal) else ((k : ℕ) : ℝ) / (2^n : ℝ)) = ((k : ℕ) : ℝ) / (2^n : ℝ) := by simp [hk_max]
              simp only [h_c_val]
              exact hk_eq
            · intro j hj
              -- hj already has the expanded form after intro
              ext
              by_cases hj_max : j.val = n * 2^n
              · -- j.val = n*2^n but k ≠ n*2^n: k/2^n = n = (n*2^n)/2^n, contradiction
                simp only [hj_max, ↓reduceIte] at hj
                have h_k_val : (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) = (n : EReal) := by
                  convert hk_eq.symm.trans hj using 2; all_goals norm_cast
                have h_eq : (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                            (((n * 2^n : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) := by
                  rw [h_k_val]; convert (mul_pow2_div_pow2_eq n).symm using 2
                exact absurd (ereal_div_pow2_eq_imp_eq k (n * 2^n) n h_eq) hk_max
              · -- Both j and k are not n*2^n
                simp only [hj_max, ↓reduceIte] at hj
                have h_eq' : (((j.val : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                             (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) := by
                  convert hj.symm.trans hk_eq using 2 <;> norm_cast
                exact ereal_div_pow2_eq_imp_eq j.val k n h_eq'
        -- Now use the unique i to simplify the sum
        have h_mem : x ∈ E (h_unique.choose) := h_unique.choose_spec.1
        rw [Finset.sum_eq_single h_unique.choose]
        · -- h_mem : x ∈ E (h_unique.choose) means approx_fn f n x = c (h_unique.choose)
          -- indicator = 1, so goal is approx_fn f n x = c (...) • 1 = c (...)
          simp only [Real.EReal_fun, Set.indicator'_of_mem h_mem, EReal.coe_one, smul_eq_mul, mul_one]
          exact h_mem
        · intro b hb_mem hb_ne
          have h_not_mem : x ∉ E b := by
            intro hcontra
            have h_eq := h_unique.choose_spec.2 b hcontra
            exact hb_ne h_eq
          simp only [Real.EReal_fun, Set.indicator'_of_notMem h_not_mem,
                     EReal.coe_zero, smul_zero]
        · intro hcontra
          exact absurd (Finset.mem_univ _) hcontra
    constructor
    · -- EReal.BoundedFunction (approx_fn f n)
      use n
      intro x
      obtain ⟨k, hk_bound, hk_eq⟩ := approx_fn_values f hf n x
      rw [hk_eq]
      have h2n_pos : (2^n : ℝ) > 0 := pow_pos (by norm_num) n
      have h2n_nonneg : (0 : ℝ) ≤ 2^n := le_of_lt h2n_pos
      have h_val_nonneg : (0 : ℝ) ≤ (k : ℝ) / 2^n := div_nonneg (Nat.cast_nonneg k) h2n_nonneg
      have h_val_le_n : (k : ℝ) / 2^n ≤ n := by
        have h1 : (k : ℝ) ≤ n * 2^n := by exact_mod_cast hk_bound
        calc (k : ℝ) / 2^n ≤ (n * 2^n) / 2^n := by apply div_le_div_of_nonneg_right h1 h2n_nonneg
          _ = n := by field_simp
      -- The value k/2^n as a real
      let val : ℝ := (k : ℝ) / 2^n
      -- Direct proof - just use native simp with the relevant lemmas
      simp only [← EReal.coe_div, EReal.abs_def, abs_of_nonneg h_val_nonneg]
      calc ENNReal.ofReal val
        ≤ ENNReal.ofReal n := ENNReal.ofReal_le_ofReal h_val_le_n
        _ = ↑n := ENNReal.ofReal_natCast n
    · -- FiniteMeasureSupport (approx_fn f n)
      -- Support ⊆ {|x| ≤ n}, which has finite Lebesgue measure
      -- Closed balls are compact, so have finite measure
      have h_support_sub : Support (approx_fn f n) ⊆ {x | ‖x‖ ≤ n} := by
        intro x hx
        simp only [Support] at hx
        by_contra h
        simp only [Set.mem_setOf_eq, not_le] at h
        -- When ‖x‖ > n, approx_fn f n x = 0
        have h' : ¬(‖x‖ ≤ (n : ℝ)) := not_le.mpr h
        have h_eq : approx_fn f n x = 0 := by
          unfold approx_fn
          simp only [h', ite_false]
        exact hx h_eq
      have h_ball_eq : {x : EuclideanSpace' d | ‖x‖ ≤ n} = Metric.closedBall 0 n := by
        ext x; simp [Metric.closedBall, dist_zero_right]
      have h_compact : IsCompact (Metric.closedBall (0 : EuclideanSpace' d) n) :=
        isCompact_closedBall 0 n
      have h_finite : Lebesgue_outer_measure (Metric.closedBall (0 : EuclideanSpace' d) n) ≠ ⊤ :=
        Lebesgue_outer_measure.finite_of_compact h_compact
      calc Lebesgue_measure (Support (approx_fn f n))
          ≤ Lebesgue_measure {x | ‖x‖ ≤ n} := Lebesgue_outer_measure.mono h_support_sub
        _ = Lebesgue_measure (Metric.closedBall 0 n) := by rw [h_ball_eq]
        _ < ⊤ := lt_top_iff_ne_top.mpr h_finite
  constructor
  · -- Monotonicity: approx_fn f m x ≤ approx_fn f n x for m ≤ n
    intro x m n hmn
    -- Key insight: as n increases, the ball grows and approximation gets finer
    unfold approx_fn
    by_cases hm : ‖x‖ ≤ m
    · -- |x| ≤ m ≤ n
      have hn : ‖x‖ ≤ n := le_trans (by exact_mod_cast hm) (Nat.cast_le.mpr hmn)
      simp only [hm, hn, ite_true]
      -- Both are non-trivial, need to compare the floor values
      -- approx_fn f m x approximates min(f x, m) and approx_fn f n x approximates min(f x, n)
      -- Since min(f x, m) ≤ min(f x, n) and approximation gets better, we have monotonicity
      -- First eliminate the impossible cases using unsigned property
      have hm_ne_bot : min (f x) ↑m ≠ ⊥ := by
        intro h
        have h1 : 0 ≤ min (f x) ↑m := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg m))
        rw [h] at h1; exact not_le.mpr EReal.bot_lt_zero h1
      have hn_ne_bot : min (f x) ↑n ≠ ⊥ := by
        intro h
        have h1 : 0 ≤ min (f x) ↑n := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
        rw [h] at h1; exact not_le.mpr EReal.bot_lt_zero h1
      have hm_ne_top : min (f x) ↑m ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top m) (min_le_right _ _)
      have hn_ne_top : min (f x) ↑n ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top n) (min_le_right _ _)
      have hm_nonneg : 0 ≤ (min (f x) ↑m).toReal := by
        have h1 : 0 ≤ min (f x) ↑m := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg m))
        exact EReal.toReal_nonneg h1
      have hn_nonneg : 0 ≤ (min (f x) ↑n).toReal := by
        have h1 : 0 ≤ min (f x) ↑n := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
        exact EReal.toReal_nonneg h1
      simp only [hm_ne_bot, hm_ne_top, hn_ne_bot, hn_ne_top, ite_false]
      simp only [not_lt.mpr hm_nonneg, not_lt.mpr hn_nonneg, ite_false]
      -- Now we need: floor(t_m * 2^m) / 2^m ≤ floor(t_n * 2^n) / 2^n
      -- Key: t_m ≤ t_n and floor approximation from below
      set t_m := (min (f x) ↑m).toReal with ht_m
      set t_n := (min (f x) ↑n).toReal with ht_n
      have h_tm_le_tn : t_m ≤ t_n := by
        have h1 : min (f x) ↑m ≤ min (f x) ↑n := by
          apply min_le_min_left
          exact EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hmn)
        exact EReal.toReal_le_toReal h1 hm_ne_bot hn_ne_top
      have h2m_pos : (0 : ℝ) < 2^m := pow_pos (by norm_num) m
      have h2n_pos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
      -- floor(t_m * 2^m) / 2^m ≤ t_m ≤ t_n
      have h_floor_le_tm : (⌊t_m * 2^m⌋₊ : ℝ) / 2^m ≤ t_m := by
        have h1 : (⌊t_m * 2^m⌋₊ : ℝ) ≤ t_m * 2^m := Nat.floor_le (mul_nonneg hm_nonneg (le_of_lt h2m_pos))
        rw [div_le_iff₀ h2m_pos]
        linarith
      -- floor(t_n * 2^n) / 2^n is the largest multiple of 2^{-n} ≤ t_n
      -- Since floor(t_m * 2^m) / 2^m is a multiple of 2^{-m}, hence of 2^{-n},
      -- and it's ≤ t_m ≤ t_n, we have the result
      have h_lhs_mul : ∃ k : ℕ, (⌊t_m * 2^m⌋₊ : ℝ) / 2^m = (k : ℝ) / 2^n := by
        use ⌊t_m * 2^m⌋₊ * 2^(n - m)
        have h_pow : (2 : ℝ)^m * 2^(n - m) = 2^n := by
          rw [← pow_add]; congr 1; omega
        field_simp
        ring_nf
        rw [← h_pow]
        push_cast; ring
      obtain ⟨k, hk⟩ := h_lhs_mul
      -- k / 2^n ≤ t_m ≤ t_n, so k / 2^n ≤ floor(t_n * 2^n) / 2^n
      have h_k_le_tn : (k : ℝ) / 2^n ≤ t_n := by
        rw [← hk]; exact le_trans h_floor_le_tm h_tm_le_tn
      have h_k_le_floor : k ≤ ⌊t_n * 2^n⌋₊ := by
        have h1 : (k : ℝ) ≤ t_n * 2^n := by
          rw [div_le_iff₀ h2n_pos] at h_k_le_tn; linarith
        exact Nat.le_floor h1
      -- Final result in ℝ: floor(t_m * 2^m) / 2^m ≤ floor(t_n * 2^n) / 2^n
      have h_real : (⌊t_m * 2^m⌋₊ : ℝ) / 2^m ≤ (⌊t_n * 2^n⌋₊ : ℝ) / 2^n := by
        calc (⌊t_m * 2^m⌋₊ : ℝ) / 2^m = (k : ℝ) / 2^n := hk
             _ ≤ (⌊t_n * 2^n⌋₊ : ℝ) / 2^n := by
               apply div_le_div_of_nonneg_right _ (le_of_lt h2n_pos)
               exact_mod_cast h_k_le_floor
      -- Coerce to EReal
      exact EReal.coe_le_coe_iff.mpr h_real
    · -- |x| > m, so approx_fn f m x = 0
      simp only [hm, ite_false]
      -- approx_fn f n x ≥ 0 by construction (it's unsigned)
      by_cases hn : ‖x‖ ≤ n
      · simp only [hn, ite_true]
        -- Need: 0 ≤ (if bot then 0, if top then n, if neg then 0, else floor/2^n)
        split_ifs with h_bot h_top h_neg
        · exact le_refl 0  -- 0 ≤ 0
        · exact EReal.coe_nonneg.mpr (Nat.cast_nonneg n)  -- 0 ≤ n
        · exact le_refl 0  -- 0 ≤ 0
        · -- 0 ≤ floor(...) / 2^n
          apply EReal.coe_nonneg.mpr
          apply div_nonneg (Nat.cast_nonneg _)
          exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) n)
      · simp only [hn, ite_false]
        rfl
  · -- Convergence: f x = iSup (fun n => approx_fn f n x)
    intro x
    -- Case analysis: f x = ⊤ or f x < ⊤
    rcases eq_top_or_lt_top (f x) with hfx_top | hfx_lt_top
    · -- Case 1: f x = ⊤
      rw [hfx_top, eq_comm, iSup_eq_top]
      intro b hb
      -- For b < ⊤, find n with approx_fn f n x > b
      rcases eq_bot_or_bot_lt b with rfl | hb_bot
      · -- b = ⊥: any n works since approx_fn f n x ≥ 0 > ⊥
        use max 1 (Nat.ceil ‖x‖)
        exact lt_of_lt_of_le EReal.bot_lt_zero (approx_fn_nonneg f hf _ x)
      · -- b > ⊥ and b < ⊤, so b is a finite real
        induction b using EReal.rec with
        | bot => exact (not_lt_bot hb_bot).elim
        | top => exact (lt_irrefl _ hb).elim
        | coe b' =>
          -- Choose n > b' and n ≥ ‖x‖
          let N := max (Nat.ceil b' + 1) (Nat.ceil ‖x‖)
          use N
          have h_norm : ‖x‖ ≤ N := by
            calc ‖x‖ ≤ Nat.ceil ‖x‖ := Nat.le_ceil _
                 _ ≤ N := by exact_mod_cast Nat.le_max_right _ _
          -- approx_fn f N x = floor(N * 2^N) / 2^N = N when f x = ⊤
          have hN_ne_bot : ((N : ℕ) : EReal) ≠ ⊥ := EReal.coe_ne_bot N
          have hN_ne_top : ((N : ℕ) : EReal) ≠ ⊤ := EReal.coe_ne_top N
          have hN_nonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          have hN_toReal : ((N : ℕ) : EReal).toReal = N := EReal.toReal_coe N
          simp only [approx_fn, h_norm, ite_true, hfx_top, min_top_left,
                     hN_ne_bot, hN_ne_top, ite_false, hN_toReal, not_lt.mpr hN_nonneg]
          -- floor(N * 2^N) / 2^N = N
          have h_floor_eq : (⌊(N : ℝ) * 2^N⌋₊ : ℝ) / 2^N = N := by
            have h_nat_mul : (N : ℝ) * (2 : ℝ)^N = ↑(N * 2^N) := by push_cast; ring
            rw [h_nat_mul, Nat.floor_natCast]
            field_simp; push_cast; ring
          simp only [← EReal.coe_div, EReal.coe_lt_coe_iff, h_floor_eq]
          calc b' ≤ Nat.ceil b' := Nat.le_ceil _
               _ < (Nat.ceil b' : ℝ) + 1 := lt_add_one _
               _ ≤ N := by exact_mod_cast Nat.le_max_left _ _
    · -- Case 2: f x < ⊤ (finite)
      have hfx_not_bot : f x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf x))
      -- f x is finite: not ⊥ (by unsigned) and not ⊤ (by hypothesis)
      set r := (f x).toReal with hr_def
      have hr_eq : f x = r := (EReal.coe_toReal hfx_lt_top.ne hfx_not_bot).symm
      rw [hr_eq]
      -- f x = r (finite nonnegative real)
      have hr_nonneg : r ≥ 0 := by
        have h := hf x
        rw [hr_eq] at h
        exact EReal.coe_nonneg.mp h
      -- Use floor_approx_iSup_eq: for large n, approx_fn f n x = floor(r * 2^n) / 2^n
      apply le_antisymm
      · -- r ≤ iSup (approx_fn)
        -- Strategy: use floor_approx_iSup_eq and show that for large n, floor_approx ≤ approx_fn
        rw [floor_approx_iSup_eq r hr_nonneg]
        apply iSup_le
        intro n
        -- Find N ≥ n with ‖x‖ ≤ N and r ≤ N
        let N := max n (max (Nat.ceil ‖x‖) (Nat.ceil r))
        have hnN : n ≤ N := Nat.le_max_left _ _
        have h_norm_N : ‖x‖ ≤ N := by
          calc ‖x‖ ≤ Nat.ceil ‖x‖ := Nat.le_ceil _
               _ ≤ max (Nat.ceil ‖x‖) (Nat.ceil r) := by exact_mod_cast le_max_left _ _
               _ ≤ N := by exact_mod_cast le_max_right _ _
        have hrN : r ≤ N := by
          calc r ≤ Nat.ceil r := Nat.le_ceil _
               _ ≤ max (Nat.ceil ‖x‖) (Nat.ceil r) := by exact_mod_cast le_max_right _ _
               _ ≤ N := by exact_mod_cast le_max_right _ _
        -- approx_fn f N x = floor(r * 2^N) / 2^N
        have h_approx_N : approx_fn f N x = (((⌊r * 2^N⌋₊ : ℕ) : ℝ) / (2^N : ℝ) : EReal) :=
          approx_fn_eq_floor_when_finite f hf N x h_norm_N r hr_eq hr_nonneg hrN
        -- floor(r * 2^n) / 2^n ≤ floor(r * 2^N) / 2^N (monotonicity)
        have h2n_pos : (2 : ℝ)^n > 0 := pow_pos (by norm_num) n
        have h2N_pos : (2 : ℝ)^N > 0 := pow_pos (by norm_num) N
        have h_floor_n_le_r : (⌊r * 2^n⌋₊ : ℝ) / 2^n ≤ r := by
          rw [div_le_iff₀ h2n_pos]
          exact Nat.floor_le (mul_nonneg hr_nonneg (le_of_lt h2n_pos))
        have h_mono : (⌊r * 2^n⌋₊ : ℝ) / 2^n ≤ (⌊r * 2^N⌋₊ : ℝ) / 2^N := by
          -- floor(r * 2^n) / 2^n is a multiple of 2^{-n}, hence of 2^{-N}
          have h_lhs_mul : ∃ k : ℕ, (⌊r * 2^n⌋₊ : ℝ) / 2^n = (k : ℝ) / 2^N := by
            use ⌊r * 2^n⌋₊ * 2^(N - n)
            have h_pow : (2 : ℝ)^n * 2^(N - n) = 2^N := by
              rw [← pow_add]; congr 1; omega
            field_simp
            ring_nf
            rw [← h_pow]
            push_cast; ring
          obtain ⟨k, hk⟩ := h_lhs_mul
          rw [hk]
          apply div_le_div_of_nonneg_right _ (le_of_lt h2N_pos)
          have h_k_le_r : (k : ℝ) / 2^N ≤ r := by rw [← hk]; exact h_floor_n_le_r
          have h_k_le_floor : k ≤ ⌊r * 2^N⌋₊ := by
            have h1 : (k : ℝ) ≤ r * 2^N := by
              rw [div_le_iff₀ h2N_pos] at h_k_le_r; linarith
            exact Nat.le_floor h1
          exact_mod_cast h_k_le_floor
        -- Use the monotonicity and connect to iSup
        have h_le_approx : (((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) ≤ approx_fn f N x := by
          rw [h_approx_N]
          exact EReal.coe_le_coe_iff.mpr h_mono
        calc (((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal)
            ≤ approx_fn f N x := h_le_approx
          _ ≤ ⨆ m, approx_fn f m x := le_iSup (fun m => approx_fn f m x) N
      · -- iSup (approx_fn) ≤ r
        apply iSup_le
        intro n
        by_cases h_norm : ‖x‖ ≤ n
        · simp only [approx_fn, h_norm, ite_true, hr_eq]
          -- min r n ≤ r, and floor approx ≤ min r n
          have h_min_ne_bot : min (r : EReal) n ≠ ⊥ := by
            intro h
            rcases min_eq_bot.mp h with hr | hn
            · exact EReal.coe_ne_bot r hr
            · exact EReal.coe_ne_bot n hn
          have h_min_ne_top : min (r : EReal) n ≠ ⊤ :=
            ne_top_of_le_ne_top (EReal.coe_ne_top n) (min_le_right _ _)
          have h_min_nonneg : (min (r : EReal) n).toReal ≥ 0 := by
            apply EReal.toReal_nonneg
            exact le_min (EReal.coe_nonneg.mpr hr_nonneg) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
          simp only [h_min_ne_bot, ite_false, h_min_ne_top, not_lt.mpr h_min_nonneg]
          apply EReal.coe_le_coe_iff.mpr
          have h2n_pos : (2 : ℝ)^n > 0 := pow_pos (by norm_num) n
          have h_floor_le : (⌊(min (r : EReal) n).toReal * 2^n⌋₊ : ℝ) / 2^n ≤ (min (r : EReal) n).toReal := by
            rw [div_le_iff₀ h2n_pos]
            exact Nat.floor_le (mul_nonneg h_min_nonneg (le_of_lt h2n_pos))
          have h_min_le_r : (min (r : EReal) n).toReal ≤ r := by
            have h1 : min (r : EReal) n ≤ r := min_le_left _ _
            have h2 := EReal.toReal_le_toReal h1 h_min_ne_bot (EReal.coe_ne_top r)
            simp only [EReal.toReal_coe] at h2
            exact h2
          exact le_trans h_floor_le h_min_le_r
        · simp only [approx_fn, h_norm, ite_false]
          exact EReal.coe_nonneg.mpr hr_nonneg

end UnsignedMeasurable.TFAE_helpers

/-- Lemma 1.3.9 (Equivalent notions of measurability).  Some slight changes to the statement have been made to make the claims cleaner to state -/
theorem UnsignedMeasurable.TFAE {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f):
    [
      UnsignedMeasurable f,
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (∀ x, Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))),
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f),
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n) ∧  EReal.BoundedFunction (g n) ∧ FiniteMeasureSupport (g n)) ∧ (∀ x, Monotone (fun n ↦ g n x)) ∧ (∀ x, f x = iSup (fun n ↦ g n x)),
      ∀ t, LebesgueMeasurable {x | f x > t},
      ∀ t, LebesgueMeasurable {x | f x ≥ t},
      ∀ t, LebesgueMeasurable {x | f x < t},
      ∀ t, LebesgueMeasurable {x | f x ≤ t},
      ∀ I:BoundedInterval, LebesgueMeasurable (f⁻¹' (Real.toEReal '' I.toSet)),
      ∀ U: Set EReal, IsOpen U → LebesgueMeasurable (f⁻¹' U),
      ∀ K: Set EReal, IsClosed K → LebesgueMeasurable (f⁻¹' K)
    ].TFAE := by
  open UnsignedMeasurable.TFAE_helpers in
  -- Establish the implication graph
  tfae_have 1 ↔ 2 := i_iff_ii hf
  tfae_have 2 → 3 := ii_imp_iii
  tfae_have 4 → 2 := iv_imp_ii
  tfae_have 3 → 5 := iii_imp_v
  tfae_have 5 → 6 := v_imp_vi
  tfae_have 6 → 5 := vi_imp_v
  tfae_have 5 → 8 := v_imp_viii
  tfae_have 6 → 7 := vi_imp_vii
  tfae_have 7 → 6 := vii_imp_vi
  tfae_have 8 → 5 := viii_imp_v
  tfae_have 5 → 9 := fun h => v_to_viii_imp_ix h (v_imp_vi h) (vi_imp_vii (v_imp_vi h)) (v_imp_viii h)
  tfae_have 9 → 10 := ix_imp_x hf
  tfae_have 10 ↔ 11 := x_iff_xi
  tfae_have 10 → 7 := x_imp_vii
  tfae_have 5 → 4 := fun hv => v_to_xi_imp_iv hf (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv))
  tfae_finish

/-- Exercise 1.3.3(i) -/
theorem Continuous.UnsignedMeasurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Continuous f) (hnonneg: Unsigned f): UnsignedMeasurable f := by sorry

/-- Exercise 1.3.3(ii) -/
theorem UnsignedSimpleFunction.unsignedMeasurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f): UnsignedMeasurable f := by sorry

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.sup {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ iSup (fun n ↦ f n x)) := by sorry

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.inf {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ iInf (fun n ↦ f n x)) := by sorry

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.limsup {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ Filter.atTop.limsup (fun n ↦ f n x) ) := by sorry

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.liminf {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ Filter.atTop.liminf (fun n ↦ f n x) ) := by sorry

/-- Exercise 1.3.3(iv) -/
theorem UnsignedMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (heq: AlmostEverywhereEqual f g) : UnsignedMeasurable g := by sorry

/-- Exercise 1.3.3(v) -/
theorem UnsignedMeasurable.aeLimit {d:ℕ} {f: EuclideanSpace' d → EReal} (g: ℕ → EuclideanSpace' d → EReal) (hf: ∀ n, UnsignedMeasurable (g n)) (heq: PointwiseAeConvergesTo g f) : UnsignedMeasurable f := by sorry

/-- Exercise 1.3.3(vi) -/
theorem UnsignedMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {φ: EReal → EReal} (hφ: Continuous φ)  : UnsignedMeasurable (φ ∘ f) := by sorry

/-- Exercise 1.3.3(vii) -/
theorem UnsignedMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g) : UnsignedMeasurable (f + g) := by sorry

def UniformConvergesTo {X:Type*} (f: ℕ → X → EReal) (g: X → EReal) : Prop := ∀ ε:NNReal, ε > 0 → ∃ N:ℕ, ∀ n ≥ N, ∀ x, f n x > g x - ε ∧ f n x < g x + ε

/-- Exercise 1.3.4 -/
theorem UnsignedMeasurable.bounded_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f) : UnsignedMeasurable f ∧ EReal.BoundedFunction f ↔ ∃ g : ℕ → EuclideanSpace' d → EReal, (∀ n, UnsignedSimpleFunction (g n) ∧ EReal.BoundedFunction (g n)) ∧ UniformConvergesTo g f := by sorry

/-- Exercise 1.3.5 -/
theorem UnsignedSimpleFunction.iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f) : UnsignedSimpleFunction f ↔ UnsignedMeasurable f ∧ Finite (f '' Set.univ) := by sorry

/-- Exercise 1.3.6 -/
theorem UnsignedMeasurable.measurable_graph {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : LebesgueMeasurable { p | ∃ x, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by sorry

/-!
## Remark 1.3.10: Measurable functions can have non-measurable preimages

We construct an example showing that even for a measurable function f: ℝ^d → [0, +∞],
the inverse image f⁻¹(E) of a Lebesgue measurable set E need not be Lebesgue measurable.

**Strategy** (from the textbook):
1. The Cantor set C := {∑ aⱼ 3^{-j} : aⱼ ∈ {0,2}} has measure zero
2. Define f: [0,1] → C by mapping binary digits to ternary: f(∑ bⱼ 2^{-j}) = ∑ 2bⱼ 3^{-j}
3. f is bijective from A (non-terminating binary decimals) onto C, and f is measurable
4. Take non-measurable F ⊆ A (from Vitali construction)
5. E := f(F) ⊆ C is measurable (subset of null set), but f⁻¹(E) = F is non-measurable

**Implementation note**: Our formalization differs slightly from the textbook:
- **Textbook**: f(x) = 0 for dyadic rationals (terminating binary decimals)
- **Our version**: f is defined uniformly for all x ∈ [0,1] using floor-based binary digits

The textbook's f is NOT monotone on [0,1] (e.g., f(0.4) > 0 but f(0.5) = 0).
Our f IS monotone on all of [0,1], which simplifies the measurability proof:
sublevel sets are intervals, hence measurable by Lemma 1.3.9(viii).

Both versions work for the theorem because:
- Both are injective on A (non-dyadic numbers have unique binary expansions)
- Both map [0,1] into CantorSet ∪ {0}
- Both give measurable f with f⁻¹(E) = F non-measurable
-/

/-- Dyadic rationals: numbers of the form k/2^n where k ≤ 2^n.
    These are exactly the real numbers with terminating binary expansions. -/
def DyadicRationals : Set ℝ := {x : ℝ | ∃ (k n : ℕ), x = k / 2^n ∧ k ≤ 2^n}

/-- Dyadic rationals are countable. -/
lemma DyadicRationals.countable : DyadicRationals.Countable := by
  let D' := ⋃ n : ℕ, (fun k : Fin (2^n + 1) => (k : ℝ) / 2^n) '' Set.univ
  have hD'_countable : D'.Countable :=
    Set.countable_iUnion (fun n => Set.Countable.image Set.countable_univ _)
  apply Set.Countable.mono _ hD'_countable
  intro x ⟨k, n, hk, hk_le⟩
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and, D']
  use n
  have hk_lt : k < 2^n + 1 := Nat.lt_succ_of_le hk_le
  exact ⟨⟨k, hk_lt⟩, hk.symm⟩

/-- Binary digit extraction: bⱼ(x) = ⌊2^j · x⌋ mod 2.
    For x ∈ [0,1), this extracts the j-th binary digit.
    Special case: x = 1 has all digits = 1 (1 = 0.111...₂).
    For x ∉ [0,1], all digits are 0. -/
noncomputable def binaryDigit (x : ℝ) (j : ℕ) : ℕ :=
  if x ∈ Set.Ico (0:ℝ) 1 then ⌊(2:ℝ)^j * x⌋₊ % 2
  else if x = 1 then 1
  else 0

/-- Binary digits are in {0, 1}. -/
lemma binaryDigit_le_one (x : ℝ) (j : ℕ) : binaryDigit x j ≤ 1 := by
  simp only [binaryDigit]
  split_ifs with h1 h2 <;> omega

/-- Binary digits of 0 are all 0. -/
lemma binaryDigit_zero (j : ℕ) : binaryDigit 0 j = 0 := by
  simp only [binaryDigit]
  have h0' : (0:ℝ) ∈ Set.Ico 0 1 := ⟨le_refl 0, by norm_num⟩
  rw [if_pos h0']
  simp [mul_zero]

/-- Binary digits of 1 are all 1. -/
lemma binaryDigit_one (j : ℕ) : binaryDigit 1 j = 1 := by
  simp only [binaryDigit, Set.mem_Ico, lt_self_iff_false, and_false, ↓reduceIte]

/-- The full sum ∑_{j≥0} 2·(1/3)^{j+1} = 1. -/
lemma tsum_two_thirds_geometric : ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(j + 1) = 1 := by
  have h1 : ∑' j : ℕ, (1/3:ℝ)^j = (1 - 1/3)⁻¹ :=
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)
  calc ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(j + 1)
      = ∑' j : ℕ, (2/3:ℝ) * (1/3:ℝ)^j := by congr 1; ext j; ring
    _ = (2/3) * ∑' j : ℕ, (1/3:ℝ)^j := by rw [tsum_mul_left]
    _ = (2/3) * (1 - 1/3)⁻¹ := by rw [h1]
    _ = 1 := by norm_num

/-- The tail sum bound: ∑_{j≥k} 2·(1/3)^{j+1} = (1/3)^k. -/
lemma tsum_tail_bound (k : ℕ) :
    ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(k + j + 1) = (1/3:ℝ)^k := by
  have h1 : ∑' j : ℕ, (1/3:ℝ)^j = (1 - 1/3)⁻¹ :=
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)
  calc ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(k + j + 1)
      = ∑' j : ℕ, (2:ℝ) * ((1/3:ℝ)^(k+1) * (1/3:ℝ)^j) := by
        congr 1; ext j; rw [← pow_add]; ring_nf
    _ = (2:ℝ) * (1/3:ℝ)^(k+1) * ∑' j : ℕ, (1/3:ℝ)^j := by
        rw [← tsum_mul_left]; congr 1; ext j; ring
    _ = (2:ℝ) * (1/3:ℝ)^(k+1) * (1 - 1/3)⁻¹ := by rw [h1]
    _ = (1/3:ℝ)^k := by field_simp; ring

/-- Helper: if ⌊2z⌋₊ % 2 = 1 then ⌊2z⌋₊ ≥ 2⌊z⌋₊ + 1 -/
lemma floor_two_mul_odd_ge {z : ℝ} (hz : 0 ≤ z) (hodd : ⌊2 * z⌋₊ % 2 = 1) :
    ⌊2 * z⌋₊ ≥ 2 * ⌊z⌋₊ + 1 := by
  have h_decomp : ⌊2 * z⌋₊ = 2 * (⌊2 * z⌋₊ / 2) + ⌊2 * z⌋₊ % 2 := (Nat.div_add_mod _ _).symm
  rw [hodd] at h_decomp
  have h_div : ⌊2 * z⌋₊ / 2 ≥ ⌊z⌋₊ := by
    have h1 : (2 * ⌊z⌋₊ : ℕ) ≤ ⌊2 * z⌋₊ := by
      have hfloor := Nat.floor_le hz
      apply Nat.le_floor
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linarith
    rw [mul_comm] at h1
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr h1
  omega

/-- Helper: if ⌊2z⌋₊ % 2 = 0 then ⌊2z⌋₊ ≤ 2⌊z⌋₊ -/
lemma floor_two_mul_even_le {z : ℝ} (hz : 0 ≤ z) (heven : ⌊2 * z⌋₊ % 2 = 0) :
    ⌊2 * z⌋₊ ≤ 2 * ⌊z⌋₊ := by
  have h_decomp : ⌊2 * z⌋₊ = 2 * (⌊2 * z⌋₊ / 2) + ⌊2 * z⌋₊ % 2 := (Nat.div_add_mod _ _).symm
  rw [heven, add_zero] at h_decomp
  have h_div : ⌊2 * z⌋₊ / 2 ≤ ⌊z⌋₊ := by
    have h1 : ⌊2 * z⌋₊ < 2 * (⌊z⌋₊ + 1) := by
      have := Nat.lt_floor_add_one z
      have h2 : 2 * z < 2 * (⌊z⌋₊ + 1) := by linarith
      have h3 : (⌊2 * z⌋₊ : ℝ) ≤ 2 * z := Nat.floor_le (mul_nonneg (by norm_num) hz)
      have h4 : (⌊2 * z⌋₊ : ℝ) < 2 * (↑⌊z⌋₊ + 1) := lt_of_le_of_lt h3 h2
      have h5 : (⌊2 * z⌋₊ : ℝ) < 2 * ⌊z⌋₊ + 2 := by linarith
      exact_mod_cast h5
    omega
  omega

/-- Helper: equal mod 2 and equal ⌊z⌋ implies equal ⌊2z⌋ -/
lemma floor_two_mul_eq_of_mod_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h_floor : ⌊x⌋₊ = ⌊y⌋₊) (h_mod : ⌊2 * x⌋₊ % 2 = ⌊2 * y⌋₊ % 2) :
    ⌊2 * x⌋₊ = ⌊2 * y⌋₊ := by
  by_cases hxodd : ⌊2 * x⌋₊ % 2 = 1
  · have hyodd := h_mod ▸ hxodd
    have hx_ge := floor_two_mul_odd_ge hx hxodd
    have hy_ge := floor_two_mul_odd_ge hy hyodd
    have hx_lt : ⌊2 * x⌋₊ < 2 * ⌊x⌋₊ + 2 := by
      have := Nat.lt_floor_add_one x
      have h2 : 2 * x < 2 * (⌊x⌋₊ + 1) := by linarith
      have h3 : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (mul_nonneg (by norm_num) hx)
      have h4 : (⌊2 * x⌋₊ : ℝ) < 2 * ⌊x⌋₊ + 2 := by linarith
      exact_mod_cast h4
    have hy_lt : ⌊2 * y⌋₊ < 2 * ⌊y⌋₊ + 2 := by
      have := Nat.lt_floor_add_one y
      have h2 : 2 * y < 2 * (⌊y⌋₊ + 1) := by linarith
      have h3 : (⌊2 * y⌋₊ : ℝ) ≤ 2 * y := Nat.floor_le (mul_nonneg (by norm_num) hy)
      have h4 : (⌊2 * y⌋₊ : ℝ) < 2 * ⌊y⌋₊ + 2 := by linarith
      exact_mod_cast h4
    omega
  · have hxeven : ⌊2 * x⌋₊ % 2 = 0 := Nat.mod_two_eq_zero_or_one (⌊2 * x⌋₊) |>.resolve_right hxodd
    have hyeven := h_mod ▸ hxeven
    have hx_le := floor_two_mul_even_le hx hxeven
    have hy_le := floor_two_mul_even_le hy hyeven
    have hx_ge : ⌊2 * x⌋₊ ≥ 2 * ⌊x⌋₊ := by
      have h1 : (2 * ⌊x⌋₊ : ℕ) ≤ ⌊2 * x⌋₊ := by
        have hfloor := Nat.floor_le hx
        apply Nat.le_floor
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        linarith
      exact h1
    have hy_ge : ⌊2 * y⌋₊ ≥ 2 * ⌊y⌋₊ := by
      have h1 : (2 * ⌊y⌋₊ : ℕ) ≤ ⌊2 * y⌋₊ := by
        have hfloor := Nat.floor_le hy
        apply Nat.le_floor
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        linarith
      exact h1
    omega

namespace Remark_1_3_10

/-- The properties required of the binary-to-ternary function for this construction.
    The function maps [0,1] into the Cantor set C by converting binary digits to ternary.

    Note: Unlike the textbook (which sets g(x) = 0 for dyadic rationals), our g is defined
    uniformly for all x ∈ [0,1]. This makes g monotone on ALL of [0,1], not just on A. -/
structure BinaryToTernaryProperties (g : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ g x
  bounded : ∀ x, g x ≤ 1
  zero_outside : ∀ x, x ∉ Set.Icc 0 1 → g x = 0  -- g(x) = 0 outside [0,1]
  zero_at_zero : g 0 = 0  -- g(0) = 0 (binary 0.000... maps to ternary 0.000...)
  zero_set_countable : (Set.Icc 0 1 ∩ {x | g x = 0}).Countable  -- {g = 0} ∩ [0,1] = {0}
  monotone_on : MonotoneOn g (Set.Icc 0 1)  -- g is monotone on ALL of [0,1]
  image_in_cantor : g '' (Set.Icc 0 1) ⊆ CantorSet ∪ {0}
  injective_on_nonterminating : ∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧
    (Set.Icc 0 1 \ A).Countable ∧  -- A is co-countable in [0,1]
    Set.InjOn g A ∧                 -- g is injective on A (hence bijective onto g(A) ⊆ C)
    A ∩ DyadicRationals = ∅         -- A excludes dyadic rationals

/-- The binary-to-ternary function: g(x) = ∑_{j≥1} 2·bⱼ(x)·3^{-j} for x ∈ [0,1], else 0. -/
noncomputable def binaryToTernaryFn (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0:ℝ) 1 then
    ∑' j : ℕ, (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
  else 0

/-- The series ∑ 2·bⱼ(x)·3^{-j} is summable for any x. -/
lemma binaryToTernary_summable (x : ℝ) :
    Summable (fun j => (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro j
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    · positivity
  · intro j
    have h1 : (binaryDigit x (j + 1) : ℝ) ≤ 1 := by exact_mod_cast binaryDigit_le_one x (j + 1)
    calc (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
        ≤ (2 * 1) * (1/3:ℝ)^(j + 1) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/3) (j + 1)]
      _ = 2 * (1/3:ℝ)^(j + 1) := by ring
  · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact (h.mul_left 2).comp_injective (fun _ _ h => Nat.succ_injective h)

/-! ### Helper lemmas for monotonicity proof -/

/-- For x ∈ (0, 1), there exists a position where the binary digit is 1. -/
lemma binaryDigit_exists_one_of_pos {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < 1) :
    ∃ j, binaryDigit x (j + 1) = 1 := by
  have hx_Ico : x ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hx_pos, hx_lt⟩
  have hinv_ge_one : 1 ≤ x⁻¹ := Bound.one_le_inv₀ hx_pos (le_of_lt hx_lt)
  have h_pow_exists := exists_nat_pow_near hinv_ge_one (by norm_num : (1:ℝ) < 2)
  obtain ⟨n, hn_le, hn_lt⟩ := h_pow_exists
  have h_pow_unbounded : ∃ j : ℕ, 1 ≤ (2:ℝ)^(j+1) * x := by
    use n
    have h2n_pos : (0:ℝ) < 2^n := by positivity
    calc (1:ℝ) = x⁻¹ * x := (inv_mul_cancel₀ (ne_of_gt hx_pos)).symm
      _ ≤ (2:ℝ)^(n+1) * x := by nlinarith
  let j := Nat.find h_pow_unbounded
  have hj_ge : 1 ≤ (2:ℝ)^(j+1) * x := Nat.find_spec h_pow_unbounded
  have hj_lt : (2:ℝ)^(j+1) * x < 2 := by
    by_cases hj0 : j = 0
    · simp only [hj0, zero_add, pow_one]
      calc 2 * x < 2 * 1 := by nlinarith [hx_Ico.2]
        _ = 2 := by ring
    · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
      have hj_pred : j - 1 < j := Nat.sub_lt hj_pos Nat.one_pos
      have := Nat.find_min h_pow_unbounded hj_pred
      simp only [not_le] at this
      have hj_sub : j - 1 + 1 = j := Nat.sub_add_cancel hj_pos
      rw [hj_sub] at this
      calc (2:ℝ)^(j+1) * x = 2 * ((2:ℝ)^j * x) := by rw [pow_succ]; ring
        _ < 2 * 1 := by nlinarith
        _ = 2 := by ring
  have h_floor_eq : ⌊(2:ℝ)^(j+1) * x⌋₊ = 1 := by
    apply Nat.floor_eq_on_Ico 1
    constructor
    · simp only [Nat.cast_one]; exact hj_ge
    · simp only [Nat.cast_one]; linarith
  exact ⟨j, by simp only [binaryDigit, if_pos hx_Ico, h_floor_eq]⟩

/-- The partial sum bounds x from below: Sₙ(x) ≤ x -/
lemma binaryDigit_partial_sum_le {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (n : ℕ) :
    (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ≤ x := by
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  rw [div_le_iff₀ h2n_pos, mul_comm]
  exact Nat.floor_le (mul_nonneg hx.1 (le_of_lt h2n_pos))

/-- The partial sum bounds x from above: x < Sₙ(x) + 2^{-n} -/
lemma binaryDigit_partial_sum_lt (x : ℝ) (n : ℕ) :
    x < (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n := by
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  have := Nat.lt_floor_add_one ((2:ℝ)^n * x)
  have h1 : (2:ℝ)^n * x < ⌊(2:ℝ)^n * x⌋₊ + 1 := this
  calc x = ((2:ℝ)^n * x) / (2:ℝ)^n := by field_simp
    _ < (⌊(2:ℝ)^n * x⌋₊ + 1 : ℝ) / (2:ℝ)^n := by
        apply div_lt_div_of_pos_right h1 h2n_pos
    _ = (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n := by ring

/-- Key lemma: if bₖ(x) = 1, then x ≥ ⌊2^k * x⌋₊ / 2^k + 2^{-(k+1)} -/
lemma binaryDigit_one_implies_lower_bound {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (k : ℕ)
    (hbk : binaryDigit x (k + 1) = 1) :
    (⌊(2:ℝ)^k * x⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1) ≤ x := by
  simp only [binaryDigit, if_pos hx] at hbk
  have heq : (2:ℝ)^(k+1) * x = 2 * ((2:ℝ)^k * x) := by ring
  have h_floor_odd : ⌊2 * ((2:ℝ)^k * x)⌋₊ % 2 = 1 := by rw [← heq]; exact hbk
  have h2k1_pos : (0:ℝ) < 2^(k+1) := by positivity
  have h2k1_nonneg : (0:ℝ) ≤ 2^(k+1) := le_of_lt h2k1_pos
  have hx_nonneg : 0 ≤ (2:ℝ)^k * x := mul_nonneg (by positivity) hx.1
  have h_floor_rel : ⌊(2:ℝ)^(k+1) * x⌋₊ ≥ 2 * ⌊(2:ℝ)^k * x⌋₊ + 1 := by
    rw [heq]
    exact floor_two_mul_odd_ge hx_nonneg h_floor_odd
  calc (⌊(2:ℝ)^k * x⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1)
      = (2 * ⌊(2:ℝ)^k * x⌋₊ + 1) / (2:ℝ)^(k + 1) := by field_simp; ring
    _ ≤ (⌊(2:ℝ)^(k+1) * x⌋₊ : ℝ) / (2:ℝ)^(k + 1) := by
        apply div_le_div_of_nonneg_right _ h2k1_nonneg
        exact_mod_cast h_floor_rel
    _ ≤ x := binaryDigit_partial_sum_le hx (k + 1)

/-- Key lemma: if bₖ(y) = 0, then y < ⌊2^k * y⌋₊ / 2^k + 2^{-(k+1)} -/
lemma binaryDigit_zero_implies_upper_bound {y : ℝ} (hy : y ∈ Set.Ico (0:ℝ) 1) (k : ℕ)
    (hbk : binaryDigit y (k + 1) = 0) :
    y < (⌊(2:ℝ)^k * y⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1) := by
  simp only [binaryDigit, if_pos hy] at hbk
  have heq : (2:ℝ)^(k+1) * y = 2 * ((2:ℝ)^k * y) := by ring
  have h_floor_even : ⌊2 * ((2:ℝ)^k * y)⌋₊ % 2 = 0 := by rw [← heq]; exact hbk
  have h2k1_pos : (0:ℝ) < 2^(k+1) := by positivity
  have h2k1_nonneg : (0:ℝ) ≤ 2^(k+1) := le_of_lt h2k1_pos
  have hy_nonneg : 0 ≤ (2:ℝ)^k * y := mul_nonneg (by positivity) hy.1
  have h_floor_rel : ⌊(2:ℝ)^(k+1) * y⌋₊ ≤ 2 * ⌊(2:ℝ)^k * y⌋₊ := by
    rw [heq]
    exact floor_two_mul_even_le hy_nonneg h_floor_even
  have h_lt := binaryDigit_partial_sum_lt y (k + 1)
  calc y < (⌊(2:ℝ)^(k+1) * y⌋₊ : ℝ) / (2:ℝ)^(k + 1) + (1:ℝ) / (2:ℝ)^(k + 1) := h_lt
    _ = (⌊(2:ℝ)^(k+1) * y⌋₊ + 1 : ℝ) / (2:ℝ)^(k + 1) := by ring
    _ ≤ (2 * ⌊(2:ℝ)^k * y⌋₊ + 1 : ℝ) / (2:ℝ)^(k + 1) := by
        apply div_le_div_of_nonneg_right _ h2k1_nonneg
        have : (⌊(2:ℝ)^(k+1) * y⌋₊ : ℝ) + 1 ≤ 2 * ⌊(2:ℝ)^k * y⌋₊ + 1 := by
          exact_mod_cast Nat.add_le_add_right h_floor_rel 1
        linarith
    _ = (⌊(2:ℝ)^k * y⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1) := by field_simp; ring

/-- Helper: floors of x, y in [0,1) are equal up to level n if their binary digits agree up to level n-1. -/
lemma floor_eq_of_binaryDigit_eq {x y : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (hy : y ∈ Set.Ico (0:ℝ) 1)
    (heq : ∀ j < n, binaryDigit x (j + 1) = binaryDigit y (j + 1)) :
    ⌊(2:ℝ)^n * x⌋₊ = ⌊(2:ℝ)^n * y⌋₊ := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    have hx01 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith [hx.2] : x < 1)
    have hy01 : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith [hy.2] : y < 1)
    simp [hx01, hy01]
  | succ n ih =>
    have h_prev : ∀ j < n, binaryDigit x (j + 1) = binaryDigit y (j + 1) := fun j hj => heq j (Nat.lt_succ_of_lt hj)
    have ih' := ih h_prev
    simp only [binaryDigit, if_pos hx, if_pos hy] at heq
    have hmod_eq := heq n (Nat.lt_succ_self n)
    have hx_nonneg : 0 ≤ (2:ℝ)^n * x := mul_nonneg (by positivity) hx.1
    have hy_nonneg : 0 ≤ (2:ℝ)^n * y := mul_nonneg (by positivity) hy.1
    have h1 : (2:ℝ)^(n+1) * x = 2 * ((2:ℝ)^n * x) := by ring
    have h2 : (2:ℝ)^(n+1) * y = 2 * ((2:ℝ)^n * y) := by ring
    have hmod_eq' : ⌊2 * ((2:ℝ)^n * x)⌋₊ % 2 = ⌊2 * ((2:ℝ)^n * y)⌋₊ % 2 := by
      rw [← h1, ← h2]; exact hmod_eq
    rw [h1, h2]
    exact floor_two_mul_eq_of_mod_eq hx_nonneg hy_nonneg ih' hmod_eq'

/-- For x, y ∈ [0,1) with x < y, there exists a first position k where bₖ(x) < bₖ(y). -/
lemma binaryDigit_first_diff {x y : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (hy : y ∈ Set.Ico (0:ℝ) 1)
    (hxy : x < y) :
    ∃ k, binaryDigit x (k + 1) < binaryDigit y (k + 1) ∧
         ∀ j < k, binaryDigit x (j + 1) = binaryDigit y (j + 1) := by
  have h_exists_diff : ∃ j, binaryDigit x (j + 1) ≠ binaryDigit y (j + 1) := by
    by_contra h_all_eq
    push_neg at h_all_eq
    have h_floor_eq : ∀ n, ⌊(2:ℝ)^n * x⌋₊ = ⌊(2:ℝ)^n * y⌋₊ := by
      intro n
      exact floor_eq_of_binaryDigit_eq hx hy (fun j _ => h_all_eq j)
    have h_close : ∀ n, |x - y| < (1:ℝ) / (2:ℝ)^n := by
      intro n
      have hx_bounds := binaryDigit_partial_sum_le hx n
      have hx_bounds' := binaryDigit_partial_sum_lt x n
      have hy_bounds := binaryDigit_partial_sum_le hy n
      have hy_bounds' := binaryDigit_partial_sum_lt y n
      rw [h_floor_eq n] at hx_bounds hx_bounds'
      rw [abs_lt]
      constructor <;> linarith
    have hxy_eq : x = y := by
      by_contra hne
      have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1:ℝ)/2 < 1)
      have := h_close n
      have h1 : (1:ℝ) / 2^n = (1/2)^n := by simp [div_eq_mul_inv]
      linarith
    exact absurd hxy_eq (ne_of_lt hxy)
  let k := Nat.find h_exists_diff
  have hk_diff : binaryDigit x (k + 1) ≠ binaryDigit y (k + 1) := Nat.find_spec h_exists_diff
  have hk_first : ∀ j < k, binaryDigit x (j + 1) = binaryDigit y (j + 1) := by
    intro j hj
    exact of_not_not (Nat.find_min h_exists_diff hj)
  have hbx := binaryDigit_le_one x (k + 1)
  have hby := binaryDigit_le_one y (k + 1)
  by_cases h : binaryDigit x (k + 1) < binaryDigit y (k + 1)
  · exact ⟨k, h, hk_first⟩
  · push_neg at h
    have hbx_eq : binaryDigit x (k + 1) = 1 := by omega
    have hby_eq : binaryDigit y (k + 1) = 0 := by omega
    exfalso
    have hx_lb := binaryDigit_one_implies_lower_bound hx k hbx_eq
    have hy_ub := binaryDigit_zero_implies_upper_bound hy k hby_eq
    have h_floor_eq : ⌊(2:ℝ)^k * x⌋₊ = ⌊(2:ℝ)^k * y⌋₊ := floor_eq_of_binaryDigit_eq hx hy hk_first
    rw [h_floor_eq] at hx_lb
    linarith

/-- Monotonicity: if digits agree up to k and bₖ(x) < bₖ(y), then g(x) < g(y). -/
lemma binaryToTernary_lt_of_digit_lt {x y : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) (k : ℕ)
    (hk_lt : binaryDigit x (k + 1) < binaryDigit y (k + 1))
    (hk_eq : ∀ j < k, binaryDigit x (j + 1) = binaryDigit y (j + 1)) :
    binaryToTernaryFn x < binaryToTernaryFn y := by
  have hbx_le := binaryDigit_le_one x (k + 1)
  have hby_le := binaryDigit_le_one y (k + 1)
  have hbx_zero : binaryDigit x (k + 1) = 0 := by omega
  have hby_one : binaryDigit y (k + 1) = 1 := by omega
  simp only [binaryToTernaryFn, if_pos hx, if_pos hy]
  let fx := fun j => (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
  let fy := fun j => (2 * binaryDigit y (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
  have h_first_eq : ∑ j ∈ Finset.range k, fx j = ∑ j ∈ Finset.range k, fy j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [fx, fy]
    rw [hk_eq j (Finset.mem_range.mp hj)]
  have h_term_x : fx k = 0 := by simp only [fx, hbx_zero, Nat.cast_zero, mul_zero, zero_mul]
  have h_term_y : fy k = (2:ℝ) * (1/3:ℝ)^(k + 1) := by
    simp only [fy, hby_one, Nat.cast_one, mul_one]
  have h_tail_x : ∑' j, fx (k + 1 + j) ≤ (1/3:ℝ)^(k + 1) := by
    calc ∑' j, fx (k + 1 + j)
        = ∑' j, (2 * binaryDigit x (k + 1 + j + 1) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := rfl
      _ ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
          apply Summable.tsum_le_tsum
          · intro j
            have hb := binaryDigit_le_one x (k + 1 + j + 1)
            have hb_real : (binaryDigit x (k + 1 + j + 1) : ℝ) ≤ 1 := by exact_mod_cast hb
            have h3pos : (0:ℝ) < (1/3)^(k + 1 + j + 1) := by positivity
            calc (2 * binaryDigit x (k + 1 + j + 1) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
                = 2 * (binaryDigit x (k + 1 + j + 1) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by ring
              _ ≤ 2 * 1 * (1/3:ℝ)^(k + 1 + j + 1) := by nlinarith
              _ = 2 * (1/3:ℝ)^(k + 1 + j + 1) := by ring
          · exact (binaryToTernary_summable x).comp_injective (fun j₁ j₂ h => by omega)
          · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
            exact (h.mul_left 2).comp_injective (fun j₁ j₂ h => by omega)
      _ = (1/3:ℝ)^(k + 1) := by
          have h1 := tsum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num)
          calc ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
              = ∑' j, (2:ℝ) * ((1/3:ℝ)^(k + 2) * (1/3:ℝ)^j) := by
                congr 1; ext j; rw [← pow_add]; ring_nf
            _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * ∑' j, (1/3:ℝ)^j := by
                rw [← tsum_mul_left]; congr 1; ext j; ring
            _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * (1 - 1/3)⁻¹ := by rw [h1]
            _ = (1/3:ℝ)^(k + 1) := by field_simp; ring
  have h_tail_y_nonneg : 0 ≤ ∑' j, fy (k + 1 + j) := by
    apply tsum_nonneg; intro j; simp only [fy]; positivity
  have hsum_x : Summable fx := binaryToTernary_summable x
  have hsum_y : Summable fy := binaryToTernary_summable y
  have h_split_x : ∑' j, fx j = ∑ j ∈ Finset.range k, fx j + fx k + ∑' j, fx (k + 1 + j) := by
    rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_x, Finset.sum_range_succ]
    congr 1
    congr 1
    ext j
    congr 1
    omega
  have h_split_y : ∑' j, fy j = ∑ j ∈ Finset.range k, fy j + fy k + ∑' j, fy (k + 1 + j) := by
    rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_y, Finset.sum_range_succ]
    congr 1
    congr 1
    ext j
    congr 1
    omega
  rw [h_split_x, h_split_y, h_first_eq, h_term_x, h_term_y]
  have h3pos : (0:ℝ) < (1/3)^(k + 1) := by positivity
  linarith

/-! ### Helper lemmas for injectivity proof -/

/-- Ternary {0,2} expansions are unique. -/
lemma ternary_02_expansion_unique {d e : ℕ → ℕ}
    (hd : ∀ j, d j ∈ ({0, 2} : Set ℕ))
    (he : ∀ j, e j ∈ ({0, 2} : Set ℕ))
    (hsum_d : Summable (fun j => (d j : ℝ) * (1/3:ℝ)^(j + 1)))
    (hsum_e : Summable (fun j => (e j : ℝ) * (1/3:ℝ)^(j + 1)))
    (heq : ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) = ∑' j, (e j : ℝ) * (1/3:ℝ)^(j + 1)) :
    ∀ j, d j = e j := by
  by_contra h_ne
  push_neg at h_ne
  have h_exists : ∃ k, d k ≠ e k := h_ne
  let k := Nat.find h_exists
  have hk_ne : d k ≠ e k := Nat.find_spec h_exists
  have hk_eq : ∀ j < k, d j = e j := fun j hj => by
    by_contra h
    exact Nat.find_min h_exists hj h
  have hd_k := hd k
  have he_k := he k
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd_k he_k
  rcases hd_k with hdk0 | hdk2 <;> rcases he_k with hek0 | hek2
  · omega
  ·
    have h_first_eq : ∑ j ∈ Finset.range k, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (e j : ℝ) * (1/3:ℝ)^(j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hk_eq j (Finset.mem_range.mp hj)]
    have h_split_d : ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (d j : ℝ) * (1/3:ℝ)^(j + 1) + (d k : ℝ) * (1/3:ℝ)^(k + 1) +
        ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_d, Finset.sum_range_succ]
      congr 1; congr 1
      funext j; simp only [add_comm j (k + 1)]
    have h_split_e : ∑' j, (e j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (e j : ℝ) * (1/3:ℝ)^(j + 1) + (e k : ℝ) * (1/3:ℝ)^(k + 1) +
        ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_e, Finset.sum_range_succ]
      congr 1; congr 1
      funext j; simp only [add_comm j (k + 1)]
    rw [h_split_d, h_split_e, h_first_eq, hdk0, hek2] at heq
    simp only [Nat.cast_zero, zero_mul, Nat.cast_ofNat] at heq
    have h_tail_d_bound : ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) ≤ (1/3:ℝ)^(k + 1) := by
      calc ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
          ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
            apply Summable.tsum_le_tsum
            · intro j
              have hdj := hd (k + 1 + j)
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdj
              rcases hdj with hdj0 | hdj2
              · simp only [hdj0, Nat.cast_zero, zero_mul]; positivity
              · simp only [hdj2, Nat.cast_ofNat]; exact le_rfl
            · exact hsum_d.comp_injective (fun _ _ h => by omega)
            · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
              exact (h.mul_left 2).comp_injective (fun _ _ h => by omega)
        _ = (1/3:ℝ)^(k + 1) := by
            have h1 := tsum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num)
            calc ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
                = ∑' j, (2:ℝ) * ((1/3:ℝ)^(k + 2) * (1/3:ℝ)^j) := by
                  congr 1; ext j; rw [← pow_add]; ring_nf
              _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * ∑' j, (1/3:ℝ)^j := by
                  rw [← tsum_mul_left]; congr 1; ext j; ring
              _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * (1 - 1/3)⁻¹ := by rw [h1]
              _ = (1/3:ℝ)^(k + 1) := by field_simp; ring
    have h_tail_e_nonneg : 0 ≤ ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      apply tsum_nonneg; intro j; positivity
    have h3pos : (0:ℝ) < (1/3)^(k + 1) := by positivity
    linarith
  ·
    have h_first_eq : ∑ j ∈ Finset.range k, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (e j : ℝ) * (1/3:ℝ)^(j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hk_eq j (Finset.mem_range.mp hj)]
    have h_split_d : ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (d j : ℝ) * (1/3:ℝ)^(j + 1) + (d k : ℝ) * (1/3:ℝ)^(k + 1) +
        ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_d, Finset.sum_range_succ]
      congr 1; congr 1
      funext j; simp only [add_comm j (k + 1)]
    have h_split_e : ∑' j, (e j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (e j : ℝ) * (1/3:ℝ)^(j + 1) + (e k : ℝ) * (1/3:ℝ)^(k + 1) +
        ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_e, Finset.sum_range_succ]
      congr 1; congr 1
      funext j; simp only [add_comm j (k + 1)]
    rw [h_split_d, h_split_e, h_first_eq, hdk2, hek0] at heq
    simp only [Nat.cast_zero, zero_mul, Nat.cast_ofNat] at heq
    have h_tail_e_bound : ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) ≤ (1/3:ℝ)^(k + 1) := by
      calc ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
          ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
            apply Summable.tsum_le_tsum
            · intro j
              have hej := he (k + 1 + j)
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hej
              rcases hej with hej0 | hej2
              · simp only [hej0, Nat.cast_zero, zero_mul]; positivity
              · simp only [hej2, Nat.cast_ofNat]; exact le_rfl
            · exact hsum_e.comp_injective (fun _ _ h => by omega)
            · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
              exact (h.mul_left 2).comp_injective (fun _ _ h => by omega)
        _ = (1/3:ℝ)^(k + 1) := by
            have h1 := tsum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num)
            calc ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
                = ∑' j, (2:ℝ) * ((1/3:ℝ)^(k + 2) * (1/3:ℝ)^j) := by
                  congr 1; ext j; rw [← pow_add]; ring_nf
              _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * ∑' j, (1/3:ℝ)^j := by
                  rw [← tsum_mul_left]; congr 1; ext j; ring
              _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * (1 - 1/3)⁻¹ := by rw [h1]
              _ = (1/3:ℝ)^(k + 1) := by field_simp; ring
    have h_tail_d_nonneg : 0 ≤ ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      apply tsum_nonneg; intro j; positivity
    have h3pos : (0:ℝ) < (1/3)^(k + 1) := by positivity
    linarith
  · omega

/-! ### Helper lemmas for binary expansion sums -/

/-- ⌊2y⌋ = 2⌊y⌋ + ⌊2y⌋ % 2 for y ≥ 0. -/
private lemma floor_two_mul_decomp {y : ℝ} (_hy : 0 ≤ y) :
    ⌊2 * y⌋₊ = 2 * ⌊y⌋₊ + ⌊2 * y⌋₊ % 2 := by
  have h := Nat.div_add_mod ⌊2 * y⌋₊ 2
  have h_div : ⌊2 * y⌋₊ / 2 = ⌊y⌋₊ := Nat.cast_mul_floor_div_cancel (by norm_num : (2:ℕ) ≠ 0) y
  omega

/-- Partial sum identity: ∑_{j < n} b_j * 2^{-(j+1)} = ⌊2^n * x⌋ / 2^n. -/
private lemma partial_sum_eq_floor {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) =
    (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
    have h0 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx.2
    simp [h0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h2n_pos : (0:ℝ) < 2^n := by positivity
    have hx_nonneg : 0 ≤ x := hx.1
    have hb : binaryDigit x (n + 1) = ⌊(2:ℝ)^(n+1) * x⌋₊ % 2 := by
      simp only [binaryDigit, if_pos hx]
    have h_floor : ⌊(2:ℝ)^(n+1) * x⌋₊ = 2 * ⌊(2:ℝ)^n * x⌋₊ + ⌊(2:ℝ)^(n+1) * x⌋₊ % 2 := by
      have h2 : (2:ℝ)^(n+1) * x = 2 * ((2:ℝ)^n * x) := by ring
      rw [h2]
      exact floor_two_mul_decomp (mul_nonneg (le_of_lt h2n_pos) hx_nonneg)
    rw [hb]
    have h2n_ne : (2:ℝ)^n ≠ 0 := ne_of_gt h2n_pos
    have h_pow_succ : (2:ℝ)^(n+1) = 2 * 2^n := by ring
    rw [h_pow_succ]
    have h_half_pow : (1/2:ℝ)^(n+1) = 1 / (2 * 2^n) := by
      rw [← h_pow_succ]; simp [div_eq_mul_inv]
    rw [h_half_pow]
    have h_floor' : (⌊2 * 2^n * x⌋₊ : ℝ) = 2 * (⌊(2:ℝ)^n * x⌋₊ : ℝ) + (⌊2 * 2^n * x⌋₊ % 2 : ℕ) := by
      have h2eq : (2:ℝ) * 2^n * x = (2:ℝ)^(n+1) * x := by ring
      rw [h2eq]
      exact_mod_cast h_floor
    have h2_2n_pos : (0:ℝ) < 2 * 2^n := by positivity
    have h2_2n_ne : (2:ℝ) * 2^n ≠ 0 := ne_of_gt h2_2n_pos
    rw [h_floor']
    field_simp

/-- Binary series is summable for x ∈ [0,1). -/
private lemma binary_summable {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) :
    Summable (fun j => (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro j; positivity
  · intro j
    have h1 : (binaryDigit x (j + 1) : ℝ) ≤ 1 := by
      have : binaryDigit x (j + 1) ≤ 1 := by
        simp only [binaryDigit, if_pos hx]
        omega
      exact_mod_cast this
    calc (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1)
        ≤ 1 * (1/2:ℝ)^(j + 1) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) (j + 1)]
      _ = (1/2:ℝ)^(j + 1) := by ring
  · have h : Summable (fun j : ℕ => (1/2:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact h.comp_injective (fun _ _ h => Nat.succ_injective h)

/-- For non-dyadic x ∈ [0,1), x equals its binary expansion sum. -/
lemma non_dyadic_eq_binary_sum {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (_hnd : x ∉ DyadicRationals) :
    x = ∑' j : ℕ, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) := by
  have h_summable := binary_summable hx
  have h_partial_to_tsum : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range n, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1))
      Filter.atTop (nhds (∑' j, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1))) :=
    h_summable.hasSum.tendsto_sum_nat
  have h_partial_eq : ∀ n, ∑ j ∈ Finset.range n, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) =
      (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n := partial_sum_eq_floor hx
  have h_floor_to_x : Filter.Tendsto (fun n => (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n) Filter.atTop (nhds x) := by
    have h_lower : ∀ n, (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ≤ x := fun n => by
      have h2n_pos : (0:ℝ) < 2^n := by positivity
      rw [div_le_iff₀ h2n_pos, mul_comm]
      exact Nat.floor_le (mul_nonneg hx.1 (le_of_lt h2n_pos))
    have h_upper : ∀ n, x < (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n := fun n => by
      have h2n_pos : (0:ℝ) < 2^n := by positivity
      have := Nat.lt_floor_add_one ((2:ℝ)^n * x)
      calc x = ((2:ℝ)^n * x) / (2:ℝ)^n := by field_simp
        _ < (⌊(2:ℝ)^n * x⌋₊ + 1 : ℝ) / (2:ℝ)^n := by apply div_lt_div_of_pos_right this h2n_pos
        _ = (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n := by ring
    have h_gap : Filter.Tendsto (fun n : ℕ => (1:ℝ) / (2:ℝ)^n) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2)^n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      convert h1 using 1; ext n; simp [div_eq_mul_inv]
    have h_between : ∀ n, x - (1:ℝ) / (2:ℝ)^n < (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ∧
        (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ≤ x := fun n => ⟨by linarith [h_upper n], h_lower n⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    rw [Metric.tendsto_atTop] at h_gap
    obtain ⟨N, hN⟩ := h_gap ε hε
    use N
    intro n hn
    specialize hN n hn
    simp only [Real.dist_eq, sub_zero] at hN
    rw [abs_of_pos (by positivity)] at hN
    have hbn := h_between n
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hbn.1, hbn.2]
  have h_partial_to_x : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range n, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1))
      Filter.atTop (nhds x) := by
    simp_rw [h_partial_eq]
    exact h_floor_to_x
  exact tendsto_nhds_unique h_partial_to_x h_partial_to_tsum

/-- Non-dyadic x ∈ [0,1) with equal binary digits are equal. -/
lemma eq_of_binaryDigit_eq_of_non_dyadic {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ Set.Ico (0:ℝ) 1) (hx₂ : x₂ ∈ Set.Ico (0:ℝ) 1)
    (hnd₁ : x₁ ∉ DyadicRationals) (hnd₂ : x₂ ∉ DyadicRationals)
    (heq : ∀ j, binaryDigit x₁ j = binaryDigit x₂ j) :
    x₁ = x₂ := by
  have h1 := non_dyadic_eq_binary_sum hx₁ hnd₁
  have h2 := non_dyadic_eq_binary_sum hx₂ hnd₂
  rw [h1, h2]
  congr 1
  ext j
  rw [heq (j + 1)]

/-! ### Helper lemmas for image_in_cantor -/

/-- Points with {0,2} ternary digits are in the Cantor set. -/
lemma mem_CantorSet_of_ternary_02 {y : ℝ} (d : ℕ → ℕ)
    (hd : ∀ j, d j ∈ ({0, 2} : Set ℕ))
    (hsum : Summable (fun j => (d j : ℝ) * (1/3:ℝ)^(j + 1)))
    (hy : y = ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1)) :
    y ∈ CantorSet ∨ y = 0 := by
  left
  rw [CantorSet]
  simp only [Set.mem_iInter]
  intro n
  let a : Fin n → ({0, 2} : Set ℕ) := fun i => ⟨d i.val, hd i.val⟩
  rw [CantorInterval]
  simp only [Set.mem_iUnion]
  use a
  simp only [BoundedInterval.set_Icc, Set.mem_Icc]
  have h_split : y = ∑ j ∈ Finset.range n, (d j : ℝ) * (1/3:ℝ)^(j + 1) +
      ∑' j, (d (n + j) : ℝ) * (1/3:ℝ)^(n + j + 1) := by
    rw [hy, ← Summable.sum_add_tsum_nat_add n hsum]
    congr 1
    apply tsum_congr
    intro j
    rw [add_comm j n]
  have h_partial : ∑ j ∈ Finset.range n, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
      ∑ i : Fin n, (a i : ℝ) / (3:ℝ)^(i.val + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [dif_pos hj]
    simp only [a]
    field_simp; ring_nf; simp
  have h_tail_nonneg : 0 ≤ ∑' j, (d (n + j) : ℝ) * (1/3:ℝ)^(n + j + 1) := by
    apply tsum_nonneg; intro j; positivity
  have h_tail_bound : ∑' j, (d (n + j) : ℝ) * (1/3:ℝ)^(n + j + 1) ≤ (1/3:ℝ)^n := by
    calc ∑' j, (d (n + j) : ℝ) * (1/3:ℝ)^(n + j + 1)
        ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(n + j + 1) := by
          apply Summable.tsum_le_tsum
          · intro j
            have hdj := hd (n + j)
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdj
            rcases hdj with hdj0 | hdj2
            · simp only [hdj0, Nat.cast_zero, zero_mul]; positivity
            · simp only [hdj2, Nat.cast_ofNat]; exact le_refl _
          · exact hsum.comp_injective (fun _ _ h => by omega)
          · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            exact (h.mul_left 2).comp_injective (fun _ _ h => by omega)
      _ = (1/3:ℝ)^n := by
          have h1 := tsum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num)
          calc ∑' j, (2:ℝ) * (1/3:ℝ)^(n + j + 1)
              = ∑' j, (2:ℝ) * ((1/3:ℝ)^(n + 1) * (1/3:ℝ)^j) := by
                congr 1; ext j; rw [← pow_add]; ring_nf
            _ = (2:ℝ) * (1/3:ℝ)^(n + 1) * ∑' j, (1/3:ℝ)^j := by
                rw [← tsum_mul_left]; congr 1; ext j; ring
            _ = (2:ℝ) * (1/3:ℝ)^(n + 1) * (1 - 1/3)⁻¹ := by rw [h1]
            _ = (1/3:ℝ)^n := by field_simp; ring
  rw [h_split, h_partial]
  have h_one_third_pow : (1/3:ℝ)^n = 1 / 3^n := by simp [div_eq_mul_inv]
  constructor
  · linarith
  · rw [← h_one_third_pow]
    exact add_le_add_right h_tail_bound _

/-- Existence of a binary-to-ternary function: g(x) = ∑ 2bⱼ 3^{-j}. -/
lemma binaryToTernary_exists : ∃ g : ℝ → ℝ, BinaryToTernaryProperties g := by
  use binaryToTernaryFn
  exact {
    nonneg := by
      intro x
      simp only [binaryToTernaryFn]
      split_ifs with h
      · apply tsum_nonneg; intro j; positivity
      · rfl
    bounded := by
      intro x
      simp only [binaryToTernaryFn]
      split_ifs with h
      · have h_bound : ∀ j, (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1) ≤
            (2:ℝ) * (1/3:ℝ)^(j + 1) := by
          intro j
          have h1 : (binaryDigit x (j + 1) : ℝ) ≤ 1 := by
            exact_mod_cast binaryDigit_le_one x (j + 1)
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/3) (j + 1)]
        have h_summable2 : Summable (fun j => (2:ℝ) * (1/3:ℝ)^(j + 1)) := by
          have h : Summable (fun j : ℕ => (1/3:ℝ)^j) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          exact (h.mul_left 2).comp_injective (fun _ _ h => Nat.succ_injective h)
        calc ∑' j, (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
            ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(j + 1) :=
              Summable.tsum_le_tsum h_bound (binaryToTernary_summable x) h_summable2
          _ = 1 := tsum_two_thirds_geometric
      · norm_num
    zero_outside := by
      intro x hx
      simp only [binaryToTernaryFn, if_neg hx]
    zero_at_zero := by
      simp only [binaryToTernaryFn]
      have h0 : (0:ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, by norm_num⟩
      rw [if_pos h0]
      simp only [binaryDigit_zero, Nat.cast_zero, mul_zero, zero_mul, tsum_zero]
    zero_set_countable := by
      apply Set.Countable.mono _ (Set.countable_singleton 0)
      intro x hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
      obtain ⟨hx_in, hgx⟩ := hx
      simp only [binaryToTernaryFn, if_pos hx_in] at hgx
      by_contra hx_ne
      have hx_pos : 0 < x := by
        rcases eq_or_lt_of_le hx_in.1 with rfl | hpos
        · exact absurd rfl hx_ne
        · exact hpos
      have h_exists_one : ∃ j, binaryDigit x (j + 1) = 1 := by
        by_cases hx1 : x = 1
        · exact ⟨0, by rw [hx1]; exact binaryDigit_one 1⟩
        · exact binaryDigit_exists_one_of_pos hx_pos (lt_of_le_of_ne hx_in.2 hx1)
      obtain ⟨j, hj_eq⟩ := h_exists_one
      have h_term_pos : (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1) > 0 := by
        rw [hj_eq]; positivity
      have h_nonneg : ∀ k, 0 ≤ (2 * binaryDigit x (k + 1) : ℝ) * (1/3:ℝ)^(k + 1) := by
        intro k; positivity
      have h_sum_pos : 0 < ∑' k : ℕ, (2 * binaryDigit x (k + 1) : ℝ) * (1/3:ℝ)^(k + 1) :=
        (binaryToTernary_summable x).tsum_pos h_nonneg j h_term_pos
      linarith
    monotone_on := by
      intro x hx y hy hxy
      by_cases hxy' : x = y
      · simp [hxy']
      ·
        have hxy_strict : x < y := lt_of_le_of_ne hxy hxy'
        have hx_lt_one : x < 1 := lt_of_lt_of_le hxy_strict hy.2
        have hx_Ico : x ∈ Set.Ico (0:ℝ) 1 := ⟨hx.1, hx_lt_one⟩
        by_cases hy1 : y = 1
        ·
          subst hy1
          have h_exists_k : ∃ k, binaryDigit x (k + 1) = 0 := by
            by_contra h_all_one
            push_neg at h_all_one
            have h_all_eq_one : ∀ j, binaryDigit x (j + 1) = 1 := by
              intro j
              have h := binaryDigit_le_one x (j + 1)
              have hne := h_all_one j
              omega
            by_cases hx_dyadic : x ∈ DyadicRationals
            · simp only [DyadicRationals, Set.mem_setOf_eq] at hx_dyadic
              obtain ⟨k, n, hx_eq, _⟩ := hx_dyadic
              have h_zero_after : binaryDigit x (n + 1) = 0 := by
                simp only [binaryDigit, if_pos hx_Ico]
                rw [hx_eq]
                have h_calc : (2:ℝ)^(n + 1) * (k / (2:ℝ)^n) = 2 * k := by field_simp; ring
                rw [h_calc]
                have : (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) := by simp
                rw [this, Nat.floor_natCast, Nat.mul_mod_right]
              exact h_all_one n h_zero_after
            · have hx_eq_sum := non_dyadic_eq_binary_sum hx_Ico hx_dyadic
              exfalso
              have h_sum_one : ∑' j : ℕ, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) = 1 := by
                have h_digit : ∀ j, (binaryDigit x (j + 1) : ℝ) = 1 := by
                  intro j; rw [h_all_eq_one j]; norm_num
                simp_rw [h_digit]
                have h := tsum_geometric_of_lt_one (r := (1:ℝ)/2) (by norm_num) (by norm_num)
                calc ∑' j, (1:ℝ) * (1/2)^(j + 1) = ∑' j, (1/2:ℝ)^(j + 1) := by simp
                  _ = (1/2) * ∑' j, (1/2:ℝ)^j := by
                      rw [← tsum_mul_left]; congr 1; ext j; ring
                  _ = (1/2) * (1 - 1/2)⁻¹ := by rw [h]
                  _ = 1 := by norm_num
              rw [hx_eq_sum, h_sum_one] at hx_lt_one
              linarith
          let k := Nat.find h_exists_k
          have hk_zero : binaryDigit x (k + 1) = 0 := Nat.find_spec h_exists_k
          have hk_first : ∀ j < k, binaryDigit x (j + 1) ≠ 0 := by
            intro j hj
            exact Nat.find_min h_exists_k hj
          have hk_lt : binaryDigit x (k + 1) < binaryDigit 1 (k + 1) := by
            rw [hk_zero, binaryDigit_one]; norm_num
          have hk_eq : ∀ j < k, binaryDigit x (j + 1) = binaryDigit 1 (j + 1) := by
            intro j hj
            rw [binaryDigit_one]
            have h := binaryDigit_le_one x (j + 1)
            have hne := hk_first j hj
            omega
          exact le_of_lt (binaryToTernary_lt_of_digit_lt hx ⟨zero_le_one, le_refl 1⟩ k hk_lt hk_eq)
        ·
          have hy_lt_one : y < 1 := lt_of_le_of_ne hy.2 hy1
          have hy_Ico : y ∈ Set.Ico (0:ℝ) 1 := ⟨hy.1, hy_lt_one⟩
          obtain ⟨k, hk_lt, hk_eq⟩ := binaryDigit_first_diff hx_Ico hy_Ico hxy_strict
          exact le_of_lt (binaryToTernary_lt_of_digit_lt hx hy k hk_lt hk_eq)
    image_in_cantor := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [binaryToTernaryFn, if_pos hx]
      let d : ℕ → ℕ := fun j => 2 * binaryDigit x (j + 1)
      have hd : ∀ j, d j ∈ ({0, 2} : Set ℕ) := by
        intro j
        have h := binaryDigit_le_one x (j + 1)
        simp only [d]
        interval_cases binaryDigit x (j + 1) <;> simp
      have hsum : Summable (fun j => (d j : ℝ) * (1/3:ℝ)^(j + 1)) := by
        convert binaryToTernary_summable x using 1
        funext j; simp [d]
      have hy_eq : ∑' j, (2:ℝ) * ↑(binaryDigit x (j + 1)) * (1 / 3) ^ (j + 1) =
          ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) := by
        congr 1; funext j; simp only [d, Nat.cast_mul, Nat.cast_ofNat]
      rw [hy_eq]
      exact mem_CantorSet_of_ternary_02 d hd hsum rfl
    injective_on_nonterminating := by
      let A := Set.Icc (0:ℝ) 1 \ DyadicRationals
      use A
      refine ⟨Set.diff_subset, ?_, ?_, ?_⟩
      · have h_sdiff : Set.Icc (0:ℝ) 1 \ A = DyadicRationals ∩ Set.Icc 0 1 := by
          simp only [A, Set.diff_diff_right, Set.diff_self, Set.empty_union, Set.inter_comm]
        rw [h_sdiff]
        exact DyadicRationals.countable.mono Set.inter_subset_left
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [A, Set.mem_diff] at hx₁ hx₂
        simp only [binaryToTernaryFn, if_pos hx₁.1, if_pos hx₂.1] at heq
        let d₁ : ℕ → ℕ := fun j => 2 * binaryDigit x₁ (j + 1)
        let d₂ : ℕ → ℕ := fun j => 2 * binaryDigit x₂ (j + 1)
        have hd₁ : ∀ j, d₁ j ∈ ({0, 2} : Set ℕ) := by
          intro j; have h := binaryDigit_le_one x₁ (j + 1)
          simp only [d₁]; interval_cases binaryDigit x₁ (j + 1) <;> simp
        have hd₂ : ∀ j, d₂ j ∈ ({0, 2} : Set ℕ) := by
          intro j; have h := binaryDigit_le_one x₂ (j + 1)
          simp only [d₂]; interval_cases binaryDigit x₂ (j + 1) <;> simp
        have heq' : ∑' j, (d₁ j : ℝ) * (1/3:ℝ)^(j + 1) = ∑' j, (d₂ j : ℝ) * (1/3:ℝ)^(j + 1) := by
          convert heq using 1 <;> { congr 1; funext j; simp only [d₁, d₂, Nat.cast_mul, Nat.cast_ofNat] }
        have hsum₁ : Summable (fun j => (d₁ j : ℝ) * (1/3:ℝ)^(j + 1)) := by
          convert binaryToTernary_summable x₁ using 1
          funext j; simp only [d₁, Nat.cast_mul, Nat.cast_ofNat]
        have hsum₂ : Summable (fun j => (d₂ j : ℝ) * (1/3:ℝ)^(j + 1)) := by
          convert binaryToTernary_summable x₂ using 1
          funext j; simp only [d₂, Nat.cast_mul, Nat.cast_ofNat]
        have hdigits_eq := ternary_02_expansion_unique hd₁ hd₂ hsum₁ hsum₂ heq'
        have hbinary_eq : ∀ j, binaryDigit x₁ (j + 1) = binaryDigit x₂ (j + 1) := by
          intro j
          have := hdigits_eq j
          simp only [d₁, d₂] at this
          omega
        have h1_dyadic : (1:ℝ) ∈ DyadicRationals := ⟨1, 0, by norm_num, by norm_num⟩
        have hx₁_ne_1 : x₁ ≠ 1 := fun h => hx₁.2 (h ▸ h1_dyadic)
        have hx₂_ne_1 : x₂ ≠ 1 := fun h => hx₂.2 (h ▸ h1_dyadic)
        have hx₁_Ico : x₁ ∈ Set.Ico (0:ℝ) 1 := ⟨hx₁.1.1, lt_of_le_of_ne hx₁.1.2 hx₁_ne_1⟩
        have hx₂_Ico : x₂ ∈ Set.Ico (0:ℝ) 1 := ⟨hx₂.1.1, lt_of_le_of_ne hx₂.1.2 hx₂_ne_1⟩
        apply eq_of_binaryDigit_eq_of_non_dyadic hx₁_Ico hx₂_Ico hx₁.2 hx₂.2
        intro j
        rcases j with _ | j
        ·
          simp only [binaryDigit, if_pos hx₁_Ico, if_pos hx₂_Ico, pow_zero, one_mul]
          have h1 : ⌊x₁⌋₊ = 0 := Nat.floor_eq_zero.mpr hx₁_Ico.2
          have h2 : ⌊x₂⌋₊ = 0 := Nat.floor_eq_zero.mpr hx₂_Ico.2
          simp [h1, h2]
        · exact hbinary_eq j
      · ext x
        simp only [A, Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and]
        intro ⟨_, hx_not_dyadic⟩ hx_dyadic
        exact hx_not_dyadic hx_dyadic
  }

/-- Binary-to-ternary function: g(x) = ∑ 2·bⱼ(x)·3^{-j}, monotone on [0,1], g([0,1]) ⊆ C ∪ {0}. -/
noncomputable def binaryToTernary : ℝ → ℝ := Classical.choose binaryToTernary_exists

lemma binaryToTernary_props : BinaryToTernaryProperties binaryToTernary :=
  Classical.choose_spec binaryToTernary_exists

/-- binaryToTernary x = 0 iff x = 0 for x ∈ [0,1]. -/
lemma binaryToTernary_eq_zero_iff {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    binaryToTernary x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx_ne
    have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_ne)
    have h0_in : (0:ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, by norm_num⟩
    have h_mono := binaryToTernary_props.monotone_on h0_in hx (le_of_lt hx_pos)
    rw [binaryToTernary_props.zero_at_zero] at h_mono
    have h_zero_set : Set.Icc (0:ℝ) x ⊆ Set.Icc 0 1 ∩ {y | binaryToTernary y = 0} := by
      intro y hy
      constructor
      · exact ⟨hy.1, le_trans hy.2 hx.2⟩
      · simp only [Set.mem_setOf_eq]
        have h0y : (0:ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, by norm_num⟩
        have hy_in : y ∈ Set.Icc 0 1 := ⟨hy.1, le_trans hy.2 hx.2⟩
        have h_mono1 := binaryToTernary_props.monotone_on h0y hy_in hy.1
        have h_mono2 := binaryToTernary_props.monotone_on hy_in hx hy.2
        rw [binaryToTernary_props.zero_at_zero] at h_mono1
        rw [h] at h_mono2
        linarith [binaryToTernary_props.nonneg y]
    have h_uncountable : ¬ (Set.Icc (0:ℝ) x).Countable := by
      have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (fun h => hx_ne h.symm)
      have h_card := Cardinal.mk_Icc_real hx_pos
      intro hc
      have := hc.le_aleph0
      rw [h_card] at this
      exact Cardinal.aleph0_lt_continuum.not_ge this
    exact h_uncountable (Set.Countable.mono h_zero_set binaryToTernary_props.zero_set_countable)
  · intro h
    rw [h]
    exact binaryToTernary_props.zero_at_zero

/-- binaryToTernary lifted to EuclideanSpace' 1 → EReal (called f in informal proof). -/
noncomputable def f_lifted : EuclideanSpace' 1 → EReal :=
  fun x => Real.toEReal (max 0 (binaryToTernary (EuclideanSpace'.equiv_Real x)))

lemma f_lifted_unsigned : Unsigned f_lifted := by
  intro x
  simp only [f_lifted, ge_iff_le]
  rw [EReal.coe_nonneg]
  exact le_max_left 0 _

lemma f_lifted_le_one (x : EuclideanSpace' 1) : f_lifted x ≤ 1 := by
  simp only [f_lifted]
  have hg := binaryToTernary_props.bounded (EuclideanSpace'.equiv_Real x)
  have h_max_le : max 0 (binaryToTernary (EuclideanSpace'.equiv_Real x)) ≤ 1 :=
    max_le (by norm_num) hg
  exact EReal.coe_le_coe_iff.mpr h_max_le

lemma f_lifted_zero_outside (x : EuclideanSpace' 1) (hx : EuclideanSpace'.equiv_Real x ∉ Set.Icc 0 1) :
    f_lifted x = 0 := by
  simp only [f_lifted]
  have hg := binaryToTernary_props.zero_outside (EuclideanSpace'.equiv_Real x) hx
  rw [hg]
  simp

lemma f_lifted_zero_at_zero (x : EuclideanSpace' 1) (hx : EuclideanSpace'.equiv_Real x = 0) :
    f_lifted x = 0 := by
  simp only [f_lifted]
  have hg := binaryToTernary_props.zero_at_zero
  rw [hx, hg]
  simp

lemma f_zero_set_in_interval_countable :
    (Set.Icc (0:ℝ) 1 ∩ {x | binaryToTernary x = 0}).Countable :=
  binaryToTernary_props.zero_set_countable

lemma f_lifted_zero_set_measurable : LebesgueMeasurable {x : EuclideanSpace' 1 | f_lifted x = 0} := by
  have h_decomp : {x : EuclideanSpace' 1 | f_lifted x = 0} =
      (Real.equiv_EuclideanSpace' '' (Set.Icc 0 1)ᶜ) ∪
      (Real.equiv_EuclideanSpace' '' (Set.Icc 0 1 ∩ {x | binaryToTernary x = 0})) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hfx
      simp only [f_lifted] at hfx
      have hmax : max 0 (binaryToTernary (EuclideanSpace'.equiv_Real x)) = 0 := by
        rw [EReal.coe_eq_zero] at hfx
        exact hfx
      have hbinary : binaryToTernary (EuclideanSpace'.equiv_Real x) ≤ 0 := by
        have := le_max_right 0 (binaryToTernary (EuclideanSpace'.equiv_Real x))
        rw [hmax] at this
        exact this
      have hbinary_nonneg := binaryToTernary_props.nonneg (EuclideanSpace'.equiv_Real x)
      have hbinary_eq : binaryToTernary (EuclideanSpace'.equiv_Real x) = 0 :=
        le_antisymm hbinary hbinary_nonneg
      by_cases h_in : EuclideanSpace'.equiv_Real x ∈ Set.Icc 0 1
      · right
        use EuclideanSpace'.equiv_Real x
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · exact ⟨h_in, hbinary_eq⟩
        · exact EuclideanSpace'.equiv_Real.symm_apply_apply x
      · left
        use EuclideanSpace'.equiv_Real x
        simp only [Set.mem_compl_iff]
        exact ⟨h_in, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
    · intro h
      rcases h with ⟨r, hr, hrx⟩ | ⟨r, ⟨hr_in, hr_zero⟩, hrx⟩
      · simp only [f_lifted]
        have hx_eq : EuclideanSpace'.equiv_Real x = r := by
          rw [← hrx]; exact EuclideanSpace'.equiv_Real.apply_symm_apply r
        rw [hx_eq, binaryToTernary_props.zero_outside r hr]; simp
      · simp only [f_lifted]
        have hx_eq : EuclideanSpace'.equiv_Real x = r := by
          rw [← hrx]; exact EuclideanSpace'.equiv_Real.apply_symm_apply r
        rw [hx_eq, hr_zero]; simp
  rw [h_decomp]
  apply LebesgueMeasurable.union
  · apply IsOpen.measurable
    have h_open : IsOpen (Set.Icc (0:ℝ) 1)ᶜ := isOpen_compl_iff.mpr isClosed_Icc
    have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
      show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
    have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
      exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
    let e : ℝ ≃ₜ EuclideanSpace' 1 :=
      { toEquiv := Real.equiv_EuclideanSpace'
        continuous_toFun := hf_cont
        continuous_invFun := hg_cont }
    exact e.isOpenMap (Set.Icc 0 1)ᶜ h_open
  · apply IsNull.measurable
    have h_countable : (Real.equiv_EuclideanSpace' '' (Set.Icc 0 1 ∩ {x | binaryToTernary x = 0})).Countable := by
      apply Set.Countable.image; exact f_zero_set_in_interval_countable
    exact Countable.Lebesgue_measure Nat.one_pos h_countable

/-- Sublevel sets of f_lifted are measurable (key lemma for f_lifted_measurable). -/
lemma sublevel_set_measurable (t : EReal) (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    LebesgueMeasurable {x : EuclideanSpace' 1 | f_lifted x ≤ t} := by
  have h_outside_zero : ∀ x : EuclideanSpace' 1, EuclideanSpace'.equiv_Real x ∉ Set.Icc 0 1 →
      f_lifted x ≤ t := fun x hx => by rw [f_lifted_zero_outside x hx]; exact le_of_lt ht_pos
  have h_decomp : {x : EuclideanSpace' 1 | f_lifted x ≤ t} =
      (Real.equiv_EuclideanSpace' '' Set.Iio 0) ∪
      (Real.equiv_EuclideanSpace' '' Set.Ioi 1) ∪
      {x : EuclideanSpace' 1 | EuclideanSpace'.equiv_Real x ∈ Set.Icc 0 1 ∧ f_lifted x ≤ t} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hfx
      by_cases h_neg : EuclideanSpace'.equiv_Real x < 0
      · left; left
        use EuclideanSpace'.equiv_Real x
        exact ⟨h_neg, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
      · by_cases h_big : EuclideanSpace'.equiv_Real x > 1
        · left; right
          use EuclideanSpace'.equiv_Real x
          exact ⟨h_big, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
        · right
          push_neg at h_neg h_big
          exact ⟨⟨h_neg, h_big⟩, hfx⟩
    · intro h
      rcases h with (⟨r, hr, hrx⟩ | ⟨r, hr, hrx⟩) | ⟨h_in, hfx⟩
      · apply h_outside_zero
        rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]
        simp only [Set.mem_Icc, not_and, not_le, Set.mem_Iio] at hr ⊢
        intro; linarith
      · apply h_outside_zero
        rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]
        simp only [Set.mem_Icc, not_and, not_le, Set.mem_Ioi] at hr ⊢
        intro; linarith
      · exact hfx
  rw [h_decomp]
  apply LebesgueMeasurable.union
  apply LebesgueMeasurable.union
  · apply IsOpen.measurable
    have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
      show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
    have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
      exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
    let e : ℝ ≃ₜ EuclideanSpace' 1 :=
      { toEquiv := Real.equiv_EuclideanSpace'
        continuous_toFun := hf_cont
        continuous_invFun := hg_cont }
    exact e.isOpenMap (Set.Iio 0) isOpen_Iio
  · apply IsOpen.measurable
    have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
      show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
    have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
      exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
    let e : ℝ ≃ₜ EuclideanSpace' 1 :=
      { toEquiv := Real.equiv_EuclideanSpace'
        continuous_toFun := hf_cont
        continuous_invFun := hg_cont }
    exact e.isOpenMap (Set.Ioi 1) isOpen_Ioi
  · -- Monotonicity case: {x ∈ [0,1] | f_lifted x ≤ t} is a convex set, hence measurable
    have ht_ne_top : t ≠ ⊤ := ne_of_lt (lt_of_lt_of_le ht_lt_one le_top)
    have ht_ne_bot : t ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le ht_pos)
    let t' := t.toReal
    have ht_eq : t = (t' : EReal) := (EReal.coe_toReal ht_ne_top ht_ne_bot).symm
    rw [ht_eq]
    have ht'_pos : 0 < t' := by
      have h : (0:EReal) < t := ht_pos
      rw [ht_eq, EReal.coe_pos] at h; exact h
    have ht'_lt_one : t' < 1 := by
      have h : (t':EReal) < 1 := by rw [← ht_eq]; exact ht_lt_one
      exact EReal.coe_lt_coe_iff.mp h
    let S : Set ℝ := {r ∈ Set.Icc (0:ℝ) 1 | binaryToTernary r ≤ t'}
    have h_set_eq : {x : EuclideanSpace' 1 | EuclideanSpace'.equiv_Real x ∈ Set.Icc 0 1 ∧ f_lifted x ≤ ↑t'} =
        Real.equiv_EuclideanSpace' '' S := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_image, S]
      constructor
      · intro ⟨h_in, hfx⟩
        use EuclideanSpace'.equiv_Real x
        refine ⟨⟨h_in, ?_⟩, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
        simp only [f_lifted] at hfx
        have h_max : max 0 (binaryToTernary (EuclideanSpace'.equiv_Real x)) ≤ t' := by
          rw [EReal.coe_le_coe_iff] at hfx; exact hfx
        exact le_of_max_le_right h_max
      · intro ⟨r, ⟨hr_in, hr_le⟩, hrx⟩
        constructor
        · rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]; exact hr_in
        · rw [← hrx]; simp only [f_lifted, EuclideanSpace'.equiv_Real.apply_symm_apply]
          rw [EReal.coe_le_coe_iff]
          exact max_le (le_of_lt ht'_pos) hr_le
    rw [h_set_eq]
    have h_convex : Convex ℝ S := binaryToTernary_props.monotone_on.convex_le (convex_Icc 0 1) t'
    have h_bounded : Bornology.IsBounded S := (Metric.isBounded_Icc 0 1).subset (fun x hx => hx.1)
    have h_ordConnected : S.OrdConnected := Convex.ordConnected h_convex
    by_cases hS_empty : S = ∅
    · rw [hS_empty]; simp only [Set.image_empty]; exact LebesgueMeasurable.empty
    push_neg at hS_empty
    have h_zero_in_S : (0:ℝ) ∈ S := by
      simp only [S, Set.mem_Icc]
      constructor
      · exact ⟨le_refl 0, zero_le_one⟩
      · rw [binaryToTernary_props.zero_at_zero]; exact le_of_lt ht'_pos
    have h_bdd_above : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
    let a := sSup S
    have ha_mem : a ∈ Set.Icc (0:ℝ) 1 := ⟨
      le_csSup_of_le h_bdd_above h_zero_in_S (le_refl 0),
      csSup_le (Set.nonempty_of_mem h_zero_in_S) (fun x hx => hx.1.2)⟩
    have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
      show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
    have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
      exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
    let e : ℝ ≃ₜ EuclideanSpace' 1 :=
      { toEquiv := Real.equiv_EuclideanSpace'
        continuous_toFun := hf_cont
        continuous_invFun := hg_cont }
    -- S is either [0, a] or [0, a) where a = sSup S; both are measurable
    have h_S_subset_Icc : S ⊆ Set.Icc 0 a := fun x hx => ⟨hx.1.1, le_csSup h_bdd_above hx⟩
    have h_image_Icc : Real.equiv_EuclideanSpace' '' Set.Icc 0 a =
        {x : EuclideanSpace' 1 | EuclideanSpace'.equiv_Real x ∈ Set.Icc 0 a} := by
      ext x; simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro ⟨r, hr, hrx⟩
        rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]; exact hr
      · intro hx
        exact ⟨EuclideanSpace'.equiv_Real x, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
    have h_meas_Icc : LebesgueMeasurable (Real.equiv_EuclideanSpace' '' Set.Icc 0 a) := by
      apply IsClosed.measurable; rw [h_image_Icc]
      exact IsClosed.preimage hg_cont isClosed_Icc
    by_cases ha_in_S : a ∈ S
    · -- S = [0, a]
      have h_S_eq : S = Set.Icc 0 a := by
        ext x
        constructor
        · intro hx; exact h_S_subset_Icc hx
        · intro hx
          exact h_ordConnected.out h_zero_in_S ha_in_S ⟨hx.1, hx.2⟩
      rw [h_S_eq]; exact h_meas_Icc
    · -- S = [0, a)
      have h_S_eq : S = Set.Ico 0 a := by
        ext x
        constructor
        · intro hx
          refine ⟨hx.1.1, ?_⟩
          rcases lt_or_eq_of_le (le_csSup h_bdd_above hx) with hlt | heq
          · exact hlt
          · exfalso; rw [heq] at hx; exact ha_in_S hx
        · intro hx
          have ⟨y, hy_in_S, hx_lt_y⟩ := exists_lt_of_lt_csSup (Set.nonempty_of_mem h_zero_in_S) hx.2
          exact h_ordConnected.out h_zero_in_S hy_in_S ⟨hx.1, le_of_lt hx_lt_y⟩
      rw [h_S_eq]
      have h_image_Ico : Real.equiv_EuclideanSpace' '' Set.Ico 0 a =
          {x : EuclideanSpace' 1 | EuclideanSpace'.equiv_Real x ∈ Set.Ico 0 a} := by
        ext x; simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro ⟨r, hr, hrx⟩
          rw [← hrx, EuclideanSpace'.equiv_Real.apply_symm_apply]; exact hr
        · intro hx
          exact ⟨EuclideanSpace'.equiv_Real x, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
      -- [0, a) = [0, a] \ {a}
      have h_diff : Set.Ico 0 a = Set.Icc 0 a \ {a} := by
        ext x; simp only [Set.mem_Ico, Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨⟨h1, le_of_lt h2⟩, ne_of_lt h2⟩
        · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 h3⟩
      rw [h_diff, Set.image_diff Real.equiv_EuclideanSpace'.injective, Set.diff_eq]
      apply LebesgueMeasurable.inter h_meas_Icc
      apply LebesgueMeasurable.complement
      apply IsNull.measurable
      exact Countable.Lebesgue_measure Nat.one_pos (Set.countable_singleton a |>.image _)

lemma f_lifted_measurable : UnsignedMeasurable f_lifted := by
  -- Apply Lemma 1.3.9(viii): f is measurable iff ∀ t, {x | f(x) ≤ t} is measurable
  have h_iff : UnsignedMeasurable f_lifted ↔ (∀ t, LebesgueMeasurable {x | f_lifted x ≤ t}) :=
    (UnsignedMeasurable.TFAE f_lifted_unsigned).out 0 7
  apply h_iff.mpr
  intro t
  rcases lt_trichotomy t 0 with ht_neg | ht_zero | ht_pos
  · have h_empty : {x | f_lifted x ≤ t} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht_neg (f_lifted_unsigned x)
    rw [h_empty]; exact LebesgueMeasurable.empty
  · subst ht_zero
    have h_eq : {x | f_lifted x ≤ (0 : EReal)} = {x | f_lifted x = 0} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hle; exact le_antisymm hle (f_lifted_unsigned x)
      · intro heq; rw [heq]
    rw [h_eq]; exact f_lifted_zero_set_measurable
  · rcases le_or_gt 1 t with ht_ge_one | ht_lt_one
    · have h_univ : {x | f_lifted x ≤ t} = Set.univ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact le_trans (f_lifted_le_one x) ht_ge_one
      rw [h_univ]; exact IsOpen.measurable isOpen_univ
    · exact sublevel_set_measurable t ht_pos ht_lt_one

/-- Non-measurable F ⊆ [0,1] with binaryToTernary(F) ⊆ Cantor set (Vitali construction). -/
lemma exists_nonmeasurable_with_cantor_image :
    ∃ F : Set ℝ, ∃ A : Set ℝ, F ⊆ Set.Icc 0 1 ∧
    ¬ LebesgueMeasurable (Real.equiv_EuclideanSpace' '' F) ∧
    binaryToTernary '' F ⊆ CantorSet ∧
    F ⊆ A ∧
    A ⊆ Set.Icc 0 1 ∧
    (Set.Icc 0 1 \ A).Countable ∧
    Set.InjOn binaryToTernary A := by
  obtain ⟨A, hA_sub, hA_cocountable, hA_inj, hA_disjoint⟩ := binaryToTernary_props.injective_on_nonterminating
  let F := VitaliSet ∩ A
  use F, A
  refine ⟨?hF_sub, ?hF_nonmeas, ?hF_image, ?hF_sub_A, hA_sub, hA_cocountable, hA_inj⟩
  case hF_sub => intro x hx; exact VitaliSet_subset_unit_interval hx.1
  case hF_image =>
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx_in_Icc : x ∈ Set.Icc (0:ℝ) 1 := hA_sub hx.2
    have h_image := binaryToTernary_props.image_in_cantor ⟨x, hx_in_Icc, rfl⟩
    cases h_image with
    | inl h => exact h
    | inr h =>
      simp only [Set.mem_singleton_iff] at h
      exfalso
      have h_x_eq_0 : x = 0 := binaryToTernary_eq_zero_iff hx_in_Icc |>.mp h
      have h0_dyadic : (0:ℝ) ∈ DyadicRationals := ⟨0, 0, by norm_num, by norm_num⟩
      subst h_x_eq_0
      have h0_in_A : (0:ℝ) ∈ A := hx.2
      have h0_in_inter : (0:ℝ) ∈ A ∩ DyadicRationals := ⟨h0_in_A, h0_dyadic⟩
      rw [hA_disjoint] at h0_in_inter
      exact h0_in_inter
  case hF_nonmeas =>
    intro hF_meas
    have hV_decomp : VitaliSet = F ∪ (VitaliSet \ A) := by
      ext x; simp only [F, Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
      constructor
      · intro hx
        by_cases hxA : x ∈ A
        · left; exact ⟨hx, hxA⟩
        · right; exact ⟨hx, hxA⟩
      · intro hx; rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
    have hVminusA_countable : (VitaliSet \ A).Countable := by
      apply Set.Countable.mono _ hA_cocountable
      intro x hx; exact ⟨VitaliSet_subset_unit_interval hx.1, hx.2⟩
    have hVminusA_null : IsNull (Real.equiv_EuclideanSpace' '' (VitaliSet \ A)) :=
      Countable.Lebesgue_measure Nat.one_pos (Set.Countable.image hVminusA_countable _)
    have hVminusA_meas : LebesgueMeasurable (Real.equiv_EuclideanSpace' '' (VitaliSet \ A)) :=
      IsNull.measurable hVminusA_null
    have hV_meas : LebesgueMeasurable (Real.equiv_EuclideanSpace' '' VitaliSet) := by
      have h_image_union : Real.equiv_EuclideanSpace' '' VitaliSet =
          Real.equiv_EuclideanSpace' '' F ∪ Real.equiv_EuclideanSpace' '' (VitaliSet \ A) := by
        ext x
        simp only [Set.mem_image, Set.mem_union]
        constructor
        · intro ⟨r, hr, hrx⟩
          rw [hV_decomp] at hr
          rcases hr with ⟨hrV, hrA⟩ | ⟨hrV, hrA⟩
          · left; exact ⟨r, ⟨hrV, hrA⟩, hrx⟩
          · right; exact ⟨r, ⟨hrV, hrA⟩, hrx⟩
        · intro h
          rcases h with ⟨r, ⟨hrV, hrA⟩, hrx⟩ | ⟨r, ⟨hrV, hrA⟩, hrx⟩
          · exact ⟨r, hrV, hrx⟩
          · exact ⟨r, hrV, hrx⟩
      rw [h_image_union]; exact LebesgueMeasurable.union hF_meas hVminusA_meas
    exact VitaliSet.nonmeasurable hV_meas
  case hF_sub_A => intro x hx; exact hx.2

end Remark_1_3_10

/-- Remark 1.3.10: The inverse image of a Lebesgue measurable set by a measurable function
    need not be Lebesgue measurable.
    Proof: Let f = binaryToTernary (maps [0,1] → Cantor set), F ⊆ [0,1] non-measurable (Vitali).
    Set E = f(F) ⊆ Cantor set. Then E is null (⊆ null set) hence measurable, but f⁻¹(E) = F
    is non-measurable. (Uses injectivity of f on non-dyadic rationals A ⊇ F.) -/
example : ∃ (f: EuclideanSpace' 1 → EReal) (_hf: UnsignedMeasurable f) (E: Set (EuclideanSpace' 1)) (_hE: LebesgueMeasurable E), ¬ LebesgueMeasurable (f⁻¹' ((Real.toEReal ∘ EuclideanSpace'.equiv_Real) '' E)) := by
  use Remark_1_3_10.f_lifted, Remark_1_3_10.f_lifted_measurable
  obtain ⟨F, A, hF_sub, hF_nonmeas, hF_image, hF_sub_A, hA_sub, hA_cocountable, hA_inj⟩ :=
    Remark_1_3_10.exists_nonmeasurable_with_cantor_image
  use Real.equiv_EuclideanSpace' '' (Remark_1_3_10.binaryToTernary '' F)
  refine ⟨?hE_meas, ?hPreimage_nonmeas⟩
  case hE_meas =>
    apply IsNull.measurable
    apply IsNull.subset CantorSet.null
    intro x hx; obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hF_image hy, rfl⟩
  case hPreimage_nonmeas =>
    -- Key: f is injective on A ⊆ ℝ, F ⊆ A, so f⁻¹(E) ∩ A' = F' where A', F' are A, F in EuclideanSpace'
    intro h_meas
    apply hF_nonmeas
    have h_simplify : (Real.toEReal ∘ EuclideanSpace'.equiv_Real) ''
        (Real.equiv_EuclideanSpace' '' (Remark_1_3_10.binaryToTernary '' F)) =
        Real.toEReal '' (Remark_1_3_10.binaryToTernary '' F) := by
      ext z; simp only [Set.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨p, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, by simp⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨Real.equiv_EuclideanSpace' y, ⟨y, hy, rfl⟩, by simp⟩
    rw [h_simplify] at h_meas
    -- A', F' := A, F viewed in EuclideanSpace' 1 (via ℝ ≃ EuclideanSpace' 1)
    let A' := Real.equiv_EuclideanSpace' '' A
    let F' := Real.equiv_EuclideanSpace' '' F
    have h_preimage_inter : Remark_1_3_10.f_lifted ⁻¹' (Real.toEReal '' (Remark_1_3_10.binaryToTernary '' F)) ∩ A' = F' := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, A', F']
      constructor
      · rintro ⟨⟨z, ⟨w, hw, rfl⟩, hfp⟩, a, ha, rfl⟩
        -- p = Real.equiv_EuclideanSpace' a, a ∈ A
        -- f p = Real.toEReal z where z = binaryToTernary w, w ∈ F
        -- So binaryToTernary a = z = binaryToTernary w
        use a
        refine ⟨?_, rfl⟩
        -- Show a ∈ F using injectivity
        have ha_in_Icc : a ∈ Set.Icc (0:ℝ) 1 := hA_sub ha
        have hw_in_A : w ∈ A := hF_sub_A hw
        have hw_in_Icc : w ∈ Set.Icc (0:ℝ) 1 := hA_sub hw_in_A
        -- f p = binaryToTernary a (since a ∈ [0,1] and binaryToTernary a ≥ 0)
        have hf_eq : Remark_1_3_10.f_lifted (Real.equiv_EuclideanSpace' a) =
            Real.toEReal (Remark_1_3_10.binaryToTernary a) := by
          simp only [Remark_1_3_10.f_lifted, EuclideanSpace'.equiv_Real.apply_symm_apply]
          congr 1
          exact max_eq_right (Remark_1_3_10.binaryToTernary_props.nonneg a)
        rw [hf_eq] at hfp
        have h_eq_values : Remark_1_3_10.binaryToTernary a = Remark_1_3_10.binaryToTernary w :=
          (EReal.coe_injective hfp).symm
        have ha_eq_w : a = w := hA_inj ha hw_in_A h_eq_values
        rw [ha_eq_w]; exact hw
      · rintro ⟨r, hr, rfl⟩
        constructor
        · -- f (Real.equiv_EuclideanSpace' r) ∈ Real.toEReal '' (binaryToTernary '' F)
          use Remark_1_3_10.binaryToTernary r
          refine ⟨⟨r, hr, rfl⟩, ?_⟩
          simp only [Remark_1_3_10.f_lifted, EuclideanSpace'.equiv_Real.apply_symm_apply]
          congr 1
          exact (max_eq_right (Remark_1_3_10.binaryToTernary_props.nonneg r)).symm
        · exact ⟨r, hF_sub_A hr, rfl⟩
    -- A' is measurable: [0,1]' \ A' is countable hence null, use of_ae_eq with [0,1]'
    have hA'_meas : LebesgueMeasurable A' := by
      let Icc' := Real.equiv_EuclideanSpace' '' Set.Icc (0:ℝ) 1
      have hIcc'_meas : LebesgueMeasurable Icc' := IsClosed.measurable <| by
        have : Icc' = EuclideanSpace'.equiv_Real ⁻¹' Set.Icc 0 1 := by
          ext x; simp only [Icc', Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨r, hr, rfl⟩; simp [hr]
          · intro hx; exact ⟨_, hx, EuclideanSpace'.equiv_Real.symm_apply_apply x⟩
        exact this ▸ IsClosed.preimage (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) _) isClosed_Icc
      have h_diff_null : IsNull (Icc' \ A') := by
        apply Countable.Lebesgue_measure Nat.one_pos
        have : Icc' \ A' = Real.equiv_EuclideanSpace' '' (Set.Icc 0 1 \ A) := by
          ext x; simp only [Set.mem_diff, Set.mem_image, Icc', A']
          constructor
          · rintro ⟨⟨r, hr, rfl⟩, hn⟩
            exact ⟨r, ⟨hr, fun ha => hn ⟨r, ha, rfl⟩⟩, rfl⟩
          · rintro ⟨r, ⟨hr, hn⟩, rfl⟩
            exact ⟨⟨r, hr, rfl⟩, fun ⟨s, hs, he⟩ =>
              hn (Real.equiv_EuclideanSpace'.injective he.symm ▸ hs)⟩
        exact this ▸ Set.Countable.image hA_cocountable _
      have h_A'_sub : A' ⊆ Icc' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, hA_sub ha, rfl⟩
      -- A' ∩ (Icc' \ A')ᶜ = Icc' ∩ (Icc' \ A')ᶜ = A' (since A' ⊆ Icc')
      refine LebesgueMeasurable.of_ae_eq hIcc'_meas h_diff_null ?_
      ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
      constructor
      · intro ⟨hx, _⟩; exact ⟨h_A'_sub hx, fun ⟨_, h⟩ => h hx⟩
      · intro ⟨hi, hn⟩; push_neg at hn; exact ⟨hn hi, fun ⟨_, h⟩ => h (hn hi)⟩
    -- F' = f⁻¹'(...) ∩ A' is measurable
    have : F' = Remark_1_3_10.f_lifted ⁻¹' (Real.toEReal '' (Remark_1_3_10.binaryToTernary '' F)) ∩ A' :=
      h_preimage_inter.symm
    simp only [F'] at this
    rw [this]
    exact LebesgueMeasurable.inter h_meas hA'_meas

/-- Definition 1.3.11 (Complex measurability)-/
def ComplexMeasurable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ∃ (g: ℕ → EuclideanSpace' d → ℂ), (∀ n, ComplexSimpleFunction (g n)) ∧ (PointwiseConvergesTo g f)

def RealMeasurable {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := ∃ (g: ℕ → EuclideanSpace' d → ℝ), (∀ n, RealSimpleFunction (g n)) ∧ (PointwiseConvergesTo g f)

theorem RealMeasurable.iff {d:ℕ} {f: EuclideanSpace' d → ℝ} : RealMeasurable f ↔ ComplexMeasurable (Real.complex_fun f) := by
  constructor
  -- Forward: RealMeasurable f → ComplexMeasurable (Real.complex_fun f)
  · intro ⟨g, hg_simple, hg_conv⟩
    use fun n => Real.complex_fun (g n)
    constructor
    · intro n; exact (hg_simple n).toComplex
    · intro x
      simp only [Real.complex_fun]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hg_conv x)
  -- Backward: ComplexMeasurable (Real.complex_fun f) → RealMeasurable f
  · intro ⟨g, hg_simple, hg_conv⟩
    use fun n => Complex.re_fun (g n)
    constructor
    · intro n; exact (hg_simple n).re
    · intro x
      simp only [Complex.re_fun]
      have h := hg_conv x
      simp only [Real.complex_fun] at h
      have h' := Complex.continuous_re.continuousAt.tendsto.comp h
      simp only [Complex.ofReal_re] at h'
      exact h'

theorem ComplexMeasurable.iff {d:ℕ} {f: EuclideanSpace' d → ℂ} : ComplexMeasurable f ↔ RealMeasurable (Complex.re_fun f) ∧ RealMeasurable (Complex.im_fun f) := by
  constructor
  -- Forward: ComplexMeasurable f → RealMeasurable (re ∘ f) ∧ RealMeasurable (im ∘ f)
  · intro ⟨g, hg_simple, hg_conv⟩
    constructor
    · use fun n => Complex.re_fun (g n)
      exact ⟨fun n => (hg_simple n).re, fun x => Complex.continuous_re.continuousAt.tendsto.comp (hg_conv x)⟩
    · use fun n => Complex.im_fun (g n)
      exact ⟨fun n => (hg_simple n).im, fun x => Complex.continuous_im.continuousAt.tendsto.comp (hg_conv x)⟩
  -- Backward: RealMeasurable (re ∘ f) ∧ RealMeasurable (im ∘ f) → ComplexMeasurable f
  · intro ⟨⟨g_re, hg_re_simple, hg_re_conv⟩, ⟨g_im, hg_im_simple, hg_im_conv⟩⟩
    use fun n => Real.complex_fun (g_re n) + Complex.I • Real.complex_fun (g_im n)
    constructor
    · intro n
      exact ((hg_re_simple n).toComplex).add ((hg_im_simple n).toComplex.smul Complex.I)
    · intro x
      have h_re := hg_re_conv x; simp only [Complex.re_fun] at h_re
      have h_im := hg_im_conv x; simp only [Complex.im_fun] at h_im
      have h_re' := Complex.continuous_ofReal.continuousAt.tendsto.comp h_re
      have h_im' := Complex.continuous_ofReal.continuousAt.tendsto.comp h_im
      have h_sum : Filter.Tendsto (fun n => Complex.ofReal (g_re n x) + Complex.I * Complex.ofReal (g_im n x))
          Filter.atTop (nhds (Complex.ofReal (f x).re + Complex.I * Complex.ofReal (f x).im)) :=
        h_re'.add (h_im'.const_mul Complex.I)
      have h_eq : Complex.ofReal (f x).re + Complex.I * Complex.ofReal (f x).im =
                  Complex.ofReal (f x).re + Complex.ofReal (f x).im * Complex.I := by ring
      rw [h_eq, Complex.re_add_im] at h_sum
      simp only [Pi.add_apply, Pi.smul_apply, Real.complex_fun, smul_eq_mul]
      exact h_sum

/-- Exercise 1.3.7 -/
theorem RealMeasurable.TFAE {d:ℕ} {f: EuclideanSpace' d → ℝ}:
    [
      RealMeasurable f,
      ∃ (g: ℕ → EuclideanSpace' d → ℝ), (∀ n, RealSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f),
      UnsignedMeasurable (EReal.pos_fun f) ∧ UnsignedMeasurable (EReal.neg_fun f),
      ∀ U: Set ℝ, IsOpen U → MeasurableSet (f⁻¹' U),
      ∀ K: Set ℝ, IsClosed K → MeasurableSet (f⁻¹' K)
    ].TFAE
  := by sorry

theorem ComplexMeasurable.TFAE {d:ℕ} {f: EuclideanSpace' d → ℂ}:
    [
      ComplexMeasurable f,
      ∃ (g: ℕ → EuclideanSpace' d → ℂ), (∀ n, ComplexSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f),
      RealMeasurable (Complex.re_fun f) ∧ RealMeasurable (Complex.im_fun f),
      UnsignedMeasurable (EReal.pos_fun (Complex.re_fun f)) ∧ UnsignedMeasurable (EReal.neg_fun (Complex.im_fun f)) ∧ UnsignedMeasurable (EReal.pos_fun (Complex.im_fun f)) ∧ UnsignedMeasurable (EReal.neg_fun (Complex.re_fun f)),
      ∀ U: Set ℂ, IsOpen U → MeasurableSet (f⁻¹' U),
      ∀ K: Set ℂ, IsClosed K → MeasurableSet (f⁻¹' K)
    ].TFAE
  := by sorry

/-- Exercise 1.3.8(i) -/
theorem Continuous.RealMeasurable {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: Continuous f) : RealMeasurable f := by sorry

theorem Continuous.ComplexMeasurable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: Continuous f) : ComplexMeasurable f := by sorry

/-- Exercise 1.3.8(ii) -/
theorem UnsignedSimpleFunction.iff' {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f) : UnsignedSimpleFunction f ↔ UnsignedMeasurable f ∧ Finite (f '' Set.univ) := by sorry

/-- Exercise 1.3.8(iii) -/
theorem RealMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (heq: AlmostEverywhereEqual f g) : RealMeasurable g := by sorry

theorem ComplexMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (heq: AlmostEverywhereEqual f g) : ComplexMeasurable g := by sorry

/-- Exercise 1.3.8(iv) -/
theorem RealMeasurable.aeLimit {d:ℕ} {f: EuclideanSpace' d → ℝ} (g: ℕ → EuclideanSpace' d → ℝ) (hf: ∀ n, RealMeasurable (g n)) (heq: PointwiseAeConvergesTo g f) : RealMeasurable f := by sorry

theorem ComplexMeasurable.aeLimit {d:ℕ} {f: EuclideanSpace' d → ℂ} (g: ℕ → EuclideanSpace' d → ℂ) (hf: ∀ n, ComplexMeasurable (g n)) (heq: PointwiseAeConvergesTo g f) : ComplexMeasurable f := by sorry

/-- Exercise 1.3.8(v) -/
theorem RealMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) {φ: ℝ → ℝ} (hφ: Continuous φ)  : RealMeasurable (φ ∘ f) := by sorry

theorem ComplexMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) {φ: ℂ → ℂ} (hφ: Continuous φ)  : ComplexMeasurable (φ ∘ f) := by sorry

/-- Exercise 1.3.8(vi) -/
theorem RealMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (hg: RealMeasurable g) : RealMeasurable (f + g) := by sorry

theorem ComplexMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (hg: ComplexMeasurable g) : ComplexMeasurable (f + g) := by sorry

/-- Exercise 1.3.8(vi) -/
theorem RealMeasurable.sub {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (hg: RealMeasurable g) : RealMeasurable (f - g) := by sorry

theorem ComplexMeasurable.sub {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (hg: ComplexMeasurable g) : ComplexMeasurable (f - g) := by sorry

/-- Exercise 1.3.8(vi) -/
theorem RealMeasurable.mul {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (hg: RealMeasurable g) : RealMeasurable (f * g) := by sorry

theorem ComplexMeasurable.mul {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (hg: ComplexMeasurable g) : ComplexMeasurable (f * g) := by sorry


open Classical in
/-- Exercise 1.3.9 -/
theorem RealMeasurable.riemann_integrable {f: ℝ → ℝ} {I: BoundedInterval} (hf: RiemannIntegrableOn f I) : RealMeasurable ((fun x ↦ if x ∈ I.toSet then f x else 0) ∘ EuclideanSpace'.equiv_Real) := by sorry
