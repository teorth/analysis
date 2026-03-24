import Mathlib.Tactic

/-!
# Analysis I, Section 8.1: Countability

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Custom notions for "equal cardinality", "countable", and "at most countable".  Note that Mathlib's
`Countable` typeclass corresponds to what we call "at most countable" in this text.
- Countability of the integers and rationals.

Note that as the Chapter 3 set theory has been deprecated, we will not re-use relevant constructions from that theory here, replacing them with Mathlib counterparts instead.

-/

namespace Chapter8

/-- The definition of equal cardinality. For simplicity we restrict attention to the Type 0 universe.
This is analogous to `Chapter3.SetTheory.Set.EqualCard`, but we are not using the latter since
the Chapter 3 set theory is deprecated. -/
abbrev EqualCard (X Y : Type) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Relation with Mathlib's `Equiv` concept -/
theorem EqualCard.iff {X Y : Type} : EqualCard X Y ↔ Nonempty (X ≃ Y) := by
  simp [EqualCard]; constructor
  . intro ⟨ f, hf ⟩; exact ⟨ .ofBijective f hf ⟩
  intro ⟨ e ⟩; exact ⟨ e.toFun, e.bijective ⟩

/-- Equivalence with Mathlib's `Cardinal.mk` concept -/
theorem EqualCard.iff' {X Y : Type} : EqualCard X Y ↔ Cardinal.mk X = Cardinal.mk Y := by
  simp [Cardinal.eq, iff]

theorem EqualCard.refl (X : Type) : EqualCard X X := sorry

theorem EqualCard.symm {X Y : Type} (hXY : EqualCard X Y) : EqualCard Y X := by
  sorry

theorem EqualCard.trans {X Y Z : Type} (hXY : EqualCard X Y) (hYZ : EqualCard Y Z) :
  EqualCard X Z := by
  sorry

instance EqualCard.instSetoid : Setoid Type := ⟨ EqualCard, ⟨ refl, symm, trans ⟩ ⟩

theorem EqualCard.univ (X : Type) : EqualCard (.univ : Set X) X :=
  ⟨ Subtype.val, Subtype.val_injective, by intro _; aesop ⟩

abbrev CountablyInfinite (X : Type) : Prop := EqualCard X ℕ

abbrev AtMostCountable (X : Type) : Prop := CountablyInfinite X ∨ Finite X

theorem CountablyInfinite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  CountablyInfinite X ↔ CountablyInfinite Y := ⟨ hXY.symm.trans, hXY.trans ⟩

theorem Finite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Finite X ↔ Finite Y := by obtain ⟨ f, hf ⟩ := hXY; exact (Equiv.ofBijective f hf).finite_iff

theorem AtMostCountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  AtMostCountable X ↔ AtMostCountable Y := by
  simp [AtMostCountable, CountablyInfinite.equiv hXY, Finite.equiv hXY]

/-- Equivalence with Mathlib's `Denumerable` concept (cf. Remark 8.1.2) -/
theorem CountablyInfinite.iff (X : Type) : CountablyInfinite X ↔ Nonempty (Denumerable X) := by
  simp [CountablyInfinite, EqualCard.iff]; constructor
  . intro ⟨ e ⟩; exact ⟨ Denumerable.mk' e ⟩
  intro ⟨ h ⟩; exact ⟨ h.eqv X ⟩

/-- Equivalence with Mathlib's `Countable` typeclass -/
theorem CountablyInfinite.iff' (X : Type) : CountablyInfinite X ↔ Countable X ∧ Infinite X := by
  rw [iff, nonempty_denumerable_iff]

theorem CountablyInfinite.toCountable {X : Type} (hX: CountablyInfinite X) : Countable X := by
  simp_all [iff']

theorem CountablyInfinite.toInfinite {X : Type} (hX: CountablyInfinite X) : Infinite X := by
  simp_all [iff']

theorem AtMostCountable.iff (X : Type) : AtMostCountable X ↔ Countable X := by
  observe h1 : CountablyInfinite X ↔ Countable X ∧ Infinite X
  observe h2 : Finite X ∨ Infinite X
  observe h3 : Finite X → Countable X
  tauto

theorem CountablyInfinite.iff_image_inj {A:Type} (X: Set A) : CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' .univ := by
  constructor
  . intro ⟨ g, hg ⟩
    choose f hleft hright using Function.bijective_iff_has_inverse.mp hg
    refine ⟨ ⟨ Subtype.val ∘ f, ?_ ⟩, ?_ ⟩
    . intro x y hxy; apply hright.injective; simp_all [Subtype.val_inj]
    ext; simp; constructor
    . intro hx; use g ⟨ _, hx ⟩; simp [hleft _]
    rintro ⟨ _, rfl ⟩; aesop
  intro ⟨ f, hf ⟩
  have := Function.leftInverse_invFun (Function.Embedding.injective f)
  use (Function.invFun f) ∘ Subtype.val; split_ands
  . rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h; grind
  intro n; use ⟨ f n, by aesop ⟩; grind

/-- Examples 8.1.3 -/
example : CountablyInfinite ℕ := by sorry

example : CountablyInfinite (.univ \ {0}: Set ℕ) := by sorry

example : CountablyInfinite ((fun n:ℕ ↦ 2*n) '' .univ) := by sorry


/-- Proposition 8.1.4 (Well ordering principle / Exercise 8.1.2 -/
theorem Nat.exists_unique_min {X : Set ℕ} (hX : X.Nonempty) :
  ∃! m ∈ X, ∀ n ∈ X, m ≤ n := by
  sorry

def Int.exists_unique_min : Decidable (∀ (X : Set ℤ) (hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def NNRat.exists_unique_min : Decidable (∀ (X : Set NNRat) (hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


open Classical in
noncomputable abbrev Nat.min (X : Set ℕ) : ℕ := if hX : X.Nonempty then (exists_unique_min hX).exists.choose else 0

theorem Nat.min_spec {X : Set ℕ} (hX : X.Nonempty) : min X ∈ X ∧ ∀ n ∈ X, min X ≤ n := by
  simp [hX, min]; exact (exists_unique_min hX).exists.choose_spec

theorem Nat.min_eq {X : Set ℕ} (hX : X.Nonempty) {a:ℕ} (ha : a ∈ X ∧ ∀ n ∈ X, a ≤ n) : min X = a :=
  (exists_unique_min hX).unique (min_spec hX) ha

@[simp]
theorem Nat.min_empty : min ∅ = 0 := by simp [Nat.min]

example : Nat.min ((fun n ↦ 2*n) '' (.Ici 1)) = 2 := by sorry

theorem Nat.min_eq_sInf {X : Set ℕ} (hX : X.Nonempty) : min X = sInf X := by
  sorry

open Classical in
/-- Equivalence with Mathlib's `Nat.find` method -/
theorem Nat.min_eq_find {X : Set ℕ} (hX : X.Nonempty) : min X = Nat.find hX := by
  symm; rw [Nat.find_eq_iff]; have := min_spec hX; grind

/-- Proposition 8.1.5 -/
theorem Nat.monotone_enum_of_infinite (X : Set ℕ) [Infinite X] : ∃! f : ℕ → X, Function.Bijective f ∧ StrictMono f := by
  -- This proof is written to follow the structure of the original text.
  let a : ℕ → ℕ := Nat.strongRec (fun n a ↦ min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m h })
  have ha : ∀ n, a n = min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := Nat.strongRec.eq_def _
  have ha_infinite (n:ℕ) : Infinite { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
    sorry
  have ha_nonempty (n:ℕ) : { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m }.Nonempty := Set.Nonempty.of_subtype
  have ha_mono : StrictMono a := by
    sorry
  have ha_injective : Function.Injective a := by
    sorry
  have haX (n:ℕ) : a n ∈ X := by
    sorry
  set f : ℕ → X := fun n ↦ ⟨ a n, haX n ⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy; simp [f] at hxy; solve_by_elim
  have hf_surjective : Function.Surjective f := by
    intro ⟨ x, hx ⟩; simp [f]; by_contra
    have h1 (n:ℕ) : x ∈ { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
      sorry
    have h2 (n:ℕ) : x ≥ a n := by
      rw [ha n]; exact ge_iff_le.mpr ((min_spec (ha_nonempty n)).2 _ (h1 n))
    have h3 (n:ℕ) : a n ≥ n := by
      sorry
    have h4 (n:ℕ) : x ≥ n := (h3 n).trans (h2 n)
    linarith [h4 (x+1)]
  apply ExistsUnique.intro _ ⟨ ⟨ hf_injective, hf_surjective ⟩, ha_mono ⟩
  intro g ⟨ hg_bijective, hg_mono ⟩; by_contra!
  replace : { n | g n ≠ f n }.Nonempty := by
    contrapose! this
    apply funext; simpa [Set.eq_empty_iff_forall_notMem] using this
  set m := min { n | g n ≠ f n }
  have hm : g m ≠ f m := (min_spec this).1
  have hm' {n:ℕ} (hn: n < m) : g n = f n := by by_contra hgfn; linarith [(min_spec this).2 n (by simp [hgfn])]
  have hgm : g m = min { x ∈ X | ∀ (n:ℕ) (h:n < m), x ≠ a n } := by
    sorry
  rw [←ha m] at hgm; contrapose! hm; exact Subtype.val_injective hgm

theorem Nat.countable_of_infinite (X : Set ℕ) [Infinite X] : CountablyInfinite X := by
  have := (monotone_enum_of_infinite X).exists
  exact EqualCard.symm ⟨ this.choose, this.choose_spec.1 ⟩

/-- Corollary 8.1.6 -/
theorem Nat.atMostCountable_subset (X: Set ℕ) : AtMostCountable X := by
  obtain _ | _ := finite_or_infinite X
  . tauto
  simp [AtMostCountable, countable_of_infinite]

/-- Corollary 8.1.7 -/
theorem AtMostCountable.subset {X: Type} (hX : AtMostCountable X) (Y: Set X) : AtMostCountable Y := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ f, hf ⟩ | hX := hX
  . let f' : Y → f '' Y := fun y ↦ ⟨ f y, by aesop ⟩
    have hf' : Function.Bijective f' := by
      sorry
    rw [equiv ⟨ _, hf' ⟩ ]; apply Nat.atMostCountable_subset
  simp [AtMostCountable, show Finite Y by infer_instance]

theorem AtMostCountable.subset' {A: Type} {X Y: Set A} (hX: AtMostCountable X) (hY: Y ⊆ X) : AtMostCountable Y := by
  refine' (equiv ⟨ fun y ↦ ⟨ ↑↑y, y.property ⟩, _, _ ⟩).mp (subset hX { x : X | ↑x ∈ Y })
  . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _; simp_all
  intro ⟨ y, hy ⟩; use ⟨ ⟨ y, hY hy ⟩, by aesop ⟩

/-- Proposition 8.1.8 / Exercise 8.1.4 -/
theorem AtMostCountable.image_nat (Y: Type) (f: ℕ → Y) : AtMostCountable (f '' .univ) := by
  sorry

/-- Corollary 8.1.9 / Exercise 8.1.5 -/
theorem AtMostCountable.image {X:Type} (hX: CountablyInfinite X) {Y: Type} (f: X → Y) : AtMostCountable (f '' .univ) := by
  sorry

/-- Proposition 8.1.10 / Exercise 8.1.7 -/
theorem CountablyInfinite.union {A:Type} {X Y: Set A} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X ∪ Y: Set A) := by
  sorry

/-- Corollary 8.1.11 --/
theorem Int.countablyInfinite : CountablyInfinite ℤ := by
  -- This proof is written to follow the structure of the original text.
  have h1 : CountablyInfinite {n:ℤ | n ≥ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    . intro h; use n.toNat; simp [h]
  have h2 : CountablyInfinite {n:ℤ | n ≤ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (-↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    intro h; use (-n).toNat; simp [h]
  have : CountablyInfinite (.univ : Set ℤ) := by
    convert h1.union h2; ext; simp; omega
  rwa [←CountablyInfinite.equiv (.univ _)]

/-- Lemma 8.1.12 -/
theorem CountablyInfinite.lower_diag : CountablyInfinite { n : ℕ × ℕ | n.2 ≤ n.1 } := by
  -- This proof is written to follow the structure of the original text.
  let A := { n : ℕ × ℕ | n.2 ≤ n.1 }
  let a : ℕ → ℕ := fun n ↦ ∑ m ∈ .range (n+1), m
  have ha : StrictMono a := by
    sorry
  let f : A → ℕ := fun ⟨ (n, m), _ ⟩ ↦ a n + m
  have hf : Function.Injective f := by
    rintro ⟨ ⟨ n, m ⟩, hnm ⟩ ⟨ ⟨ n',m'⟩, hnm' ⟩ h
    simp [A,f] at hnm hnm' ⊢ h
    obtain hnn' | rfl | hnn' := lt_trichotomy n n'
    . have : a n' + m' > a n + m := by calc
        _ ≥ a n' := by linarith
        _ ≥ a (n+1) := ha.monotone (by linarith)
        _ = a n + (n + 1) := Finset.sum_range_succ id _
        _ > a n + m := by linarith
      linarith
    . simpa using h
    have : a n + m > a n' + m' := by calc
        _ ≥ a n := by linarith
        _ ≥ a (n'+1) := ha.monotone (by linarith)
        _ = a n' + (n' + 1) := Finset.sum_range_succ id _
        _ > a n' + m' := by linarith
    linarith
  let f' : A → f '' .univ := fun p ↦ ⟨ f p, by aesop ⟩
  have hf' : Function.Bijective f' := by
    constructor
    . intro p q hpq; simp [f'] at hpq; solve_by_elim
    intro ⟨ l, hl ⟩; simp at hl
    obtain ⟨ n, m, q, rfl ⟩ := hl; use ⟨ (n, m), q ⟩
  have : AtMostCountable A := by rw [AtMostCountable.equiv ⟨ _, hf' ⟩]; apply Nat.atMostCountable_subset
  have hfin : ¬ Finite A := by
    sorry
  simp [AtMostCountable] at this; tauto

/-- Corollary 8.1.13 -/
theorem CountablyInfinite.prod_nat : CountablyInfinite (ℕ × ℕ) := by
  have upper_diag : CountablyInfinite { n : ℕ × ℕ | n.1 ≤ n.2 } := by
    refine (equiv ⟨ fun ⟨ (n, m), _ ⟩ ↦ ⟨ (m, n), by aesop ⟩, ?_, ?_ ⟩).mp lower_diag
    . intro ⟨ (_, _), _ ⟩ ⟨ (_, _), _ ⟩ _; aesop
    intro ⟨ (n, m), _ ⟩; use ⟨ (m, n), by aesop ⟩
  have : CountablyInfinite (.univ : Set (ℕ × ℕ)) := by
    convert union lower_diag upper_diag; ext ⟨ n, m ⟩; simp; omega
  exact (equiv (.univ _)).mp this

/-- Corollary 8.1.14 / Exercise 8.1.8 -/
theorem CountablyInfinite.prod {X Y:Type} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X × Y) := by
  sorry

/-- Corollary 8.1.15 -/
theorem Rat.countablyInfinite : CountablyInfinite ℚ := by
  -- This proof is written to follow the structure of the original text.
  have : CountablyInfinite { n:ℤ | n ≠ 0 } := by
    sorry
  apply Int.countablyInfinite.prod at this
  let f : ℤ × { n:ℤ | n ≠ 0 } → ℚ := fun (a,b) ↦ (a/b:ℚ)
  replace := AtMostCountable.image this f
  have h : f '' .univ = .univ := by
    sorry
  rcases this with h1 | h2
  · have h1' : CountablyInfinite (Set.univ : Set ℚ) := h ▸ h1
    rwa [CountablyInfinite.equiv (EqualCard.univ _)] at h1'
  · have h2' : Finite (Set.univ : Set ℚ) := h ▸ h2
    rw [Set.finite_coe_iff, Set.finite_univ_iff] at h2'
    exact absurd h2' (not_finite_iff_infinite.mpr inferInstance)

/-- Exercise 8.1.1 -/
example (X: Type) : Infinite X ↔ ∃ Y : Set X, Y ≠ .univ ∧ EqualCard Y X := by
  sorry

/-- Exercise 8.1.6 -/
example (A: Type) : AtMostCountable A ↔ ∃ f : A → ℕ, Function.Injective f := by
  sorry

/-- Exercise 8.1.9 -/
example {I X:Type} (hI: AtMostCountable I) (A: I → Set X) (hA: ∀ i, AtMostCountable (A i)) :
  AtMostCountable (⋃ i, A i) := by sorry

/-- Exercise 8.1.10.  Note the lack of the `noncomputable` keyword in the `abbrev`. -/
abbrev explicit_bijection : ℕ → ℚ := sorry

theorem explicit_bijection_spec : Function.Bijective explicit_bijection := by sorry

end Chapter8
