import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by sorry

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by sorry

theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  sorry

theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  sorry

theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  sorry

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := {
  r := EqualCard,
  iseqv := {refl, symm, trans}
}

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by sorry

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by sorry

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
  (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by sorry

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0)
    rw [mem_Fin]
    use 0, (by linarith); rfl
  rw [has_card_iff] at hX
  obtain ⟨ f, hf ⟩ := hX
  sorry
  -- obtain a contradiction from the fact that `f` is a bijection  from the empty set to a
  -- non-empty set.

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by sorry

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof is written to follow the structure of the original text, though with some extra
  -- notations to track some coercions that are "invisible" in the human-readable proof.
  rw [has_card_iff] at hX; obtain ⟨ f, hf ⟩ := hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun y ↦ ⟨ y.val, by have := y.property; simp [X'] at this; tauto ⟩
  have := (f x).property
  rw [mem_Fin] at this; obtain ⟨ m₀, hm₀, hm₀f ⟩ := this

  set g : X' → Fin (n-1) := fun y ↦ by
    have hy := y.property
    simp [X'] at hy; obtain ⟨ hy1, hy2 ⟩ := hy
    have := (f ⟨ y.val, hy1⟩).property
    rw [mem_Fin] at this
    have ⟨ hmn, hmm ⟩ := this.choose_spec
    set m' := this.choose
    cases m'.decLt m₀ with
    | isTrue hlt => exact Fin_mk _ m' (by omega)
    | isFalse hlt =>
      have : m' ≠ m₀ := by
        contrapose! hy2
        rwa [hy2,←hm₀f,Subtype.val_inj, hf.injective.eq_iff,←Subtype.val_inj] at hmm
      exact Fin_mk _ (m'-1) (by omega)
  have hg : Function.Bijective g := by sorry
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2
    rw [has_card_zero] at h1; contrapose! h1
    exact pos_card_nonempty (by omega) h2
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  obtain ⟨ x, hx ⟩ := nonempty_def this
  set x':X := ⟨ x, hx ⟩
  have : m ≥ 1 := by
    by_contra! hm; simp at hm
    rw [hm, has_card_zero] at h2; contradiction
  have hc : (X \ {x}).has_card (n+1-1) := card_erase (by omega) h1 x'
  have hc' : (X \ {x}).has_card (m-1) := card_erase this h2 x'
  simp at hc; specialize hn hc hc'
  omega

example : ({0,1,2}:Set).has_card 3 := by sorry

example : ({3,4}:Set).has_card 2 := by sorry

example : ¬ ({0,1,2}:Set) ≈ ({3,4}:Set) := by sorry

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by sorry

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; obtain ⟨n, hn⟩ := this
  simp [has_card] at hn; replace hn := Setoid.symm hn
  simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  obtain ⟨ f, hf ⟩ := hn
  obtain ⟨ M, hM ⟩ := bounded_on_finite f
  replace hf := hf.surjective (M+1:ℕ)
  have : ∀ i, f i ≠ (M+1:ℕ) := by
    intro i; specialize hM i; contrapose! hM
    apply_fun nat_equiv.symm at hM
    simp_all
  tauto

/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable abbrev SetTheory.Set.card (X:Set) : ℕ := by
  classical
  exact if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card (X:Set) (n: ℕ): X.has_card n → X.card = n := by
  intro h
  rw [card]
  have hf : X.finite := by rw [finite]; use n
  simp only [hf, ↓reduceDIte]
  generalize_proofs a
  have ha := a.choose_spec
  exact card_uniq ha h

theorem SetTheory.Set.card_to_has_card (X:Set) (n: ℕ) (hn: n ≠ 0): X.card = n → X.has_card n := by
  intro h
  rw [← h]
  exact has_card_card (by
    by_contra! h0
    simp only [card, h0, ↓reduceDIte] at h
    have := h.symm
    contradiction
  )

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by sorry

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by sorry

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by sorry

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by sorry

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by sorry

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by sorry

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by sorry

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by sorry

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ^ Y).finite ∧ (X ^ Y).card = X.card ^ Y.card := by sorry

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.card_eq_zero {X:Set} (hX: X.finite) :
    X.card = 0 ↔ X = ∅ := by sorry

/-- Exercise 3.6.5 -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by sorry

/-- Exercise 3.6.6 -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by sorry

example (a b c:ℕ): (a^b)^c = a^(b*c) := by sorry

example (a b c:ℕ): (a^b) * a^c = a^(b+c) := by sorry

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := sorry

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by sorry

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by  sorry

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by sorry

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by sorry

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by sorry

/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by sorry

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by sorry

end Chapter3
