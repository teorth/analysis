import Mathlib.Tactic

/-!
# API for ExistsUnique

Here we review some of the API provided for {name}`ExistsUnique` in Mathlib, and provide some additional tools.  (Some of these might be suitable for upstreaming to Mathlib.)

-/


#check existsUnique_of_exists_of_unique
#check ExistsUnique.exists
#check ExistsUnique.unique
#check ExistsUnique.intro

/-- This implements the axiom of unique choice. -/
noncomputable def ExistsUnique.choose {α: Sort*} {p: α → Prop} (h : ∃! x, p x) : α := h.exists.choose

theorem ExistsUnique.choose_spec {α: Sort*} {p: α → Prop} (h : ∃! x, p x) :
  p h.choose := h.exists.choose_spec

theorem ExistsUnique.choose_eq {α: Sort*} {p: α → Prop} (h : ∃! x, p x) {x : α} (hx : p x) :
  h.choose = x := h.unique h.choose_spec hx

theorem ExistsUnique.choose_iff {α: Sort*} {p: α → Prop} (h : ∃! x, p x) (x : α):
  p x ↔ x = h.choose :=
  ⟨ by intro hx; exact (h.choose_eq hx).symm, by rintro rfl; exact h.choose_spec ⟩

theorem ExistsUnique.choose_eq_choose {α: Sort*} {p: α → Prop} (h : ∃! x, p x) : Exists.choose h = h.choose := by
  rw [←choose_iff]; exact (Exists.choose_spec h).1


/-- An alternate form of the axiom of unique choice.   -/
noncomputable def Subsingleton.choose {α: Sort*} [Subsingleton α] [hn: Nonempty α] : α := hn.some

theorem Subsingleton.choose_spec {α: Sort*} [hs: Subsingleton α] [Nonempty α] (x:α) : x = hs.choose := Subsingleton.elim _ _

/-- The equivalence between {name}`ExistsUnique` and {name}`Subsingleton`/{name}`Nonempty` does not require choice. -/
theorem ExistsUnique.iff_subsingleton_nonempty  {α: Sort*} {p: α → Prop} :
  (∃! x, p x) ↔ (Subsingleton {x // p x} ∧ Nonempty {x // p x}) := by
  constructor
  · intro h; obtain ⟨ x₀, hx₀ ⟩ := h.exists
    refine ⟨ ⟨ ?_ ⟩, ⟨ _, hx₀ ⟩⟩
    intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
    exact (Subtype.mk.injEq _ _ _ _).symm ▸ (h.unique hx hy)
  intro ⟨ hsing, ⟨ x₀, hx₀ ⟩ ⟩
  apply ExistsUnique.intro _ hx₀; intro y hy
  exact Subtype.mk.injEq _ _ _ _ ▸ (hsing.elim ⟨ _, hy ⟩ ⟨ _, hx₀ ⟩)

#print axioms ExistsUnique.iff_subsingleton_nonempty 
