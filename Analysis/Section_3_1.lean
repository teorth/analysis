import Mathlib.Tactic

/-!
# Analysis I, Section 3.1

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- A type `Chapter3.SetTheory.Set` of sets
- A type `Chapter3.SetTheory.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The empty set `∅`, singletons `{y}`, and pairs `{y,z}` (and more general finite tuples), with their attendant axioms
- Pairwise union `X ∪ Y`, and their attendant axioms
- Coercion of a set `A` to its associated type `A.toSubtype`, which is a subtype of `Object`, and basic API.  (This is a technical construction needed to make the Zermelo-Frankel set theory compatible with the dependent type theory of Lean.)
- The specification `A.specify P` of a set `A` and a predicate `P: A.toSubtype → Prop` to the subset of elements of `A` obeying `P`, and the axiom of specification.  TODO: somehow implement set builder elaboration for this.
- The replacement `A.replace hP` of a set `A` via a predicate
`P: A.toSubtype → Object → Prop` obeying a uniqueness condition `∀ x y y', P x y ∧ P x y' → y = y'`, and the axiom of replacement.
- A bijective correspondence between the Mathlib natural numbers `ℕ` and a set `Chapter3.Nat : Chapter3.Set` (the axiom of infinity).

The other axioms of Zermelo-Frankel set theory are discussed in later sections.

Some technical notes:
- Mathlib of course has its own notion of a `Set`, which is not compatible with the notion `Chapter3.Set` defined here, though we will try to make the notations match as much as possible.  This causes some notational conflict: for instance, one may need to explicitly specify `(∅:Chapter3.Set)` instead of just `∅` to indicate that one is using the `Chapter3.Set` version of the empty set, rather than the Mathlib version of the empty set, and similarly for other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set` and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion `X.toObject` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is mostly needed when manipulating sets of sets.
- After this chapter is concluded, the notion of a `Chapter3.SetTheory.Set` will be deprecated in favor of the standard Mathlib notion of a `Set` (or more precisely of the type `Set X` of a set in a given type `X`).  However, due to various technical incompatibilities between set theory and type theory, we will not attempt to create any sort of equivalence between these two notions of sets.  (As such, this makes this entire chapter optional from the point of view of the rest of the book, though we retain it for pedagogical purposes.)
-/


namespace Chapter3

/-- Some of the axioms of Zermelo-Frankel theory with atoms  -/
class SetTheory where
  Set : Type
  Object : Type
  set_to_object : Set ↪ Object
  mem : Object → Set → Prop
  emptyset: Set
  emptyset_mem x : ¬ mem x emptyset
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y
  singleton : Object → Set
  singleton_axiom x y : mem x (singleton y) ↔ x = y
  union_pair : Set → Set → Set
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y)
  specify A (P: Subtype (fun x ↦ mem x A) → Prop) : Set
  specification_axiom A (P: Subtype (fun x ↦ mem x A) → Prop) : (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x
  replace A (P: Subtype (fun x ↦ mem x A) → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') : Set
  replacement_axiom A (P: Subtype (fun x ↦ mem x A) → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y
  nat : Set
  nat_equiv : ℕ ≃ Subtype (fun x ↦ mem x nat)

export SetTheory (Set Object)

-- This instance implicitly imposes (some of) the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory]


/-- Definition 3.1.1 (objects can be elements of sets) -/
instance objects_mem_sets : Membership Object Set where
  mem X x := SetTheory.mem x X

/-- Axiom 3.1 (Sets are objects)-/
instance sets_are_objects : Coe Set Object where
  coe X := SetTheory.set_to_object X

abbrev SetTheory.Set.toObject (X:Set) : Object := X

/-- Axiom 3.1 (Sets are objects)-/
theorem SetTheory.Set.coe_eq {X Y:Set} (h: X.toObject = Y.toObject) : X = Y := SetTheory.set_to_object.inj' h

/-- Axiom 3.1 (Sets are objects)-/
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y:Set) : X.toObject = Y.toObject ↔  X = Y := by
  constructor
  . exact coe_eq
  intro h; subst h; rfl

/-- Axiom 3.2 (Equality of sets)-/
abbrev SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := SetTheory.extensionality _ _ h

/-- Axiom 3.2 (Equality of sets)-/
theorem SetTheory.Set.ext_iff (X Y: Set) : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y := by
  constructor
  . intro h; subst h; simp
  . intro h; apply ext; exact h

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := SetTheory.emptyset

/-- Axiom 3.3 (empty set).  Note: one may have to explicitly cast ∅ to Set due to Mathlib's existing set theory notation. -/
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := SetTheory.emptyset_mem

/-- Empty set is unique -/
theorem SetTheory.Set.eq_empty_iff_forall_notMem {X:Set} : X = ∅ ↔ (∀ x, ¬ x ∈ X) := by
  sorry

/-- Empty set is unique -/
theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, ¬ x ∈ X := by
  sorry

/-- Lemma 3.1.5 (Single choice) -/
lemma SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by
    simp [this, not_mem_empty]
  replace claim := ext claim
  contradiction

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := SetTheory.singleton

/-- Axiom 3.3(a) (singleton).  Note one may have to explicitly cast {a} to Set due to Mathlib's existing set theory notation. -/
theorem SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := by
  exact SetTheory.singleton_axiom x a


instance SetTheory.Set.instUnion : Union Set where
  union := SetTheory.union_pair

/-- Axiom 3.4 (Pairwise union)-/
theorem SetTheory.Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) := SetTheory.union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

/-- Axiom 3.3(b) (pair).  Note that one often has to cast {a,b} to Set -/
theorem SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

/-- Axiom 3.3(b) (pair).  Note that one often has to cast {a,b} to Set -/
theorem SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  rw [pair_eq, mem_union, mem_singleton, mem_singleton]

/-- Remark 3.1.8 -/
theorem SetTheory.Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by sorry

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by sorry

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by sorry

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  sorry

/-- Exercise 3.1.1 -/
theorem SetTheory.Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) : a = c ∧ b = d ∨ a = d ∧ b = c := by
  sorry

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {empty.toObject}
abbrev SetTheory.Set.pair_empty : Set := {empty.toObject, singleton_empty.toObject}

/-- Exercise 3.1.2-/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  sorry

/-- Exercise 3.1.2-/
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by sorry

/-- Exercise 3.1.2-/
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  sorry

/-- Remark 3.1.11.  (These results can be proven either by a direct rewrite, or by using extensionality.) -/
theorem SetTheory.Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := by sorry

/-- Remark 3.1.11.  (These results can be proven either by a direct rewrite, or by using extensionality.) -/
theorem SetTheory.Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := by sorry

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.singleton_union_singleton (a b:Object) : ({a}:Set) ∪ ({b}:Set) = {a,b} := by
  sorry

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by sorry

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- this proof is written to follow the structure of the original text.
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . rw [mem_union] at case1
      rcases case1 with case1a | case1b
      . rw [mem_union]; tauto
      have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    have : x ∈ B ∪ C := by rw [mem_union]; tauto
    rw [mem_union]; tauto
  sorry

/-- Proposition 3.1.27(c) -/
theorem SetTheory.Set.union_self (A:Set) : A ∪ A = A := by
  sorry

/-- Proposition 3.1.27(a) -/
theorem SetTheory.Set.union_empty (A:Set) : A ∪ ∅ = A := by
  sorry

/-- Proposition 3.1.27(a) -/
theorem SetTheory.Set.empty_union (A:Set) : ∅ ∪ A = A := by
  sorry

theorem SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Example 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c:Object) : ({a,b}:Set) ∪ {b,c} = {a,b,c} := sorry

/-- Definition 3.1.14.   -/
instance SetTheory.Set.uinstSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

/-- Definition 3.1.14.  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`. -/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

/-- Definition 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/-- Definition 3.1.14.  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`. -/
theorem SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Remark 3.1.15 -/
theorem SetTheory.Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := by sorry

/-- Examples 3.1.16 -/
theorem SetTheory.Set.subset_self (A:Set) : A ⊆ A := by sorry

/-- Examples 3.1.16 -/
theorem SetTheory.Set.empty_subset (A:Set) : ∅ ⊆ A := by sorry

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_trans (A B C:Set) (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- this proof is written to follow the structure of the original text.
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  replace hx := hAB x hx
  replace hx := hBC x hx
  assumption

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  sorry

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.ssubset_trans (A B C:Set) (hAB:A ⊂ B) (hBC:B ⊂ C) : A ⊂ C := by
  sorry

/-- This defines the subtype `A.toSubtype` for any `A:Set`.  To produce an element `x'` of this subtype, use `⟨ x, hx ⟩`, where `x:Object` and `hx:x ∈ A`.  The object `x` associated to a subtype element `x'` is recovered as `x.val`, and the property `hx` that `x` belongs to `A` is recovered as `x.property`-/
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (fun x ↦ x ∈ A)

instance : CoeSort (Set) (Type) where
  coe A := A.toSubtype

/-- Elements of a set (implicitly coerced to a subtype) are also elements of the set (with respect to the membership operation of the set theory). -/
lemma SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x := rfl

lemma SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y := Subtype.coe_inj


/-- If one has a proof `hx` of `x ∈ A`, then `A.subtype_mk hx` will then make the element of `A` (viewed as a subtype) corresponding to `x`.  -/
def SetTheory.Set.subtype_mk (A:Set) {x:Object} (hx:x ∈ A) : A := ⟨ x, hx ⟩

lemma SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x := by rfl



abbrev SetTheory.Set.specify (A:Set) (P: A → Prop) : Set := SetTheory.specify A P

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom {A:Set} {P: A → Prop} {x:Object} (h: x ∈ A.specify P) : x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom' {A:Set} (P: A → Prop) (x:A.toSubtype) : x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

theorem SetTheory.Set.specify_subset {A:Set} (P: A → Prop) : A.specify P ⊆ A := by sorry

/-- This exercise may require some understanding of how  subtypes are implemented in Lean. -/
theorem SetTheory.Set.specify_congr {A A':Set} (hAA':A = A') {P: A → Prop} {P': A' → Prop} (hPP': (x:Object) → (h:x ∈ A) → (h':x ∈ A') → P ⟨ x, h⟩ ↔ P' ⟨ x, h'⟩ ) : A.specify P = A'.specify P' := by sorry

instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

/-- Definition 3.1.22 (Intersections) -/
theorem SetTheory.Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨ x,hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

/-- Definition 3.1.26 (Difference sets) -/
theorem SetTheory.Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩ ).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨ x, hX⟩ ).mpr hY

/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
theorem SetTheory.Set.inter_comm (A B:Set) : A ∩ B = B ∩ A := by sorry

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.subset_union {A X: Set} (hAX: A ⊆ X) : A ∪ X = X := by sorry

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.union_subset {A X: Set} (hAX: A ⊆ X) : X ∪ A = X := by sorry

/-- Proposition 3.1.27(c) -/
theorem SetTheory.Set.inter_self (A:Set) : A ∩ A = A := by
  sorry

/-- Proposition 3.1.27(e) -/
theorem SetTheory.Set.inter_assoc (A B C:Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by sorry

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.inter_union_distrib_left (A B C:Set) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := sorry

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.union_inter_distrib_left (A B C:Set) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := sorry

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.union_compl {A X:Set} (hAX: A ⊆ X) : A ∪ (X \ A) = X := by sorry

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.inter_compl {A X:Set} (hAX: A ⊆ X) : A ∩ (X \ A) = ∅ := by sorry

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_union {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by sorry

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_inter {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by sorry

/-- Not from textbook: sets form a distributive lattice. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by sorry
  le_sup_right := by sorry
  sup_le := by sorry
  inf_le_left := by sorry
  inf_le_right := by sorry
  le_inf := by sorry
  le_sup_inf := by
    intro X Y Z
    change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←union_inter_distrib_left]
    exact subset_self _

/-- Sets have a minimal element.  -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

/-- Definition of disjointness (using the previous instances) -/
theorem SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A:Set) {P: A → Object → Prop} (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Axiom 3.7 (Axiom of replacement) -/
theorem SetTheory.Set.replacement_axiom {A:Set} {P: A → Object → Prop} (hP: ∀ x y y', P x y ∧ P x y' → y = y') (y:Object) : y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

/-- Axiom 3.8 (Axiom of infinity) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Below are some API for handling coercions.  This may not be the optimal way to set things up.

instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  := Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m := Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n := Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n := Equiv.symm_apply_apply nat_equiv.symm n

example : (5:Nat) ≠ (3:Nat) := by
  simp

example : (5:Object) ≠ (3:Object) := by
  simp

/-- Example 3.1.16 (simplified).  -/
example : ({3, 5}:Set) ⊆ {1, 3, 5} := by
  sorry

/-- Example 3.1.17 (simplified). -/
example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3)
 = {(5:Object)} := by
  sorry

/-- Example 3.1.24 -/

example : ({1, 2, 4}:Set) ∩ {2,3,4} = {2, 4} := by sorry

/-- Example 3.1.24 -/

example : ({1, 2}:Set) ∩ {3,4} = ∅ := by sorry

example : ¬ Disjoint  ({1, 2, 3}:Set)  {2,3,4} := by sorry

example : Disjoint (∅:Set) ∅ := by sorry

/-- Definition 3.1.26 example -/

example : ({1, 2, 3, 4}:Set) \ {2,4,6} = {1, 3} := by sorry

/-- Example 3.1.30 -/

example : ({3,5,9}:Set).replace (P := fun x y ↦ ∃ (n:ℕ), x.val = n ∧ y = (n+1:ℕ)) (by sorry) = {4,6,10} := by sorry

/-- Example 3.1.31 -/

example : ({3,5,9}:Set).replace (P := fun x y ↦ y=1) (by sorry) = {1} := by sorry

/-- Exercise 3.1.5.  One can use the `tfae_have` and `tfae_finish` tactics here. -/
theorem SetTheory.Set.subset_tfae (A B C:Set) : [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by sorry

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_left (A B:Set) : A ∩ B ⊆ A := by
  sorry

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_right (A B:Set) : A ∩ B ⊆ B := by
  sorry

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_inter_iff (A B C:Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  sorry

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_left (A B:Set) : A ⊆ A ∪ B := by
  sorry

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_right (A B:Set) : B ⊆ A ∪ B := by
  sorry

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.union_subset_iff (A B C:Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  sorry

/-- Exercise 3.1.8 -/
theorem SetTheory.Set.inter_union_cancel (A B:Set) : A ∩ (A ∪ B) = A := by sorry

/-- Exercise 3.1.8 -/
theorem SetTheory.Set.union_inter_cancel (A B:Set) : A ∪ (A ∩ B) = A := by sorry

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_left {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) : A = X \ B := by sorry

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_right {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) : B = X \ A := by
  sorry

/-- Exercise 3.1.10 -/
theorem Set.pairwise_disjoint (A B:Set) : Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by sorry

/-- Exercise 3.1.10 -/
theorem Set.union_eq_partition (A B:Set) : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by sorry

/-- Exercise 3.1.11.  The challenge is to prove this without using `Set.specify`, `Set.specification_axiom`, or `Set.specification_axiom'`. -/
theorem SetTheory.Set.specification_from_replacement {A:Set} {P: A → Prop} : ∃ B, A ⊆ B ∧ ∀ x, x.val ∈ B ↔ P x := by sorry

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_union_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) : A ∪ A' ⊆ A ∪ B := by sorry

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_inter_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) : A ∩ A' ⊆ A ∩ B := by sorry

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_diff_subset_counter : ∃ (A B A' B':Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A \ A') ⊆ (B ∩ B') := by sorry

/- Final part of Exercise 3.1.12: state and prove a reasonable substitute positive result for the above theorem that involves set differences . -/

/-- Exercise 3.1.13 -/
theorem SetTheory.Set.singleton_iff (A:Set) (hA: A ≠ ∅) : ¬ ∃ B, B ⊂ A ↔ ∃ x, A = {x} := by sorry

end Chapter3
