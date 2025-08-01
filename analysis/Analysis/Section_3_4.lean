import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.
-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  rw [SetTheory.Set.replacement_axiom]; peel 1; tauto

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
    image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
  ext y
  constructor
  · intro h
    rw [mem_image] at h
    obtain ⟨x, hx, hxy⟩ := h
    rw [specification_axiom'', ←hxy]
    use (f x).property, x
  intro h
  rw [mem_image]
  rw [specification_axiom''] at h
  obtain ⟨hy, ⟨x, hx, hxy⟩⟩ := h
  use x, hx
  rw [hxy]

/--
  Connection with Mathlib's notion of image.  Note the need to utilize the `Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext; simp only [_root_.Set.mem_setOf, _root_.Set.mem_image, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; use f x, ⟨x, hx, rfl⟩
  rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; use x, hx

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by
  intro _ h; rw [mem_image] at h; obtain ⟨ x', hx', rfl ⟩ := h
  exact (f x').property

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨x, (h | h | h), rfl⟩
    map_tacs [left; (right;left); (right;right)]
    all_goals simp_all
  rintro (h | h | h)
  map_tacs [use 1; use 2; use 3]
  all_goals simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
    x.val ∈ S → (f x).val ∈ image f S := by
  intro h
  rw [mem_image]
  use x

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
  use Nat, Nat, fun x ↦ 0, {((0:Nat):Object)}, 1
  push_neg
  simp only [mem_image, mem_singleton, and_true]
  constructor
  · use 0
  simp [Subtype.coe_ne_coe]

/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that U be a subset of Y.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  A version of mem_preimage that does not require x to be of type X.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h; by_cases hx: x ∈ X
    . use ⟨ x, hx ⟩; have := mem_preimage f U ⟨ x, hx ⟩; simp_all
    . simp_all [X.specification_axiom h]
  . rintro ⟨ x', rfl, hfx' ⟩; rwa [mem_preimage]

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext x
  simp only [_root_.Set.mem_setOf, _root_.Set.mem_image]
  simp only [Set.mem_preimage', _root_.Set.mem_preimage]
  constructor
  · rintro ⟨x', rfl, hy⟩; use x', hy
  rintro ⟨x', hy, rfl⟩; simp only [_root_.Set.mem_setOf] at hy; use x'

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by intro x h; simp at h; tauto

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext x
  simp only [mem_preimage', mem_triple, f_3_4_2]
  constructor
  · rintro ⟨x, rfl, (h | h | h)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl)
  map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
  intro h
  have : 1 ∉ image f_3_4_2 (preimage f_3_4_2 {1, 2, 3}) := by simp
  simp_all

/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext x
  refine ⟨ ?_, by aesop ⟩
  rintro (h | h | h)
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  intro h
  rw [Set.ext_iff] at h
  specialize h (-2)
  have : -2 ∉ ({-1, 0, 1, 2}: _root_.Set ℤ) := by simp
  apply h.not.mpr this
  simp

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := SetTheory.pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a `CoeOut` rather than a
`Coe` because the input type `X → Y` contains
parameters not present in the output type `Output` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  unfold f_3_4_9_a f_3_4_9_b f_3_4_9_c f_3_4_9_d
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; aesop

/-- Exercise 3.4.6 (i). One needs to provide a suitable definition of the power set here. -/
def SetTheory.Set.powerset (X:Set) : Set :=
  (({0,1} ^ X): Set).replace (P := fun F Y ↦
    ∃ f : X → ({0,1}: Set), F = (f : Object) ∧ Y = (preimage f {1})
  ) (by aesop)

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  rw [powerset, replacement_axiom]
  constructor
  · rintro ⟨_, ⟨f, _, hfx⟩⟩
    use preimage f {1}, hfx
    simp only [subset_def, mem_preimage']
    rintro _ ⟨a, ⟨rfl, _⟩⟩
    use a.property
  intro h
  obtain ⟨Y, rfl, _⟩ := h
  let f : X → ({0,1}: Set) := fun x ↦
    if x.val ∈ Y then ⟨1, by simp⟩
    else ⟨0, by simp⟩
  have hf := (powerset_axiom _).mpr (by use f)
  use ⟨_, hf⟩, f
  constructor
  · rfl
  congr
  apply Set.ext
  simp only [mem_preimage']
  aesop

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases ha : a ∈ Y <;> by_cases hb : b ∈ Y <;> by_cases hc : c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  apply Set.ext
  simp only [union_axiom, Insert.insert]
  aesop

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext x; simp only [union_axiom, Set.mem_sUnion]; aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by intro x y y' ⟨ h1, h2⟩; simp at h1 h2; rw [h1,h2]))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]; constructor
  . intro ⟨ _, _, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ α, hα ⟩ := hS
    simp_all; use α.val, α.property
  intro ⟨ α, hx ⟩; refine ⟨ A α, hx, by rw [replacement_axiom]; use α ⟩

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply Set.ext; intro x
  simp only [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩
  simp only [mem_union, Subtype.exists]
  rintro (h | h | h)
  map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union
-/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp only [mem_iUnion, _root_.Set.mem_setOf_eq, _root_.Set.mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  ext
  simp only [not_mem_empty, iff_false, mem_iUnion]
  push_neg
  intro α
  have := α.property
  aesop

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
  constructor
  · intro h
    rw [specification_axiom''] at h
    exact h.2
  intro h
  rw [specification_axiom'']
  use h (nonempty_choose hI)

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV: V ⊆ Y) :
    image f_inv V = preimage f V := by
  ext
  simp only [mem_image, mem_preimage']
  constructor
  · rintro ⟨y, hy, rfl⟩
    use (f_inv y), rfl
    rwa [hf.2]
  rintro ⟨x, rfl, hx⟩
  use (f x), hx
  rw [hf.1]

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) :
    S ⊆ preimage f (image f S) := by
  simp only [subset_def, mem_preimage', mem_image] at *
  intro x xs
  let x': X := ⟨x, hS x xs⟩
  use x', rfl, x'

/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) :
    image f (preimage f U) ⊆ U := by
  simp only [subset_def, mem_image]
  rintro y ⟨x, hx, rfl⟩
  rwa [mem_preimage] at hx

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f (preimage f U))` and `preimage f U`.
Interestingly, it is not needed for U to be a subset of Y.-/
theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) :
    preimage f (image f (preimage f U)) = preimage f U := by
  aesop

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
  simp only [subset_def]
  aesop

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
  simp only [subset_def, mem_image, mem_inter, mem_sdiff]
  rintro y ⟨⟨x, ⟨h1, h2⟩⟩, h'⟩
  have : (x: Object) ∉ B := by contrapose! h'; use x
  use x, ⟨h1, this⟩

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
  aesop

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  let f : nat → nat := fun x ↦ 0
  use nat, nat, f, {1}, {2}
  intro h
  rw [show ({1} ∩ {2}: Set) = ∅ by apply ext; simp] at h
  rw [show (image f ∅) = ∅ by apply ext; simp [mem_image]] at h
  symm at h
  rw [eq_empty_iff_forall_notMem] at h
  contrapose! h
  simp only [mem_inter, mem_image, f]
  use 0
  constructor
  · use 1
    norm_num
  use 2
  norm_num

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  let f : nat → nat := fun x ↦ 0
  use nat, nat, f, {1, 2}, {2}
  rw [show ({1, 2}: Set) \ {2} = {1} by apply ext; aesop]
  intro h
  rw [Set.ext_iff] at h
  specialize h 0
  have : 0 ∈ image f {1} := by rw [mem_image]; use 1; simp [f]
  have : 0 ∈ image f {2} := by rw [mem_image]; use 2; simp [f]
  simp_all [f]

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
  aesop

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
  aesop

theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by
  aesop

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
  constructor
  · intro h y
    simp only [subset_def, Set.ext_iff, mem_singleton, mem_image] at h
    specialize h _ (by aesop) y
    obtain ⟨x, ⟨_, hx⟩⟩ := h.mpr (by aesop)
    use x, by rwa [coe_inj] at hx
  intro h S hS
  apply ext
  intro y
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    exact hx
  intro hy
  obtain ⟨x, hx⟩ := h ⟨y, hS y hy⟩
  use x, by rwa [hx], by rw [hx]

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
  constructor
  · intro h x1 x2 hf
    simp only [subset_def] at h
    have hx: ((f x2): Object) ∈ image f {(x2: Object)} := by rw [mem_image]; aesop
    rwa [←hf, ←mem_preimage, h _ (by aesop), mem_singleton, coe_inj] at hx
  intro h S hS
  ext x
  constructor
  · simp only [mem_preimage', mem_image]
    rintro ⟨x1, rfl, x2, hx2, heq⟩
    rw [coe_inj] at heq
    rwa [←h heq]
  intro hx
  simp only [mem_preimage', mem_image]
  use ⟨x, hS x hx⟩, rfl, ⟨x, hS x hx⟩

/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  simp only [union_axiom, replacement_axiom]; tauto

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
  use union (Y.powerset.replace (P := fun oY' outer ↦
    outer = union (X.powerset.replace (P := fun oX' inner ↦
      ∃ (X' Y' : Set),
        oX'.val = X' ∧
        oY'.val = Y' ∧
        inner = (Y' ^ X': Set)
    ) (by simp_all))
  ) (by simp_all))
  intro F
  constructor
  · intro hF
    simp only [mem_union_powerset_replace_iff, EmbeddingLike.apply_eq_iff_eq] at hF
    obtain ⟨⟨oY', hY'⟩, _, rfl, hF⟩ := hF
    simp only [mem_union_powerset_replace_iff, EmbeddingLike.apply_eq_iff_eq] at hF
    obtain ⟨⟨oX', hX'⟩, Y'X', hF, hF'⟩ := hF
    simp only [EmbeddingLike.apply_eq_iff_eq] at hF
    obtain ⟨X', Y', rfl, rfl, rfl⟩ := hF
    simp_all only [mem_powerset', powerset_axiom]
    obtain ⟨f, hF⟩ := hF'
    use X', Y'
    use hX', hY'
    use f, hF.symm
  rintro ⟨X', Y', hX', hY', f, rfl⟩
  simp_all [mem_union_powerset_replace_iff, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_left, Subtype.exists]
  use Y', by simp_all
  use X', by simp_all
  use Y' ^ X', by simp_all
  rw [powerset_axiom]
  use f

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation `∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  use union {(X: Object), (Y: Object)}
  simp [union_axiom]
  aesop

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by
  ext
  simp_all

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by
  ext
  simp only [mem_iUnion, mem_union]
  aesop

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by
  intro h
  simp_all [Set.ext_iff]

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
  ext x
  simp only [mem_iInter, mem_inter]
  aesop

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
  apply ext; intro x
  simp only [mem_sdiff, mem_iUnion]
  aesop

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
  ext
  simp only [mem_sdiff, mem_iInter, mem_iUnion]
  aesop

end Chapter3
