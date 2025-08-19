import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as `Set.pi` and `Set.prod`.

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used `Object × Object` to
define `OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
  constructor
  · intro h
    rw [Set.ext_iff] at h
    have : ∀ x, x = c → x = b := by specialize h b; simp_all
    simp_all
  simp_all

/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro p1 p2 hp
    simp only [EmbeddingLike.apply_eq_iff_eq, SetTheory.Set.ext_iff, mem_pair] at hp
    rw [OrderedPair.eq]
    have hfeq : p1.fst = p2.fst := by
      obtain (_ | hp2) := (hp ({p1.fst}: Set)).mp (Or.inl rfl)
      · simp_all [SetTheory.Set.ext_iff]
      symm at hp2
      simp_all [pair_eq_singleton_iff]
    use hfeq
    obtain hp1 := (hp ({p1.fst, p1.snd}: Set)).mp (Or.inr rfl)
    simp_all only [EmbeddingLike.apply_eq_iff_eq]
    by_cases h : p1.snd = p2.fst
    · simp_all [pair_eq_singleton_iff]
    have : {p2.fst, p1.snd} ≠ ({p2.fst}: Set) := by intro h; simp_all [pair_eq_singleton_iff]
    simp only [this, false_or] at hp1
    have := pair_eq_pair hp1
    simp_all

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by intros; simp_all)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by intros; simp_all))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-- This equips an `OrderedPair` with proofs that `x ∈ X` and `y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at hy ⊢; rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at hx ⊢; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

/--
  Connections with the Mathlib set product, which consists of Lean pairs like `(x, y)`
  equipped with a proof that `x` is in the left set, and `y` is in the right set.
  Lean pairs like `(x, y)` are similar to our `OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun := fun z ↦ ⟨(fst z, snd z), by simp⟩
  invFun := fun z ↦ mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv := by intro; simp
  right_inv := by intro; simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between `X ×ˢ Y` and `Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := fun z ↦ mk_cartesian (snd z) (fst z)
  invFun := fun z ↦ mk_cartesian (snd z) (fst z)
  left_inv := by intro; simp
  right_inv := by intro; simp

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f ⟨ (⟨ x, y ⟩:OrderedPair), by simp ⟩
  left_inv _ := by simp
  right_inv _ := by simp [←pair_eq_fst_snd]

/-- Definition 3.5.6.  The indexing set `I` plays the role of `{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

/-- Definition 3.5.6 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
  constructor
  · intro h
    simp only [coe_of_fun_inj, funext_iff] at h
    ext x
    specialize h x
    simp only [Subtype.mk.injEq] at h
    exact h
  tauto

/-- Example 3.5.8. There is a bijection between `(X ×ˢ Y) ×ˢ Z` and `X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun := fun t ↦ ((mem_iProd _).mp t.property).choose ⟨i, by simp⟩
  invFun := fun x ↦ ⟨tuple fun _ ↦ x, by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    have h := (mem_iProd _).mp t.property
    have ht := h.choose_spec
    ext
    rw [ht, tuple_inj]
    ext ⟨i', hi'⟩
    rw [mem_singleton] at hi'
    simp_rw [hi']
  right_inv := by
    intro x
    dsimp only []
    generalize_proofs h
    have ht := h.choose_spec
    rw [tuple_inj] at ht
    rw [←ht]

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun := fun t ↦ ()
  invFun := fun x ↦ ⟨tuple fun e ↦ False.elim (not_mem_empty _ e.property), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    have h := (mem_iProd _).mp t.property
    obtain ⟨x, ht⟩ := h
    ext
    rw [ht, tuple_inj]
    ext e
    have := not_mem_empty e
    contradiction
  right_inv := by
    intro
    simp

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun i:I ↦ X) ≃ (I → X) where
  toFun := fun t ↦ ((mem_iProd _).mp t.property).choose
  invFun := fun x ↦ ⟨tuple x, by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    have h := (mem_iProd _).mp t.property
    have ht := h.choose_spec
    ext
    rw [ht]
  right_inv := by
    intro x
    dsimp only []
    generalize_proofs h
    have ht := h.choose_spec
    rw [tuple_inj] at ht
    rw [←ht]

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun := fun t ↦
    let x := ((mem_iProd _).mp t.property).choose
    mk_cartesian (x ⟨0, by simp⟩) (x ⟨1, by simp⟩)
  invFun := fun z ↦ ⟨tuple (X:=X) (fun i ↦ by
    have : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ := by aesop
    if h : i = ⟨0, by simp⟩ then rw [h]; exact (fst z)
    else if h : i = ⟨1, by simp⟩ then rw [h]; exact (snd z)
    else aesop
  ), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    have h := (mem_iProd _).mp t.property
    have ht := h.choose_spec
    ext
    rw [ht, tuple_inj]
    ext i
    have : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ := by aesop
    if h : i = ⟨0, by simp⟩ then subst h; simp_all
    else if h : i = ⟨1, by simp⟩ then subst h; simp_all
    else tauto
  right_inv := by
    intro z
    dsimp only []
    generalize_proofs _ _ _ _ _ h
    have ht := h.choose_spec
    rw [tuple_inj] at ht
    simp [←ht]

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun := fun t ↦
    let x := ((mem_iProd _).mp t.property).choose
    mk_cartesian (x ⟨0, by simp⟩) (mk_cartesian (x ⟨1, by simp⟩) (x ⟨2, by simp⟩))
  invFun := fun z ↦ ⟨tuple (X:=X) (fun i ↦ by
    have : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ ∨ i = ⟨2, by simp⟩  := by aesop
    if h : i = ⟨0, by simp⟩ then rw [h]; exact (fst z)
    else if h : i = ⟨1, by simp⟩ then rw [h]; exact (fst (snd z))
    else if h : i = ⟨2, by simp⟩ then rw [h]; exact (snd (snd z))
    else aesop
  ), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    have h := (mem_iProd _).mp t.property
    have ht := h.choose_spec
    ext
    rw [ht, tuple_inj]
    ext i
    dsimp only []
    if h : i = ⟨0, by simp⟩ then
      rw [dif_pos h, fst_of_mk_cartesian]
      subst h
      rfl
    else if h : i = ⟨1, by simp⟩ then
      have h0 : i ≠ ⟨0, by simp⟩ := by aesop
      rw [dif_neg h0, dif_pos h, snd_of_mk_cartesian, fst_of_mk_cartesian]
      subst h
      rfl
    else if h : i = ⟨2, by simp⟩ then
      have h0 : i ≠ ⟨0, by simp⟩ := by aesop
      have h1 : i ≠ ⟨1, by simp⟩ := by aesop
      rw [dif_neg h0, dif_neg h1, dif_pos h, snd_of_mk_cartesian, snd_of_mk_cartesian]
      subst h
      rfl
    else
      have : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ ∨ i = ⟨2, by simp⟩ := by aesop
      tauto
  right_inv := by
    intro z
    dsimp only []
    generalize_proofs _ _ _ _ _ _ _ h
    have ht := h.choose_spec
    rw [tuple_inj] at ht
    simp [←ht]

/-- Connections with Mathlib's `Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    have ht := h.choose_spec
    rw [tuple_inj] at ht
    rw [←ht]


/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib `Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩:nat); simp [h2]
    calc
      x = (⟨ x, h1 ⟩:nat) := rfl
      _ = _ := by congr; simp
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).property)
  convert hm; simp [h, Equiv.symm_apply_eq]; rfl

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at this ⊢
  choose m hm im using this; use m, by linarith
⟩

/-- Connections with Mathlib's `Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]; intros; by_contra! h; simp at h
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by rwa [this]⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by rw [this]; exact (x' i').property⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro p1 p2 hp
    simp only [EmbeddingLike.apply_eq_iff_eq, SetTheory.Set.ext_iff, mem_pair] at hp
    rw [OrderedPair.eq]
    have : p1.fst = p2.fst := by
      have h1 := hp p1.fst
      have h2 := hp p2.fst
      simp only [true_or, or_true, true_iff, iff_true] at h1 h2
      rcases h1 with (h1' | h1')
      · tauto
      rcases h2 with (h2' | h2')
      · tauto
      have : ∃ (X: Set), p1.fst = X := by simp [h1']
      obtain ⟨X, hX⟩ := this
      have : ∃ (Y: Set), p2.fst = Y := by simp [h2']
      obtain ⟨Y, hY⟩ := this
      simp only [hX, hY, EmbeddingLike.apply_eq_iff_eq,
        SetTheory.Set.ext_iff, SetTheory.Set.mem_pair] at h1' h2'
      have : (X: Object) ∈ Y := by simp_all
      have : (Y: Object) ∈ X := by simp_all
      have := not_mem_mem X Y
      tauto
    have h1 : (({p2.fst, p1.snd}: Set): Object) ≠ p2.fst := by
      intro h'
      have : ∃ (X: Set), {p2.fst, p1.snd} = X := by simp [h']
      obtain ⟨X, hX⟩ := this
      have : ∃ (Y: Set), p2.fst = Y := by rw [←h']; simp
      obtain ⟨Y, hY⟩ := this
      apply not_mem_self Y
      simp_all only [EmbeddingLike.apply_eq_iff_eq, or_self, iff_self_or, forall_eq]
      simp_rw [SetTheory.Set.ext_iff, SetTheory.Set.mem_pair] at hp
      specialize hp Y
      simp_all
    have h2 := hp ({p2.fst, p1.snd}: Set)
    simp_all only [EmbeddingLike.apply_eq_iff_eq, false_or, true_iff]
    rw [SetTheory.Set.ext_iff] at h2
    have := h2 p1.snd
    aesop

/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing `@[ext]` on the structure would generate a lemma requiring proof of `t.x = t'.x`,
  but these functions have different types when `t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; apply hx

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
  constructor
  · rintro rfl
    simp
  intro h
  ext o
  · constructor
    · intro ho
      let x : t.X := ⟨o, ho⟩
      have ⟨m, hm⟩ := t.surj x
      have : (t.x m) = o := by simp_all only [x]
      rw [← this, h m]
      use (t'.x m).property
    intro ho
    let x' : t'.X := ⟨o, ho⟩
    have ⟨m, hm⟩ := t'.surj x'
    have : (t'.x m) = o := by simp_all only [x']
    rw [← this, (h m).symm]
    use (t.x m).property
  apply h

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun := fun t ↦
    let hx := (mem_iProd _).mp t.property
    let x := hx.choose
    ⟨{
      X := iUnion _ fun i ↦ {((x i): Object)},
      x := fun i ↦ ⟨x i, by rw [mem_iUnion]; use i; simp⟩,
      surj := by
        rintro ⟨o, ho⟩
        rw [mem_iUnion] at ho
        obtain ⟨i, hi⟩ := ho
        rw [mem_singleton] at hi
        subst hi
        use i
    }, by intro i; use (x i).property⟩
  invFun := fun t ↦
    let x := fun i ↦ (⟨t.val.x i, t.property i⟩: X i)
    ⟨tuple x, by rw [mem_iProd]; use x⟩
  left_inv := by
    intro t
    let hx := (mem_iProd _).mp t.property
    simp [←hx.choose_spec]
  right_inv := by
    intro ⟨t, _⟩
    ext xi
    · simp only [mem_iUnion, mem_singleton]
      generalize_proofs hx
      have := hx.choose_spec
      rw [tuple_inj] at this
      simp only [←this]
      obtain ⟨x, hx⟩ := hx
      constructor
      · rintro ⟨i, rfl⟩
        use (t.x i).property
      intro hxi
      obtain ⟨i, hi⟩ := t.surj ⟨xi, hxi⟩
      use i
      rw [hi]
    dsimp only []
    generalize_proofs hx
    have := hx.choose_spec
    rw [tuple_inj] at this
    rw [←this]

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use `OrderedPair.eq` or `SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  cases p
  rw [OrderedPair.eq]
  cc

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  cases p
  cases q
  simp_rw [OrderedPair.eq]
  cc

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by
  rw [OrderedPair.eq] at *
  cc

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := by
  rw [tuple_inj]

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by
  simp_rw [tuple_inj]
  cc

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
  simp_rw [tuple_inj] at *
  cc

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by
  aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by
  aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by
  aesop

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  aesop

/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use {0}, ∅, ∅, {0}
  intro h
  rw [Set.ext_iff] at h
  specialize h (OrderedPair.mk 0 0)
  simp_all

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use {0}, {0}, ∅, {0}
  intro h
  rw [Set.ext_iff] at h
  simp_all

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
  simp_rw [subset_def] at *
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra h'
      let b := nonempty_choose hB
      let p := mk_cartesian ⟨a, ha⟩ b
      specialize h _ p.property
      simp_rw [p, mk_cartesian] at h
      aesop
    intro b hb
    by_contra h'
    let a := nonempty_choose hA
    let p := mk_cartesian a ⟨b, hb⟩
    specialize h _ p.property
    simp_rw [p, mk_cartesian] at h
    simp_all
  simp_all

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use {0}, ∅, ∅, ∅
  simp [subset_def]

/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
  apply existsUnique_of_exists_of_unique
  · use fun z ↦ mk_cartesian (f z) (g z)
    aesop
  intro h1 h2 ⟨hf, hs⟩ ⟨rfl, rfl⟩
  ext
  rw [Function.comp_def, funext_iff] at hf hs
  rw [pair_eq_fst_snd, pair_eq_fst_snd]
  simp_all

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  constructor
  · intro h
    by_contra! h'
    have x : ∀ i, X i := fun i ↦ nonempty_choose (h' i)
    have : tuple x ∈ iProd X := by rw [mem_iProd]; use x
    have : tuple x ∉ iProd X := by exact h (tuple x)
    contradiction
  intro ⟨i, hi⟩ t ht
  rw [mem_iProd] at ht
  obtain ⟨x, _⟩ := ht
  have := (x i).property
  simp_rw [hi] at this
  have := not_mem_empty (x i)
  contradiction

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by
  ext x
  simp only [mem_inter, mem_iUnion]
  constructor
  · rintro ⟨⟨i, ha⟩, j, hb⟩
    use mk_cartesian i j
    simp [ha, hb]
  intro ⟨p, ⟨ha, hb⟩⟩
  constructor
  · use fst p
  use snd p

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by
  constructor
  · intro h
    ext x
    simp_rw [Set.ext_iff, specification_axiom''] at h
    set p := mk_cartesian x (f x)
    have := (h p).mp (by simp [p.property])
    simp_all
  tauto

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by
  apply existsUnique_of_exists_of_unique
  · use fun x ↦ (hvert x).choose
    ext po
    constructor
    · intro hpo
      rw [subset_def] at hG
      let p : X ×ˢ Y := ⟨po, hG po hpo⟩
      have hpG : (p: Object) ∈ G := by simp [p, hpo]
      let y := snd p
      obtain ⟨y', hp, huniq⟩ := hvert (fst p)
      obtain rfl := huniq y (by simp [p]; rwa [←pair_eq_fst_snd])
      rw [specification_axiom'']
      use p.property
      simp only [Subtype.forall]
      generalize_proofs _ h
      obtain ⟨_, hy⟩ := h.choose_spec
      specialize hy y y.property hp
      rw [←hy]
    intro h
    rw [specification_axiom''] at h
    obtain ⟨hpo, hy⟩ := h
    simp only [Subtype.forall] at hy
    generalize_proofs h at hy
    obtain ⟨hy'⟩ := h.choose_spec
    let p : X ×ˢ Y := ⟨po, hpo⟩
    change (p: Object) ∈ G
    rw [pair_eq_fst_snd, ←hy]
    exact hy'
  simp_all [graph_inj]

/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
  have ⟨PT, hPT⟩ := exists_powerset (Y ×ˢ X)
  let SG := PT.specify (fun T ↦
    let h := (hPT T).mp T.property
    let G := h.choose
    ∀ y:Y, ∃! x:X, ((⟨y, x⟩:OrderedPair):Object) ∈ G
  )
  let SF := SG.replace (P := fun oG of ↦
     ∃! f: Y → X, of = f ∧ oG = ((graph f): Object)
  ) (by
    rintro G _ _ ⟨⟨f1, ⟨⟨_, h1⟩⟩⟩, ⟨f2, ⟨⟨_, h2⟩⟩⟩⟩
    simp_all [graph_inj]
  )
  apply existsUnique_of_exists_of_unique
  · use SF
    intro fo
    simp only [SF, replacement_axiom, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨G, hG, f, ⟨⟨rfl, rfl⟩⟩⟩
      use f
    rintro ⟨f, rfl⟩
    use graph f
    constructor
    · simp only [SG, specification_axiom'']
      constructor
      · intro y
        use f y
        generalize_proofs h
        obtain ⟨hG⟩ := h.choose_spec
        rw [EmbeddingLike.apply_eq_iff_eq] at hG
        rw [←hG]
        simp
      rw [hPT]
      simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq_left', subset_def]
      intro T hT
      rw [specification_axiom''] at hT
      exact hT.1
    use f
    simp
  aesop

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
  apply existsUnique_of_exists_of_unique
  · let a : ℕ → X := Nat.rec c fun n x ↦ f n x
    use fun n ↦ a n
    simp_all [a]
  intro f1 f2 ⟨h1z, h1s⟩ ⟨h2z, h2s⟩
  ext x
  rw [show x = (x:ℕ) by simp]
  induction' (x:ℕ) with n hn
  · rw [show ((0:ℕ):nat) = 0 by rfl]
    cc
  rw [←Subtype.eq_iff] at hn
  rw [h1s, h2s, hn]

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, ⟨⟨hz, hs⟩, hu⟩⟩ := recursion nat' (fun _ n' ↦ succ n') zero
  apply existsUnique_of_exists_of_unique
  · use f
    constructor
    · constructor
      · intro x1 x2 heq
        induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
        · apply nat_coe_eq_zero at hx1
          subst hx1
          rcases hx2: (x2: ℕ) with _ | j
          · apply nat_coe_eq at hx2
            exact hx2.symm
          apply nat_coe_eq at hx2
          rw [hx2, hz, hs j] at heq
          tauto
        apply nat_coe_eq at hx1
        subst hx1
        rcases hx2: (x2: ℕ) with _ | j
        · apply nat_coe_eq_zero at hx2
          rw [hx2, hz, hs i] at heq
          tauto
        apply nat_coe_eq at hx2
        subst hx2
        rw [hs, hs j] at heq
        specialize ih ((succ_of_ne _ _).mtr heq) (by simp)
        rwa [nat_equiv_inj, ←Nat.add_right_cancel_iff, ←nat_equiv_inj] at ih
      apply ind
      · use 0
      rintro y ⟨x, rfl⟩
      use ((x:ℕ) + 1:ℕ)
      rw [hs, nat_equiv_coe_of_coe']
    constructor
    · exact hz
    intro x x'
    constructor
    · intro h
      rw [hs, nat_equiv_coe_of_coe', h]
    intro h
    rw [hs] at h
    contrapose! h
    apply succ_of_ne
    rwa [nat_equiv_coe_of_coe']
  have hind : ∀ g : nat → nat',
      g 0 = zero →
      (∀ n n', g n = n' ↔ g (n+1:ℕ) = succ n') →
      ∀ n, g ((n + 1): ℕ) = succ (g n) := by
    intro g hz hs n
    induction' n with i hi
    · rw [show (0:nat) = (0:ℕ) by rfl] at hz
      rwa [hz, ←nat_equiv_coe_of_coe 0, ←hs]
    rw [←nat_equiv_coe_of_coe (i+1), ←hs]
    simp
  intro f1 f2 ⟨_, ⟨hz1, hs1⟩⟩ ⟨_, ⟨hz2, hs2⟩⟩
  rw [hu f1 ⟨hz1, hind f1 hz1 hs1⟩]
  rw [hu f2 ⟨hz2, hind f2 hz2 hs2⟩]

end Chapter3
