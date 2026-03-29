import Mathlib.Tactic

/-!
# Analysis I, Section 11.1: Partitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Bounded intervals and partitions.
- Length of an interval; the lengths of a partition sum to the length of the interval.

-/

namespace Chapter11

inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

/-- There is a technical issue in that this coercion is not injective: the empty set is represented by multiple bounded intervals.  This causes some of the statements in this section to be a little uglier than necessary.-/
@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make {name}`Finset`s of {name}`BoundedInterval`s work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

-- Definition 11.1.1
#check Set.ordConnected_def

/-- Examples 11.1.3 -/
example : (Set.Icc 1 2 : Set ℝ).OrdConnected := by sorry

example : (Set.Ioo 1 2 : Set ℝ).OrdConnected := by sorry

example : ¬(Set.Icc 1 2 ∪ Set.Icc 3 4 : Set ℝ).OrdConnected := by sorry

example : (∅:Set ℝ).OrdConnected := by sorry

example (x:ℝ) : ({x}: Set ℝ).OrdConnected := by sorry

/-- Lemma 11.1.4 / Exercise 11.1.1 -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  sorry

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  sorry

/-- Corollary 11.1.6 / Exercise 11.1.2 -/
theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  sorry

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (BoundedInterval.inter I J).choose_spec.symm

example :
  (Ioo 2 4 ∩ Icc 4 6) = (Icc 4 4 : Set ℝ) := by
  sorry

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

instance BoundedInterval.instTrans : IsTrans BoundedInterval (· ⊆ ·) where
  trans I J K hIJ hJK := by grind [subset_iff]

@[simp]
theorem BoundedInterval.mem_inter (I J: BoundedInterval) (x:ℝ) :
  x ∈ (I ∩ J : BoundedInterval) ↔ x ∈ I ∧ x ∈ J := by simp [mem_iff]

abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

example : |Icc 3 5|ₗ = 2 := by
  sorry

example : |Ioo 3 5|ₗ = 2 := by
  sorry

example : |Icc 5 5|ₗ = 0 := by
  sorry

theorem BoundedInterval.length_nonneg (I: BoundedInterval) : 0 ≤ |I|ₗ := by
  simp

theorem BoundedInterval.empty_of_lt {I: BoundedInterval} (h: I.b < I.a) : (I:Set ℝ) = ∅ := by
  cases I with
  | Ioo _ _ => simp [le_of_lt h]
  | Icc _ _ => simp [h]
  | Ioc _ _ => simp [le_of_lt h]
  | Ico _ _ => simp [le_of_lt h]

theorem BoundedInterval.length_of_empty {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : |I|ₗ = 0 := by
  sorry

theorem BoundedInterval.length_of_subsingleton {I: BoundedInterval} : Subsingleton (I:Set ℝ) ↔ |I|ₗ = 0 := by
  sorry

theorem BoundedInterval.dist_le_length {I:BoundedInterval} {x y:ℝ} (hx: x ∈ I) (hy: y ∈ I) : |x - y| ≤ |I|ₗ := by
  apply subset_Icc I at hx; apply subset_Icc I at hy; simp_all [mem_iff, abs_le']; grind

abbrev BoundedInterval.joins (K I J: BoundedInterval) : Prop := (I:Set ℝ) ∩ (J:Set ℝ) = ∅
  ∧ (K:Set ℝ) = (I:Set ℝ) ∪ (J:Set ℝ) ∧ |K|ₗ = |I|ₗ + |J|ₗ

theorem BoundedInterval.join_Icc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Icc a b) (Ioc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Icc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins (Icc a b) (Ioo b c) := by
  simp_all [joins, le_of_lt hbc]; grind

theorem BoundedInterval.join_Ioc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins (Ioc a b) (Ioc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ioc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins (Ioc a b) (Ioo b c) := by
  simp_all [joins, le_of_lt hbc]; grind

theorem BoundedInterval.join_Ico_Icc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Ico a b) (Icc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ico_Ico {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins (Ico a b) (Ico b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ioo_Icc {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins (Ioo a b) (Icc b c) := by
  simp_all [joins, le_of_lt hab]; grind

theorem BoundedInterval.join_Ioo_Ico {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins (Ioo a b) (Ico b c) := by
  simp_all [joins, le_of_lt hab]; grind

@[ext]
structure Partition (I: BoundedInterval) where
  intervals : Finset BoundedInterval
  exists_unique (x:ℝ) (hx : x ∈ I) : ∃! J, J ∈ intervals ∧ x ∈ J
  contains (J : BoundedInterval) (hJ : J ∈ intervals) : J ⊆ I

#check Partition.mk

instance Partition.instMembership (I: BoundedInterval) : Membership BoundedInterval (Partition I) where
  mem P J := J ∈ P.intervals

instance Partition.instBot (I: BoundedInterval) : Bot (Partition I) where
  bot := {
    intervals := {I}
    exists_unique x hx := by apply ExistsUnique.intro I <;> grind
    contains := by grind [subset_iff]
    }

@[simp]
theorem Partition.intervals_of_bot (I:BoundedInterval) : (⊥:Partition I).intervals = {I} := by
  rfl

noncomputable abbrev Partition.join {I J K:BoundedInterval} (P: Partition I) (Q: Partition J) (h: K.joins I J) : Partition K
:=
{
  intervals := P.intervals ∪ Q.intervals
  exists_unique x hx := by
    have := congr(x ∈ $(h.1))
    simp [mem_iff, h.2] at hx; obtain hx | hx := hx
    . choose L _ _ using (P.exists_unique _ hx).exists
      apply ExistsUnique.intro L (by grind)
      intro K ⟨hK, hxK⟩; simp at hK; obtain _ | hKQ := hK
      map_tacs [apply (P.exists_unique _ hx).unique; apply (K.subset_iff _).mp (Q.contains _ hKQ) at hxK]
      all_goals grind
    choose L hLQ hxL using (Q.exists_unique _ hx).exists
    apply ExistsUnique.intro L (by grind)
    intro K ⟨hK, hxK⟩; simp at hK; obtain hKP | _ := hK
    map_tacs [apply (K.subset_iff _).mp (P.contains _ hKP) at hxK; apply (Q.exists_unique _ hx).unique]
    all_goals grind
  contains L hL := by
    simp at hL; obtain hLP | hLQ := hL
    . apply (P.contains _ hLP).trans; simp [h, subset_iff]
    apply (Q.contains _ hLQ).trans; simp [h, subset_iff]
}

@[simp]
theorem Partition.intervals_of_join {I J K:BoundedInterval} {h:K.joins I J} (P: Partition I) (Q: Partition J) : (P.join Q h).intervals = P.intervals ∪ Q.intervals := by
  simp

noncomputable abbrev Partition.add_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals ∪ {∅}
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by aesop)
    intro K ⟨ hK, _ ⟩; simp at hK; obtain rfl | hK := hK
    · simp_all [mem_iff]
    apply (P.exists_unique _ hx).unique <;> grind
  contains L hL := by
    simp at hL; obtain rfl | hL := hL
    · simp [subset_iff]
    exact P.contains _ hL
}

open Classical in
noncomputable abbrev Partition.remove_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals.filter (fun J ↦ (J:Set ℝ).Nonempty)
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by grind [mem_iff, Set.nonempty_of_mem])
    intro K ⟨ hK, _ ⟩; simp at hK
    apply (P.exists_unique _ hx).unique <;> grind
  contains _ _ := P.contains _ (by grind)
}

@[simp]
theorem Partition.intervals_of_add_empty (I: BoundedInterval) (P: Partition I) : (P.add_empty).intervals = P.intervals ∪ {∅} := by
  simp

example : ∃ P:Partition (Icc 1 8),
  P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8, ∅} := by
  set P1 : Partition (Icc 1 1) := ⊥
  set P2 : Partition (Ico 1 3) := P1.join (⊥:Partition (Ioo 1 3)) (join_Icc_Ioo (by norm_num) (by norm_num) )
  set P3 : Partition (Ico 1 5) := P2.join (⊥:Partition (Ico 3 5)) (join_Ico_Ico (by norm_num) (by norm_num) )
  set P4 : Partition (Icc 1 5) := P3.join (⊥:Partition (Icc 5 5)) (join_Ico_Icc (by norm_num) (by norm_num) )
  set P5 : Partition (Icc 1 8) := P4.join (⊥:Partition (Ioc 5 8)) (join_Icc_Ioc (by norm_num) (by norm_num) )
  use P5.add_empty; simp_all; aesop

example : ∃ P:Partition (Icc 1 8), P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8} := by
  sorry

example : ¬∃ P:Partition (Icc 1 5), P.intervals = {Icc 1 4, Icc 3 5} := by
  sorry

example : ¬∃ P:Partition (Ioo 1 5), P.intervals = {Ioo 1 3, Ioo 3 5} := by
  sorry

example : ¬∃ P:Partition (Ioo 1 5), P.intervals = {Ioo 0 3, Ico 3 5} := by
  sorry


/-- Exercise 11.1.3.  The exercise only claims c ≤ b, but the stronger claim c < b is true and useful. -/
theorem Partition.exist_right {I: BoundedInterval} (hI: I.a < I.b) (hI': I.b ∉ I)
  {P: Partition I}
  : ∃ c ∈ Set.Ico I.a I.b, Ioo c I.b ∈ P ∨ Ico c I.b ∈ P := by
  sorry

/-- Theorem 11.1.13 (Length is finitely additive). -/
theorem Partition.sum_of_length  (I: BoundedInterval) (P: Partition I) :
  ∑ J ∈ P.intervals, |J|ₗ = |I|ₗ := by
  -- This proof is written to follow the structure of the original text.
  generalize hcard: P.intervals.card = n
  revert I; induction' n with n hn <;> intro I P hcard
  . rw [Finset.card_eq_zero] at hcard
    have : (I:Set ℝ) = ∅ := by
      sorry
    grind [length_of_empty]
  -- the proof in the book treats the n=1 case separately, but this is unnecessary
  by_cases h : Subsingleton (I:Set ℝ)
  . have (J: BoundedInterval) (hJ: J ∈ P) : Subsingleton (J:Set ℝ) := by
      sorry
    simp_rw [length_of_subsingleton] at *
    convert Finset.sum_eq_zero this
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins L K := by
    by_cases hI' : I.b ∈ I
    . choose K hK hbK using (P.exists_unique I.b hI').exists
      observe hKI : K ⊆ I
      by_cases hsub : Subsingleton (K:Set ℝ)
      . simp_all [mem_iff]
        apply hsub.eq_singleton_of_mem at hbK
        have : K = Icc (I.b) (I.b) := by
          sorry
        subst this
        cases I with
        | Ioo _ _ => simp at hI'
        | Icc a b => use (Icc b b), hK, Ico a b; apply join_Ico_Icc <;> order
        | Ioc a b => use (Icc b b), hK, Ioo a b; apply join_Ioo_Icc <;> order
        | Ico _ _ => simp at hI'
      simp [length_of_subsingleton, -Set.subsingleton_coe] at hsub
      have hKI' := (K.Ioo_subset.trans hKI).trans I.subset_Icc
      simp only [subset_iff] at hKI'
      have hKb : K.b = I.b := by
        rw [le_antisymm_iff]; split_ands
        . apply csSup_le_csSup bddAbove_Icc (by simp [hsub]) at hKI'
          simp_all [csSup_Ioo hsub, csSup_Icc (le_of_lt h)]
        have := K.subset_Icc _ hbK; simp [mem_iff] at this; exact this.2
      have hKA : I.a ≤ K.a := by
        apply csInf_le_csInf bddBelow_Icc (by simp [hsub]) at hKI'
        simp_all [csInf_Icc (le_of_lt h), csInf_Ioo]
      cases I with
      | Ioo _ _ => simp [mem_iff] at hI'
      | Icc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp [mem_iff, subset_iff] at *; grind
        | Icc c₂ b₂ => use Ico a₁ c₂, hK; simp_all; apply join_Ico_Icc <;> order
        | Ioc c₂ b₂ => use Icc a₁ c₂, hK; simp_all; apply join_Icc_Ioc <;> order
        | Ico _ _ => simp [mem_iff] at *; grind
      | Ioc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp_all [mem_iff]
        | Icc c₂ b₂ =>
          use Ioo a₁ c₂, hK
          simp_all [subset_iff]
          have : c₂ ∈ Set.Icc c₂ b₁ := by grind
          apply hKI at this; grind [join_Ioo_Icc]
        | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc <;> order
        | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
      | Ico _ _ => simp [mem_iff] at hI'
    choose c hc hK using P.exist_right h hI'
    cases I with
    | Ioo a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo <;> tauto
      use Ico c b₁, hK, Ioo a₁ c
      apply P.contains at hK; simp [subset_iff] at hK
      have : c ∈ Set.Ico c b₁ := by grind
      grind [join_Ioo_Ico]
    | Icc _ _ => simp [mem_iff] at hI' h; order
    | Ioc _ _ => simp [mem_iff] at hI' h; order
    | Ico a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Icc a₁ c; grind [join_Icc_Ioo]
      use Ico c b₁, hK, Ico a₁ c; grind [join_Ico_Ico]
  obtain ⟨ K, L, hK, ⟨ h1, h2, h3 ⟩ ⟩ := this
  have : ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
    sorry
  choose P' hP' using this
  rw [h3, ←Finset.add_sum_erase _ _ hK, ←hP', add_comm]; congr
  apply hn; simp [hP', Finset.card_erase_of_mem hK, hcard]

/-- Definition 11.1.14 (Finer and coarser partitions) -/
instance Partition.instLE (I: BoundedInterval) : LE (Partition I) where
  le P P' := ∀ J ∈ P'.intervals, ∃ K ∈ P, J ⊆ K

instance Partition.instPreOrder (I: BoundedInterval) : Preorder (Partition I) where
  le_refl P := by
    sorry
  le_trans P P' P'' hP hP' := by
    sorry

instance Partition.instOrderBot (I: BoundedInterval) : OrderBot (Partition I) where
  bot_le := by
    sorry

/-- Example 11.1.15 -/
example : ∃ P P' : Partition (Icc 1 4),
  P.intervals = {Ico 1 2, Icc 2 2, Ioo 2 3,
                 Icc 3 4} ∧
  P'.intervals = {Icc 1 2, Ioc 2 4} ∧
  P' ≤ P := by
  sorry

/-- Definition 11.1.16 (Common refinement)-/
noncomputable instance Partition.instMax (I: BoundedInterval) : Max (Partition I) where
  max P P' := {
    intervals := Finset.image₂ (fun J K ↦ J ∩ K) P.intervals P'.intervals
    exists_unique x hx := by
      choose J _ _ using P.exists_unique _ hx
      choose K _ _ using P'.exists_unique _ hx
      simp at *
      apply ExistsUnique.intro (J ∩ K)
      . simp_all; grind
      simp; grind [mem_inter]
    contains L hL := by
      simp at hL; obtain ⟨ J, hJ, K, hK, rfl ⟩ := hL
      apply P.contains at hJ; apply P'.contains at hK
      simp [subset_iff] at *; grind [Set.inter_subset_left]
    }


/-- Example 11.1.17 -/
example : ∃ P P' : Partition (Icc 1 4), P.intervals = {Ico 1 3, Icc 3 4} ∧ P'.intervals = {Icc 1 2, Ioc 2 4} ∧
  (P' ⊔ P).intervals = {Icc 1 2, Ioo 2 3, Icc 3 4, ∅} := by
  sorry

/-- Lemma 11.1.8 / Exercise 11.1.4 -/
theorem BoundedInterval.le_max {I: BoundedInterval} (P P': Partition I) :
  P ≤ P ⊔ P' ∧ P' ≤ P ⊔ P' := by
  sorry

/-- Not from textbook: the reverse inclusion -/
theorem BoundedInterval.max_le_iff (I: BoundedInterval) {P P' P'': Partition I}
  {hP : P ≤ P''} {hP': P' ≤ P''} : P ⊔ P' ≤ P''  := by
  sorry

end Chapter11
