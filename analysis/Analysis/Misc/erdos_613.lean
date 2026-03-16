import Mathlib

open Classical
open scoped BigOperators


-- 1. Define the main claim

/-- “Color-`col` monochromatic star of size `k`”: there is a center `x` and a set `S`
    of `k` distinct neighbors of `x` such that every edge `{x,y}` with `y ∈ S`
    is present in `G` and colored `col`.  (No restriction on edges inside `S`.) -/
def hasMonoStar {V:Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) (k : ℕ) : Prop :=
  ∃ (x : V) (S : Finset V),
    S.card = k ∧
    x ∉ S ∧
    ∀ ⦃y : V⦄, y ∈ S → G.Adj x y ∧ color (Sym2.mk (x, y)) = col

/-- “Color-`col` monochromatic triangle”: there exist `a b c` with all three edges
    present in `G` and colored `col`.  (Adjacency already forces distinctness.) -/
def hasMonoTriangle {V:Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) : Prop :=
  ∃ a b c : V,
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
    color (Sym2.mk (a, b)) = col ∧
    color (Sym2.mk (b, c)) = col ∧
    color (Sym2.mk (a, c)) = col

/-- **Statement (n = 5 case of Pikhurko’s counterexample).**
There exists a simple graph on `16` vertices with exactly `44` edges such that
for *every* 2‑coloring of unordered pairs, either color `0` contains a `K_{1,5}`
(a 5‑edge star) or color `1` contains a `K₃` (a triangle).

This only *states* the claim (as a `Prop`).  You can later prove it from the
explicit construction, or assume it as an axiom while you develop the rest. -/
def Pikhurko_n5_statement : Prop :=
  ∃ (V:Type) (G : SimpleGraph V),
    G.edgeSet.ncard = 44 ∧
    ∀ (color : Sym2 V → Fin 2),
      hasMonoStar G color 0 5 ∨ hasMonoTriangle G color 1


-- 2. Construct the graph

namespace PikhurkoN5

/-- Vertex type with 2 + 5 + 3 + 5 + 1 = 16 vertices. -/
inductive V
| A1 (i : Fin 2)  -- the K₂ part of P_{2,5}
| B1 (j : Fin 5)  -- the independent part of P_{2,5}
| A2 (i : Fin 3)  -- the K₃ part of P_{3,5}
| B2 (j : Fin 5)  -- the independent part of P_{3,5}
| apex            -- the universal vertex
deriving DecidableEq, Repr

open V

/-- Adjacency relation for the Pikhurko n=5 counterexample.

* Inside `A1` and inside `A2`: cliques.
* Between `A1`–`B1` and `A2`–`B2`: complete bipartite.
* Inside `B1` and `B2`: no edges.
* No edges between the two blocks `{A1,B1}` and `{A2,B2}`.
* `apex` is connected to every non-`apex` vertex. -/
def GAdj : V → V → Prop
| apex, apex => False
| apex, _    => True
| _,    apex => True
| A1 i, A1 j => i ≠ j
| A2 i, A2 j => i ≠ j
| A1 _, B1 _ => True
| B1 _, A1 _ => True
| A2 _, B2 _ => True
| B2 _, A2 _ => True
| _,    _    => False

/-- The graph `G` on 16 vertices used for the n=5 counterexample. -/
def G : SimpleGraph V where
  Adj := GAdj
  symm := by
    intro u v h
    cases u <;> cases v <;> grind [GAdj]
  loopless := ⟨by intro v; cases v <;> simp [GAdj]⟩

/-!
Convenience simp lemmas. These are optional but help when you start proving
properties about colorings later on.
-/
@[simp] lemma adj_apex_left {v : V} : G.Adj V.apex v ↔ v ≠ V.apex := by
  cases v <;> simp [G, GAdj]

@[simp] lemma adj_apex_right {v : V} : G.Adj v V.apex ↔ v ≠ V.apex := by
  cases v <;> simp [G, GAdj]

@[simp] lemma adj_A1A1 {i j} : G.Adj (A1 i) (A1 j) ↔ i ≠ j := by
  simp [G, GAdj]

@[simp] lemma adj_A2A2 {i j} : G.Adj (A2 i) (A2 j) ↔ i ≠ j := by
  simp [G, GAdj]

@[simp] lemma adj_A1B1 {i j} : G.Adj (A1 i) (B1 j) := by
  simp [G, GAdj]

@[simp] lemma adj_B1A1 {i j} : G.Adj (B1 i) (A1 j) := by
  simp [G, GAdj]

@[simp] lemma adj_A2B2 {i j} : G.Adj (A2 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma adj_B2A2 {i j} : G.Adj (B2 j) (A2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_adj_B1B1 {j j'} : ¬ G.Adj (B1 j) (B1 j') := by
  simp [G, GAdj]

@[simp] lemma no_adj_B2B2 {j j'} : ¬ G.Adj (B2 j) (B2 j') := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A1B2 {i j} : ¬ G.Adj (A1 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2B1 {i j} : ¬ G.Adj (A2 i) (B1 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_B1A2 {i j} : ¬ G.Adj (B1 j) (A2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_B1B2 {i j} : ¬ G.Adj (B1 j) (B2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2A1 {i j} : ¬ G.Adj (A2 j) (A1 i)  := by
  simp [G, GAdj]

end PikhurkoN5


-- 3.  Count edges

namespace PikhurkoN5

open V

/- We’ll need `Fintype` on `V` for `univ`, sums, etc. -/
deriving instance Fintype for V

/-- An explicit equivalence showing `V` has 2+5+3+5+1 = 16 elements. -/
def VEquiv :
    V ≃ ((((Fin 2 ⊕ Fin 5) ⊕ Fin 3) ⊕ Fin 5) ⊕ Unit) where
  toFun
  | A1 i  => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))
  | B1 j  => Sum.inl (Sum.inl (Sum.inl (Sum.inr j)))
  | A2 i  => Sum.inl (Sum.inl (Sum.inr i))
  | B2 j  => Sum.inl (Sum.inr j)
  | apex  => Sum.inr ()
  invFun
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl i))) => A1 i
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr j))) => B1 j
  | Sum.inl (Sum.inl (Sum.inr i))            => A2 i
  | Sum.inl (Sum.inr j)                      => B2 j
  | Sum.inr ()                               => apex
  left_inv v := by cases v <;> grind
  right_inv w := by cases w <;> grind

/-- `|V| = 16`. Useful for quick cardinality arithmetic. -/
lemma card_V : Fintype.card V = 16 := by
  -- Reduce to the nested-sum cardinality and compute arithmetically.
  simpa using
    (Fintype.card_congr VEquiv).trans <|
      by
        -- `simp` turns cardinals of sums into sums of cardinals; `norm_num` does the rest.
        simp [Fintype.card_sum, Fintype.card_fin]

/-! ## Degree computations

We compute the degree of each vertex *kind*. We’ll use your `[simp]` adjacency
lemmas from Approach A:
- `adj_apex_left`, `adj_A1A1`, `adj_A2A2`, `adj_A1B1`, `adj_A2B2`,
  and the corresponding “no edge” lemmas across blocks.
-/

/-- `deg(apex) = 15`. -/
lemma degree_apex : G.degree apex = 15 := by
  classical
  -- Neighbors of `apex` are exactly all vertices ≠ `apex`.
  have hN :
      G.neighborFinset apex = (Finset.univ.erase apex) := by
    ext v; constructor
    · intro hv
      have : G.Adj apex v := by simpa using hv
      have hvne : v ≠ apex := by simpa [adj_apex_left] using this
      simpa [Finset.mem_erase] using And.intro hvne (by simp : v ∈ (Finset.univ : Finset V))
    · intro hv
      have hvne : v ≠ apex := (Finset.mem_erase.mp hv).1
      have : G.Adj apex v := by simpa [adj_apex_left] using hvne
      simpa using this
  -- Count `univ.erase apex`.
  have : (G.neighborFinset apex).card = 15 := by
    -- `card (erase univ apex) = |V| - 1 = 16 - 1 = 15`
    have : (Finset.univ.erase apex).card = Fintype.card V - 1 := by
      have : apex ∈ (Finset.univ : Finset V) := by simp
      simp [Finset.card_erase_of_mem, this]
    simp [hN, card_V]
  -- `degree` is the cardinal of the neighbor finset.
  simp at this
  assumption

/-- `deg(A1 i) = 7` for each `i`. -/
lemma degree_A1 (i : Fin 2) : G.degree (A1 i) = 7 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 1 + 5 + 0 + 0 + 1 := by
      congr
      . calc
        _ = Finset.card {j | j ≠ i} := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
          grind
        _ = 1 := by
          fin_cases i <;> simp
          . convert Finset.card_singleton 1
          convert Finset.card_singleton 0
      . calc
        _ = Finset.card (Finset.univ : Finset (Fin 5)) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 5 := by simp [Fintype.card_fin]
      . calc
        _ = Finset.card (∅ : Finset (Fin 3)) := by
          congr; ext; simp [-iff_false]
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
          aesop
        _ = 0 := by simp
      . calc
        _ = Finset.card (∅: Finset (Fin 5)) := by
          congr; ext; simp [-iff_false]
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 0 := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num

/-- `deg(B1 j) = 3` for each `j`. (Two `A1`s + apex.) -/
lemma degree_B1 (j : Fin 5) : G.degree (B1 j) = 3 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 2 + 0 + 0 + 0 + 1 := by
      congr
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 2)) := by
            congr; ext; simp
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 3)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num



/-- `deg(A2 i) = 8` for each `i`. (Two inside `A2` + five in `B2` + apex.) -/
lemma degree_A2 (i : Fin 3) : G.degree (A2 i) = 8 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 0 + 0 + 2 + 5 + 1 := by
      congr
      . calc
          _ = Finset.card (∅ : Finset (Fin 2)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card {j | j ≠ i} := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
            grind
          _ = _ := by
            convert Finset.card_erase_of_mem (show i ∈ Finset.univ by simp)
            grind
      . calc
          _ = Finset.card (Finset.univ: Finset (Fin 5)) := by
            congr; ext; simp
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num


/-- `deg(B2 j) = 4` for each `j`. (Three `A2`s + apex.) -/
lemma degree_B2 (j : Fin 5) : G.degree (B2 j) = 4 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 0 + 0 + 3 + 0 + 1 := by
      congr
      . calc
          _ = Finset.card (∅ : Finset (Fin 2)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 3)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv, G, GAdj]
        _ = 1 := by simp
    _ = _ := by norm_num

/-!
### Edge count via the handshaking lemma
We now sum the degrees and divide by 2.
-/
theorem edge_count_44 : G.edgeSet.ncard = 44 := by
  classical
  -- Handshaking lemma on edge *set* cardinality.
  -- In current mathlib this comes as:
  --   `G.sum_degrees_eq_twice_card_edgeSet : (∑ v, G.degree v) = 2 * G.edgeSet.ncard`.
  have hand := G.sum_degrees_eq_twice_card_edges
  rw [←SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [←Equiv.sum_comp VEquiv.symm _] at hand
  simp_rw [Fintype.sum_sum_type] at hand
  simp [VEquiv, degree_A1, degree_B1, degree_A2, degree_B2, degree_apex, -Set.toFinset_card] at hand
  grind

end PikhurkoN5


-- 4. Show red neighbors of apex are ≥ 11 if no blue K_{1,5}

namespace PikhurkoN5
open V

/-! ### Small utilities -/

/- Pick a `k`-subset of a finset `s` when `k ≤ s.card`. -/
namespace Finset
variable {α : Type*}

lemma exists_subset_card_eq (s : Finset α) {k : ℕ} (hk : k ≤ s.card) :
  ∃ t ⊆ s, t.card = k := by
  exact Finset.le_card_iff_exists_subset_card.mp hk

end Finset

/-- In `Fin 2`, saying “equals `1`” is the same as “not equal to `0`”. -/
lemma fin2_eq_one_iff_ne_zero (a : Fin 2) : (a = 1) ↔ a ≠ 0 := by
  fin_cases a <;> simp

/-! ### Red neighbors of the apex are ≥ 11 if there is no blue star K_{1,5} -/

/-- The set of blue neighbors of `apex` in color class `0`. -/
noncomputable def blueNeighbors (color : Sym2 V → Fin 2) : Finset V :=
  (G.neighborFinset apex).filter (fun v => color (Sym2.mk (apex, v)) = 0)

/-- The set of red neighbors of `apex` in color class `1`. -/
noncomputable def redNeighbors (color : Sym2 V → Fin 2) : Finset V :=
  (G.neighborFinset apex).filter (fun v => color (Sym2.mk (apex, v)) = 1)

/-- If there is no blue `K_{1,5}`, then the apex has at most 4 blue neighbors. -/
lemma blueNeighbors_card_le_4
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (blueNeighbors color).card ≤ 4 := by
  classical
  -- Suppose ≥5 blue neighbors; extract a 5-subset and get a blue star.
  by_contra hle
  have hge : 5 ≤ (blueNeighbors color).card :=
    Nat.succ_le_of_lt (lt_of_not_ge hle)
  obtain ⟨S, hSsubset, hScard⟩ :=
    Finset.exists_subset_card_eq (blueNeighbors color) hge

  -- `apex ∉ S` since `apex` is not its own neighbor.
  have hapex_notin : apex ∉ S := by
    have : apex ∉ G.neighborFinset apex := by
      -- No loops ⇒ apex not adjacent to itself ⇒ not in neighbor set.
      simp [SimpleGraph.neighborFinset]
    exact fun hx => this <| (by
      have hx' : apex ∈ blueNeighbors color := hSsubset hx
      -- Blue neighbors are a subset of neighbors.
      have : blueNeighbors color ⊆ G.neighborFinset apex :=
        by
          intro v hv
          exact Finset.mem_of_mem_filter _ hv
      exact this hx')

  -- All edges from `apex` to `S` are present and blue, so we have a blue K_{1,5}.
  have hstar : hasMonoStar G color 0 5 := by
    refine ⟨apex, S, hScard, hapex_notin, ?_⟩
    intro y hy
    have hy' : y ∈ blueNeighbors color := hSsubset hy
    have hy_in : y ∈ G.neighborFinset apex ∧ color (Sym2.mk (apex, y)) = 0 := by
      simpa [blueNeighbors] using hy'
    exact ⟨by simpa using hy_in.1, hy_in.2⟩

  exact hNoBlueStar hstar

/-- If there is no blue `K_{1,5}`, then at least `11` neighbors of `apex` are red. -/
lemma red_from_apex_at_least_11
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (redNeighbors color).card ≥ 11 := by
  classical
  -- Split neighbors of apex into blue vs. non-blue; identify non-blue with red.
  have hsplit :
      (blueNeighbors color).card
      + ((G.neighborFinset apex).filter (fun v => ¬ (color (Sym2.mk (apex, v)) = 0))).card
      = (G.neighborFinset apex).card := by
    simpa [blueNeighbors] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset apex)
        (p := fun v => color (Sym2.mk (apex, v)) = 0))

  have hred_is_notblue :
      (G.neighborFinset apex).filter (fun v => ¬ (color (Sym2.mk (apex, v)) = 0))
      =
      redNeighbors color := by
    ext v; by_cases hv : v ∈ G.neighborFinset apex
    · -- On neighbors, “not blue” is “red”.
      simp [redNeighbors, hv, fin2_eq_one_iff_ne_zero]
    · simp [redNeighbors, hv]

  -- So blue + red = all neighbors = 15 (by `degree_apex`).
  have hsum : (blueNeighbors color).card + (redNeighbors color).card
              = (G.neighborFinset apex).card := by
    convert Finset.card_sdiff_add_card_eq_card _
    . simp [←hred_is_notblue, blueNeighbors]
      grind
    . infer_instance
    simp [redNeighbors]


  have hdeg : (G.neighborFinset apex).card = 15 := by
    simp [degree_apex]

  have hblue_le_4 := blueNeighbors_card_le_4 color hNoBlueStar

  -- Turn `blue + red = 15` into `red = 15 - blue`.
  have hred_eq : (redNeighbors color).card
      = 15 - (blueNeighbors color).card := by
    have hsum' : (redNeighbors color).card + (blueNeighbors color).card = 15 := by
      simpa [Nat.add_comm, hdeg] using hsum
    have := congrArg (fun t => t - (blueNeighbors color).card) hsum'
    -- `(red + blue) - blue = 15 - blue` ⇒ `red = 15 - blue`.
    simpa [Nat.add_sub_cancel] using this

  -- Finally: `blue ≤ 4` ⇒ `15 - blue ≥ 11`.
  have : 11 ≤ 15 - (blueNeighbors color).card :=
    by grind

  -- Combine with `red = 15 - blue`.
  simpa [hred_eq] using this

end PikhurkoN5


-- 5. Pigeonhole: one block gets ≥ 6 red edges from apex
namespace PikhurkoN5
open V

/-- Membership in the first block `{A1, B1}`. -/
def inBlock1 : V → Prop
| A1 _ => True
| B1 _ => True
| _    => False

noncomputable instance : DecidablePred inBlock1 := by
  intro v; cases v <;> infer_instance

/-- Red neighbors of `apex` that lie in the first block `{A1,B1}`. -/
noncomputable def redBlock1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => inBlock1 v)

/-- Red neighbors of `apex` that lie in the second block `{A2,B2}`.

We implement this as the *complement* of `inBlock1` inside `redNeighbors`.
Since `apex ∉ redNeighbors color`, this is exactly the `{A2,B2}` part. -/
noncomputable def redBlock2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => ¬ inBlock1 v)

/-- Partition of the red neighbors of `apex` into the two blocks. -/
lemma redBlocks_partition_card (color : Sym2 V → Fin 2) :
  (redBlock1 color).card + (redBlock2 color).card = (redNeighbors color).card := by
  classical
  -- Standard `filter` + `filter (¬p)` partition identity.
  simpa [redBlock1, redBlock2] using
    (Finset.card_filter_add_card_filter_not
      (s := redNeighbors color) (p := fun v => inBlock1 v))

/-- **Pigeonhole step.** If there is no blue `K_{1,5}`, then
one of the two blocks receives at least six red edges from `apex`. -/
lemma exists_block_receives_at_least_6_red
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (redBlock1 color).card ≥ 6 ∨ (redBlock2 color).card ≥ 6 := by
  classical
  -- Total red edges from `apex` is at least 11 (done earlier).
  have h11 : 11 ≤ (redNeighbors color).card :=
    red_from_apex_at_least_11 color hNoBlueStar
  -- Split red neighbors across the two blocks.
  have hsum := redBlocks_partition_card color
  -- If both blocks had ≤ 5, then the total would be ≤ 10 — contradiction.
  by_contra h
  push_neg at h   -- h : (redBlock1 color).card ≤ 5 ∧ (redBlock2 color).card ≤ 5
  have hle10 : (redNeighbors color).card ≤ 10 := by
    have : (redBlock1 color).card + (redBlock2 color).card ≤ 5 + 5 := by
      grind
    simpa [hsum] using this
  exact (Nat.not_succ_le_self 10) (le_trans h11 hle10)

end PikhurkoN5


-- 6. demonstrate a red neighbor in the clique side

namespace PikhurkoN5
open V

/-! ## Part / block predicates -/

/-- Recognizes the clique side `A1`. -/
def isA1 : V → Prop
| A1 _ => True | _ => False

/-- Recognizes the independent side `B1`. -/
def isB1 : V → Prop
| B1 _ => True | _ => False

/-- Recognizes the clique side `A2`. -/
def isA2 : V → Prop
| A2 _ => True | _ => False

/-- Recognizes the independent side `B2`. -/
def isB2 : V → Prop
| B2 _ => True | _ => False

/-- Second block `{A2,B2}`. -/
def inBlock2 : V → Prop
| A2 _ => True | B2 _ => True | _ => False

noncomputable instance : DecidablePred isA1 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred isB1 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred isA2 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred isB2 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred inBlock1 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred inBlock2 := by intro v; cases v <;> infer_instance

@[simp] lemma inBlock1_iff (v : V) : inBlock1 v ↔ (isA1 v ∨ isB1 v) := by
  cases v <;> simp [inBlock1, isA1, isB1]

@[simp] lemma inBlock2_iff (v : V) : inBlock2 v ↔ (isA2 v ∨ isB2 v) := by
  cases v <;> simp [inBlock2, isA2, isB2]

@[simp] lemma not_isA1_and_isB1 (v : V) : ¬ (isA1 v ∧ isB1 v) := by
  cases v <;> simp [isA1, isB1]

@[simp] lemma not_isA2_and_isB2 (v : V) : ¬ (isA2 v ∧ isB2 v) := by
  cases v <;> simp [isA2, isB2]

/-! ## Splitting the `apex` red neighbors by parts -/

-- These came from the previous step you have:
-- def redNeighbors (color : Sym2 V → Fin 2) : Finset V := ...


/-- Further refine `redBlock1` into its `A1` and `B1` parts. -/
noncomputable def redBlock1A1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isA1 v)

noncomputable def redBlock1B1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isB1 v)

/-- Further refine `redBlock2` into its `A2` and `B2` parts. -/
noncomputable def redBlock2A2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isA2 v)

noncomputable def redBlock2B2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isB2 v)

/-- `redBlock1` is exactly the disjoint union of its `A1` and `B1` parts. -/
lemma redBlock1_eq_union (color : Sym2 V → Fin 2) :
  redBlock1 color =
    redBlock1A1 color ∪ redBlock1B1 color := by
  ext v; constructor
  · intro hv
    rcases Finset.mem_filter.1 hv with ⟨hRN, hB⟩
    have : isA1 v ∨ isB1 v := (inBlock1_iff v).1 hB
    cases this with
    | inl hA1 => exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hRN, hA1⟩))
    | inr hB1 => exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hRN, hB1⟩))
  · intro hv
    rcases Finset.mem_union.1 hv with hA1 | hB1
    · rcases Finset.mem_filter.1 hA1 with ⟨hRN, hA1⟩
      exact Finset.mem_filter.2 ⟨hRN, (inBlock1_iff v).2 (Or.inl hA1)⟩
    · rcases Finset.mem_filter.1 hB1 with ⟨hRN, hB1⟩
      exact Finset.mem_filter.2 ⟨hRN, (inBlock1_iff v).2 (Or.inr hB1)⟩

/-- `redBlock2` is exactly the disjoint union of its `A2` and `B2` parts. -/
lemma redBlock2_eq_union (color : Sym2 V → Fin 2) :
  redBlock2 color =
    redBlock2A2 color ∪ redBlock2B2 color := by
  ext v; constructor
  · intro hv
    rcases Finset.mem_filter.1 hv with ⟨hRN, hB⟩
    have : isA2 v ∨ isB2 v := by
      apply (inBlock2_iff v).1
      cases v <;> simp_all [inBlock1, inBlock2, redNeighbors]

    cases this with
    | inl hA2 => exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hRN, hA2⟩))
    | inr hB2 => exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hRN, hB2⟩))
  · intro hv
    rcases Finset.mem_union.1 hv with hA2 | hB2
    · rcases Finset.mem_filter.1 hA2 with ⟨hRN, hA2⟩
      exact Finset.mem_filter.2 ⟨hRN, by
        cases v <;> simp_all [inBlock1, isA2]
        ⟩
    · rcases Finset.mem_filter.1 hB2 with ⟨hRN, hB2⟩
      exact Finset.mem_filter.2 ⟨hRN, by
        cases v <;> simp_all [inBlock1, isB2]⟩

/-- The two parts of `redBlock1` are disjoint. -/
lemma redA1_redB1_disjoint (color : Sym2 V → Fin 2) :
  Disjoint (redBlock1A1 color) (redBlock1B1 color) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro v hvA hvB
  rcases Finset.mem_filter.1 hvA with ⟨_, hA1⟩
  rcases Finset.mem_filter.1 hvB with ⟨_, hB1⟩
  exact (not_isA1_and_isB1 v) ⟨hA1, hB1⟩

/-- The two parts of `redBlock2` are disjoint. -/
lemma redA2_redB2_disjoint (color : Sym2 V → Fin 2) :
  Disjoint (redBlock2A2 color) (redBlock2B2 color) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro v hvA hvB
  rcases Finset.mem_filter.1 hvA with ⟨_, hA2⟩
  rcases Finset.mem_filter.1 hvB with ⟨_, hB2⟩
  exact (not_isA2_and_isB2 v) ⟨hA2, hB2⟩

/-- Cardinal decompositions of the blocks. -/
lemma redBlock1_card_eq_sum (color : Sym2 V → Fin 2) :
  (redBlock1 color).card
    = (redBlock1A1 color).card + (redBlock1B1 color).card := by
  classical
  have := Finset.card_union_add_card_inter
            (s := redBlock1A1 color) (t := redBlock1B1 color)
  -- rewrite the union as `redBlock1` and show the intersection is empty
  have hU : redBlock1A1 color ∪ redBlock1B1 color = redBlock1 color := by
    rw [redBlock1_eq_union]
  have hI : (redBlock1A1 color ∩ redBlock1B1 color).card = 0 := by
    have hdis := redA1_redB1_disjoint color
    -- `disjoint` implies the intersection is empty
    have : redBlock1A1 color ∩ redBlock1B1 color = (∅ : Finset V) := by
      simp [Disjoint] at hdis
      aesop
    aesop
  -- put it together
  have := by simpa [hU, hI, add_comm] using this
  exact this

lemma redBlock2_card_eq_sum (color : Sym2 V → Fin 2) :
  (redBlock2 color).card
    = (redBlock2A2 color).card + (redBlock2B2 color).card := by
  classical
  have := Finset.card_union_add_card_inter
            (s := redBlock2A2 color) (t := redBlock2B2 color)
  have hU : redBlock2A2 color ∪ redBlock2B2 color = redBlock2 color := by
    rw [redBlock2_eq_union]
  have hdis := redA2_redB2_disjoint color
  have hI : (redBlock2A2 color ∩ redBlock2B2 color).card = 0 := by
    have : redBlock2A2 color ∩ redBlock2B2 color = (∅ : Finset V) := by
      simp [Disjoint] at hdis
      aesop
    simp [this]
  have := by simpa [hU, hI, add_comm] using this
  exact this

/-! ## Bounding the `B`-parts by `5` -/

/-- All `B1`-vertices as a finset (image of `Fin 5`). -/
def B1Set : Finset V := (Finset.univ.image fun j : Fin 5 => B1 j)

/-- All `B2`-vertices as a finset (image of `Fin 5`). -/
def B2Set : Finset V := (Finset.univ.image fun j : Fin 5 => B2 j)

lemma redBlock1B1_subset_B1Set (color : Sym2 V → Fin 2) :
  redBlock1B1 color ⊆ B1Set := by
  classical
  intro v hv
  rcases Finset.mem_filter.1 hv with ⟨_, hB1⟩
  -- From `isB1 v`, `v = B1 j` for some `j`, hence in the image.
  cases v with
  | B1 j =>
      simp [B1Set]    -- `v` is exactly `B1 j`, hence in the image of `j`.
  | A1 _ => cases hB1
  | A2 _ => cases hB1
  | B2 _ => cases hB1
  | apex => cases hB1

lemma redBlock2B2_subset_B2Set (color : Sym2 V → Fin 2) :
  redBlock2B2 color ⊆ B2Set := by
  classical
  intro v hv
  rcases Finset.mem_filter.1 hv with ⟨_, hB2⟩
  cases v with
  | B2 j =>
      simp [B2Set]
  | A1 _ => cases hB2
  | B1 _ => cases hB2
  | A2 _ => cases hB2
  | apex => cases hB2

lemma card_B1Set_le_5 : (B1Set).card ≤ 5 := by
  classical
  -- image has card ≤ card of the domain
  simpa [B1Set, Fintype.card_fin] using
    (Finset.card_image_le : (Finset.univ.image (fun j : Fin 5 => B1 j)).card ≤ (Finset.univ : Finset (Fin 5)).card)

lemma card_B2Set_le_5 : (B2Set).card ≤ 5 := by
  classical
  simpa [B2Set, Fintype.card_fin] using
    (Finset.card_image_le : (Finset.univ.image (fun j : Fin 5 => B2 j)).card ≤ (Finset.univ : Finset (Fin 5)).card)

lemma redBlock1B1_card_le_5 (color : Sym2 V → Fin 2) :
  (redBlock1B1 color).card ≤ 5 :=
  (Finset.card_le_card (redBlock1B1_subset_B1Set color)).trans card_B1Set_le_5

lemma redBlock2B2_card_le_5 (color : Sym2 V → Fin 2) :
  (redBlock2B2 color).card ≤ 5 :=
  (Finset.card_le_card (redBlock2B2_subset_B2Set color)).trans card_B2Set_le_5

/-! ## Existence of a red neighbor in the clique parts `A1` / `A2` -/

/-- If block 1 receives at least 6 red neighbors from `apex`, then one of them lies in `A1`. -/
lemma exists_red_A1_of_block1_ge6
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock1 color).card) :
    ∃ i : Fin 2, G.Adj apex (A1 i) ∧ color (Sym2.mk (apex, A1 i)) = 1 := by
  classical
  -- From the decomposition `|redBlock1| = |A1-part| + |B1-part|`
  -- and `|B1-part| ≤ 5`, we get `|A1-part| ≥ 1`.
  have hdecomp := redBlock1_card_eq_sum color
  have hB1le := redBlock1B1_card_le_5 color
  have hposA1 : 0 < (redBlock1A1 color).card := by
    -- If `A1-part` were empty, then `|redBlock1| = |B1-part| ≤ 5`, contradicting `≥ 6`.
    by_contra hzero
    have hz : (redBlock1A1 color).card = 0 := Nat.eq_zero_of_not_pos hzero
    have : (redBlock1 color).card = (redBlock1B1 color).card := by
      simp [hdecomp, hz, zero_add]
    have : (redBlock1 color).card ≤ 5 := by simpa [this] using hB1le
    grind
  -- Choose a vertex `v` in the `A1` part.
  rcases Finset.card_pos.1 hposA1 with ⟨v, hv⟩
  -- From membership we extract adjacency and redness.
  rcases Finset.mem_filter.1 hv with ⟨hRN, hA1⟩
  rcases Finset.mem_filter.1 hRN with ⟨hNei, hRed⟩
  -- Now `v` must be of the form `A1 i`.
  cases v with
  | A1 i =>
      exact ⟨i, by aesop, by simpa using hRed⟩
  | B1 _ => cases hA1
  | A2 _ => cases hA1
  | B2 _ => cases hA1
  | apex  => cases hA1

/-- If block 2 receives at least 6 red neighbors from `apex`, then one of them lies in `A2`. -/
lemma exists_red_A2_of_block2_ge6
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock2 color).card) :
    ∃ i : Fin 3, G.Adj apex (A2 i) ∧ color (Sym2.mk (apex, A2 i)) = 1 := by
  classical
  have hdecomp := redBlock2_card_eq_sum color
  have hB2le := redBlock2B2_card_le_5 color
  have hposA2 : 0 < (redBlock2A2 color).card := by
    by_contra hzero
    have hz : (redBlock2A2 color).card = 0 := Nat.eq_zero_of_not_pos hzero
    have : (redBlock2 color).card = (redBlock2B2 color).card := by
      simp [hdecomp, hz, zero_add]
    have : (redBlock2 color).card ≤ 5 := by simpa [this] using hB2le
    grind
  rcases Finset.card_pos.1 hposA2 with ⟨v, hv⟩
  rcases Finset.mem_filter.1 hv with ⟨hRN, hA2⟩
  rcases Finset.mem_filter.1 hRN with ⟨hNei, hRed⟩
  cases v with
  | A2 i =>
      exact ⟨i, by aesop, by simpa using hRed⟩
  | A1 _ => cases hA2
  | B1 _ => cases hA2
  | B2 _ => cases hA2
  | apex  => cases hA2

/-- Corollary: under the “no blue star” hypothesis, there is a red neighbor of `apex`
in the appropriate clique `A1` or `A2`. -/
lemma exists_red_clique_neighbor
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (∃ i : Fin 2, G.Adj apex (A1 i) ∧ color (Sym2.mk (apex, A1 i)) = 1) ∨
    (∃ i : Fin 3, G.Adj apex (A2 i) ∧ color (Sym2.mk (apex, A2 i)) = 1) := by
  classical
  -- Your previous lemma:
  have h := exists_block_receives_at_least_6_red color hNoBlueStar
  rcases h with h1 | h2
  · exact Or.inl (exists_red_A1_of_block1_ge6 color h1)
  · exact Or.inr (exists_red_A2_of_block2_ge6 color h2)

end PikhurkoN5


-- 7. triangle-or-star from the clique vertex

namespace PikhurkoN5
open V

/-! ### Helpers: the chosen clique vertex lies in the corresponding red block -/

lemma A1_mem_redBlock1_of_red
    (color : Sym2 V → Fin 2) (i : Fin 2)
    (_hAdj : G.Adj apex (A1 i))
    (hRed : color (Sym2.mk (apex, A1 i)) = 1) :
    A1 i ∈ redBlock1 color := by
  classical
  -- First: `A1 i` is a red neighbor of `apex`.
  have hRN : A1 i ∈ redNeighbors color := by
    -- `neighborFinset` membership + color=1
    have : A1 i ∈ G.neighborFinset apex := by simp
    exact Finset.mem_filter.mpr ⟨this, by simpa⟩
  -- Second: it's in block 1.
  have hB : inBlock1 (A1 i) := by simp [inBlock1]
  -- Filter once more.
  simpa [redBlock1] using Finset.mem_filter.mpr ⟨hRN, hB⟩

lemma A2_mem_redBlock2_of_red
    (color : Sym2 V → Fin 2) (i : Fin 3)
    (_hAdj : G.Adj apex (A2 i))
    (hRed : color (Sym2.mk (apex, A2 i)) = 1) :
    A2 i ∈ redBlock2 color := by
  classical
  have hRN : A2 i ∈ redNeighbors color := by
    have : A2 i ∈ G.neighborFinset apex := by simp
    exact Finset.mem_filter.mpr ⟨this, by simpa⟩
  have hB : inBlock2 (A2 i) := by simp [inBlock2]
  simp [redBlock2, hRN, isA1, isB1]

/-! ### Triangle-or-star from Block 1 -/

/-- If Block 1 has at least 6 red apex-neighbors, and one of them is `A1 i` with a red edge
from `apex`, then either we have a red triangle, or a blue `K_{1,5}` centered at `A1 i`. -/
lemma triangle_or_blueStar_from_block1
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock1 color).card)
    (i : Fin 2)
    (hAdj : G.Adj apex (A1 i))
    (hRedApexA1 : color (Sym2.mk (apex, A1 i)) = 1) :
    hasMonoTriangle G color 1 ∨ hasMonoStar G color 0 5 := by
  classical
  -- Put `y0 := A1 i` into `redBlock1`.
  have hy0_in : A1 i ∈ redBlock1 color := A1_mem_redBlock1_of_red color i hAdj hRedApexA1
  -- We want 5 vertices in `redBlock1 \ {A1 i}`.
  have h5 :
    5 ≤ ((redBlock1 color).erase (A1 i)).card := by
    -- `card (erase y0) + 1 = card`  ⇒  `card (erase y0) ≥ 5` from `card ≥ 6`
    have hcard :
        ((redBlock1 color).erase (A1 i)).card + 1 = (redBlock1 color).card :=
      Finset.card_erase_add_one hy0_in
    -- turn `6 ≤ RHS` into `5 ≤ LHS`
    have : 6 ≤ ((redBlock1 color).erase (A1 i)).card + 1 := by simpa [hcard] using h6
    exact (Nat.succ_le_succ_iff.mp this)
  -- Pick any 5-element subset `T` of those.
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq ((redBlock1 color).erase (A1 i)) h5

  -- Either some `y ∈ T` makes the edge `(A1 i,y)` red (→ triangle), or all are blue (→ star).
  classical
  by_cases hTri : ∃ y ∈ T, color (Sym2.mk (A1 i, y)) = 1
  · rcases hTri with ⟨y, hyT, hyRedA1y⟩
    -- Facts from membership: `y ≠ A1 i`, `y ∈ redBlock1`.
    have hy_erase : y ∈ (redBlock1 color).erase (A1 i) := hTsub hyT
    have hy_ne : y ≠ A1 i := (Finset.mem_erase.mp hy_erase).1
    have hy_in : y ∈ redBlock1 color := (Finset.mem_erase.mp hy_erase).2
    -- Unpack `redBlock1` membership to get that `y` is a red neighbor of `apex` in block 1.
    rcases Finset.mem_filter.1 hy_in with ⟨hy_RN, hy_block1⟩
    rcases Finset.mem_filter.1 hy_RN with ⟨hyAdjApex, hyRedApexY⟩
    -- `A1 i` is adjacent to every other vertex in Block 1 (clique-to-A1, clique-to-B1).
    have hyAdjA1Y : G.Adj (A1 i) y := by
      cases y with
      | A1 j =>
          -- `j ≠ i` because `y ≠ A1 i`
          have hij : j ≠ i := by
            intro h; exact hy_ne (by simp [h])
          -- use `adj_A1A1 : Adj (A1 i) (A1 j) ↔ i ≠ j`
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A1A1, this]
      | B1 _  => simp [adj_A1B1]
      | A2 _  => cases hy_block1       -- impossible
      | B2 _  => cases hy_block1       -- impossible
      | apex  => cases hy_block1       -- impossible
    -- Build the red triangle: apex — A1 i — y — apex.
    refine Or.inl ?triangle
    refine ⟨apex, A1 i, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hAdj]
    · exact hyAdjA1Y
    · simpa using hyAdjApex
    · simpa using hRedApexA1
    · exact hyRedA1y
    · simpa using hyRedApexY
  · -- No red `(A1 i,y)` with `y ∈ T` ⇒ all `(A1 i,y)` are blue.
    have hAllBlue : ∀ {y}, y ∈ T → color (Sym2.mk (A1 i, y)) = 0 := by
      intro y hy
      have h1 : color (Sym2.mk (A1 i, y)) ≠ 1 := by
        intro contra; exact hTri ⟨y, hy, contra⟩
      -- In `Fin 2`, being not `1` is being `0`.
      -- (If you prefer, keep and reuse your earlier lemma `fin2_eq_one_iff_ne_zero`.)
      have : color (Sym2.mk (A1 i, y)) = 0 ∨ color (Sym2.mk (A1 i, y)) = 1 := by
        grind
      exact this.resolve_right h1
    -- Show `A1 i ∉ T`.
    have hnotin : A1 i ∉ T := by
      intro hx
      have : A1 i ∈ (redBlock1 color).erase (A1 i) := hTsub hx
      simp at this
    -- Adjacency `(A1 i,y)` for `y ∈ T`:
    have hAdjAll : ∀ {y}, y ∈ T → G.Adj (A1 i) y := by
      intro y hy
      have hy_erase : y ∈ (redBlock1 color).erase (A1 i) := hTsub hy
      have hy_ne : y ≠ A1 i := (Finset.mem_erase.mp hy_erase).1
      have hy_in : y ∈ redBlock1 color := (Finset.mem_erase.mp hy_erase).2
      rcases Finset.mem_filter.1 hy_in with ⟨_, hy_block1⟩
      -- same case split as above
      cases y with
      | A1 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A1A1, this]
      | B1 _  => simp [adj_A1B1]
      | A2 _  => simp [isA1, isB1] at hy_block1
      | B2 _  => simp [isA1, isB1] at hy_block1
      | apex  => simp [G, GAdj]
    -- We have a blue star of size 5 centered at `A1 i` with leaf-set `T`.
    refine Or.inr ?star
    refine ⟨A1 i, T, by simp [hTcard], hnotin, ?_⟩
    intro y hy
    exact ⟨hAdjAll hy, hAllBlue hy⟩

/-! ### Triangle-or-star from Block 2 (same proof pattern) -/

lemma triangle_or_blueStar_from_block2
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock2 color).card)
    (i : Fin 3)
    (hAdj : G.Adj apex (A2 i))
    (hRedApexA2 : color (Sym2.mk (apex, A2 i)) = 1) :
    hasMonoTriangle G color 1 ∨ hasMonoStar G color 0 5 := by
  classical
  have hy0_in : A2 i ∈ redBlock2 color := A2_mem_redBlock2_of_red color i hAdj hRedApexA2
  have h5 :
    5 ≤ ((redBlock2 color).erase (A2 i)).card := by
    have hcard :
        ((redBlock2 color).erase (A2 i)).card + 1 = (redBlock2 color).card :=
      Finset.card_erase_add_one hy0_in
    have : 6 ≤ ((redBlock2 color).erase (A2 i)).card + 1 := by simpa [hcard] using h6
    exact (Nat.succ_le_succ_iff.mp this)
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq ((redBlock2 color).erase (A2 i)) h5

  by_cases hTri : ∃ y ∈ T, color (Sym2.mk (A2 i, y)) = 1
  · rcases hTri with ⟨y, hyT, hyRedA2y⟩
    have hy_erase : y ∈ (redBlock2 color).erase (A2 i) := hTsub hyT
    have hy_ne : y ≠ A2 i := (Finset.mem_erase.mp hy_erase).1
    have hy_in : y ∈ redBlock2 color := (Finset.mem_erase.mp hy_erase).2
    rcases Finset.mem_filter.1 hy_in with ⟨hy_RN, hy_block2⟩
    rcases Finset.mem_filter.1 hy_RN with ⟨hyAdjApex, hyRedApexY⟩
    have hyAdjA2Y : G.Adj (A2 i) y := by
      cases y with
      | A2 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A2A2, this]
      | B2 _  => simp [adj_A2B2]
      | A1 _  => simp [isA1] at hy_block2
      | B1 _  => simp [isB1] at hy_block2
      | apex  => simp [G,GAdj]
    refine Or.inl ?triangle
    refine ⟨apex, A2 i, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hAdj]
    · exact hyAdjA2Y
    · aesop
    · simpa using hRedApexA2
    · exact hyRedA2y
    · simpa using hyRedApexY
  ·
    have hAllBlue : ∀ {y}, y ∈ T → color (Sym2.mk (A2 i, y)) = 0 := by
      intro y hy
      have h1 : color (Sym2.mk (A2 i, y)) ≠ 1 := by
        intro contra; exact hTri ⟨y, hy, contra⟩
      have : color (Sym2.mk (A2 i, y)) = 0 ∨ color (Sym2.mk (A2 i, y)) = 1 := by grind
      exact this.resolve_right h1
    have hnotin : A2 i ∉ T := by
      intro hx
      have : A2 i ∈ (redBlock2 color).erase (A2 i) := hTsub hx
      simp at this
    have hAdjAll : ∀ {y}, y ∈ T → G.Adj (A2 i) y := by
      intro y hy
      have hy_erase : y ∈ (redBlock2 color).erase (A2 i) := hTsub hy
      have hy_ne : y ≠ A2 i := (Finset.mem_erase.mp hy_erase).1
      have hy_in : y ∈ redBlock2 color := (Finset.mem_erase.mp hy_erase).2
      rcases Finset.mem_filter.1 hy_in with ⟨_, hy_block2⟩
      cases y with
      | A2 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A2A2, this]
      | B2 _  => simp [adj_A2B2]
      | A1 _  => simp [isA1] at hy_block2
      | B1 _  => simp [isB1] at hy_block2
      | apex  => simp [G, GAdj]
    refine Or.inr ?star
    refine ⟨A2 i, T, by simp [hTcard], hnotin, ?_⟩
    intro y hy
    exact ⟨hAdjAll hy, hAllBlue hy⟩

/-! ### Final step: no blue K_{1,5} ⇒ a red triangle -/

/-- **Main step (n=5):** If there is no blue `K_{1,5}`, then the red color class contains a triangle. -/
theorem red_triangle_of_no_blue_star
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    hasMonoTriangle G color 1 := by
  classical
  -- One of the two blocks has ≥6 red neighbors from `apex`.
  have h6 := exists_block_receives_at_least_6_red color hNoBlueStar
  -- From that block, extract a clique vertex with a red edge from `apex`.
  rcases h6 with hB1 | hB2
  · -- Block 1 case
    rcases exists_red_A1_of_block1_ge6 color hB1 with ⟨i, hAdj, hRed⟩
    -- Either get triangle or (if star) contradict `hNoBlueStar`.
    rcases triangle_or_blueStar_from_block1 color hB1 i hAdj hRed with hTri | hStar
    · exact hTri
    · exact (hNoBlueStar hStar).elim
  · -- Block 2 case
    rcases exists_red_A2_of_block2_ge6 color hB2 with ⟨i, hAdj, hRed⟩
    rcases triangle_or_blueStar_from_block2 color hB2 i hAdj hRed with hTri | hStar
    · exact hTri
    · exact (hNoBlueStar hStar).elim

end PikhurkoN5

-- Final statement

namespace PikhurkoN5

theorem main : Pikhurko_n5_statement := by
  use V, G
  split_ands
  . exact edge_count_44
  intro color
  have := red_triangle_of_no_blue_star color
  grind
