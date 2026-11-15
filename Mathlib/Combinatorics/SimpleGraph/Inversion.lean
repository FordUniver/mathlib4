/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.InducedCopy
public import Mathlib.Data.Fintype.Lattice

/-!
# Möbius inversion between copy counts and induced copy counts

For a guest graph `G : SimpleGraph V` and a host graph `H : SimpleGraph W` with finite
vertex types, this file establishes the standard summation identity expressing the copy
count `H.copyCount G` as a sum of induced copy counts `H.embeddingCount G'` over the graphs
`G'` obtained from `G` by adding edges, together with its Möbius inverse expressing
`H.embeddingCount G` as a signed sum of `H.copyCount G'`.

Both sums are indexed by the sets `S` of non-edges of `G`, that is by the subsets of
`Gᶜ.edgeFinset`, and the graph obtained by adding `S` to `G` is `G ⊔ fromEdgeSet S`.

Following the convention from `Mathlib/Combinatorics/SimpleGraph/Copy.lean` and
`Mathlib/Combinatorics/SimpleGraph/InducedCopy.lean`, counting operations are host-first
(`H.copyCount G`, `H.embeddingCount G`); types are guest-first (`Copy G H`, `Embedding G H`).

## Main declarations

* `SimpleGraph.Copy.inducedShape` — for `f : Copy G H`, the supergraph of `G` on `V`
  recording the induced adjacency on the image, transported back via `f.toEmbedding`.
* `SimpleGraph.Copy.fiberInducedShapeEquiv` — the bijection between copies of `G` with a
  prescribed induced shape `G'` and graph embeddings of `G'`.
* `SimpleGraph.Copy.leInducedShapeEquiv` — the bijection between copies of `G` whose induced
  shape contains `G'` and copies of `G'`.

## Main results

* `SimpleGraph.copyCount_eq_sum_embeddingCount` — forward identity:
  `H.copyCount G = ∑ S ∈ Gᶜ.edgeFinset.powerset, H.embeddingCount (G ⊔ fromEdgeSet S)`.
* `SimpleGraph.embeddingCount_eq_sum_signed_copyCount` — Möbius inverse over `ℤ`:
  `H.embeddingCount G = ∑ S ∈ Gᶜ.edgeFinset.powerset, (-1) ^ #S * H.copyCount (G ⊔ fromEdgeSet S)`.

## Implementation notes

Every copy `f` of `G` in `H` has an induced shape `f.inducedShape`, a supergraph of `G`, and `f`
is a copy of `G'` iff `G' ≤ f.inducedShape` and an embedding of `G'` iff `G' = f.inducedShape`.
The forward identity partitions the copies of `G` by the set of non-edges of `G` in their induced
shape. The Möbius inverse is the inclusion-exclusion principle
`Finset.inclusion_exclusion_card_inf_compl` applied to the sets of copies of `G` mapping a given
non-edge of `G` to an edge of `H`.

The sums range over sets of non-edges of `G` rather than over the supergraphs of `G`, so that
the statements do not depend on the order structure of `SimpleGraph V`.

The Möbius identity is stated in `ℤ` (rather than `ℕ`) because the signs are essential.
-/

public section

open Finset Function

namespace SimpleGraph

variable {V W : Type*}

/-! ### Induced shape of a copy

The pullback `H.comap f.toEmbedding` records the induced adjacency on the image of a copy
`f : Copy G H`, transported back to `V`. It is always a supergraph of `G`, and pinning it
down to a specific supergraph `G'` promotes the copy to an embedding `G' ↪g H`. -/

namespace Copy

variable {G G' : SimpleGraph V} {H : SimpleGraph W}

/-- The pullback of the host graph along the underlying injection of a copy. -/
def inducedShape (f : Copy G H) : SimpleGraph V :=
  H.comap f.toEmbedding

@[simp] lemma inducedShape_adj (f : Copy G H) {a b : V} :
    f.inducedShape.Adj a b ↔ H.Adj (f a) (f b) := Iff.rfl

lemma le_inducedShape (f : Copy G H) : G ≤ f.inducedShape :=
  fun _ _ => f.toHom.map_adj

/-- A copy with induced shape `G'` promotes to a graph embedding `G' ↪g H`. -/
@[expose] def toEmbeddingOfInducedShapeEq (f : Copy G H) (h : f.inducedShape = G') :
    G' ↪g H where
  toFun := f
  inj' := f.injective
  map_rel_iff' {a b} := by
    change H.Adj (f a) (f b) ↔ G'.Adj a b
    rw [← h, inducedShape_adj]

@[simp] lemma toEmbeddingOfInducedShapeEq_apply (f : Copy G H) (h : f.inducedShape = G')
    (v : V) : f.toEmbeddingOfInducedShapeEq h v = f v := rfl

/-- The fiber of `inducedShape` over a supergraph `G' ≥ G` is canonically `Embedding G' H`. -/
def fiberInducedShapeEquiv (hGG' : G ≤ G') :
    {f : Copy G H // f.inducedShape = G'} ≃ Embedding G' H where
  toFun f := f.val.toEmbeddingOfInducedShapeEq f.prop
  invFun e := ⟨e.toCopy.comp (Copy.ofLE G G' hGG'), by ext a b; simp [inducedShape]⟩
  left_inv f := by apply Subtype.ext; ext v; simp
  right_inv e := by apply DFunLike.ext; intro v; simp

/-- The copies of `G` in `H` whose induced shape contains a supergraph `G' ≥ G` are canonically
the copies of `G'` in `H`. -/
def leInducedShapeEquiv (hGG' : G ≤ G') :
    {f : Copy G H // G' ≤ f.inducedShape} ≃ Copy G' H where
  toFun f := ⟨⟨f.val, fun hab => f.val.inducedShape_adj.mp (f.prop hab)⟩, f.val.injective⟩
  invFun f := ⟨f.comp (Copy.ofLE G G' hGG'), fun _ _ hab => by simpa using f.toHom.map_adj hab⟩
  left_inv f := by apply Subtype.ext; ext v; simp
  right_inv f := by ext v; simp

end Copy

@[simp] lemma Embedding.inducedShape_toCopy {G : SimpleGraph V} {H : SimpleGraph W}
    (e : Embedding G H) : e.toCopy.inducedShape = G := by
  ext a b; rw [Copy.inducedShape_adj]; exact e.map_rel_iff

/-! ### Adding non-edges to a graph

Every supergraph `K` of `G` is `G ⊔ fromEdgeSet s` for a unique set `s` of non-edges of `G`,
namely the set of edges of `K` that are not edges of `G`. -/

section SupFromEdgeSet

variable {G K : SimpleGraph V} {s : Set (Sym2 V)}

/-- A set of edges of a graph contains no diagonal element. -/
private lemma sdiff_diagSet_of_subset_edgeSet (hs : s ⊆ K.edgeSet) : s \ Sym2.diagSet = s :=
  sdiff_eq_left.2 <| Set.subset_compl_iff_disjoint_right.1 <|
    hs.trans (edgeSet_subset_compl_diagSet K)

/-- Adding a set `s` of non-edges of `G` to `G` yields a subgraph of a supergraph `K` of `G` iff
all elements of `s` are edges of `K`. -/
lemma sup_fromEdgeSet_le_iff (hGK : G ≤ K) (hs : s ⊆ Gᶜ.edgeSet) :
    G ⊔ fromEdgeSet s ≤ K ↔ s ⊆ K.edgeSet := by
  rw [sup_le_iff, and_iff_right hGK, fromEdgeSet_le, sdiff_diagSet_of_subset_edgeSet hs]

/-- A supergraph `K` of `G` is obtained by adding a set `s` of non-edges of `G` to `G` iff `s` is
the set of edges of `K` that are not edges of `G`. -/
lemma eq_sup_fromEdgeSet_iff (hGK : G ≤ K) (hs : s ⊆ Gᶜ.edgeSet) :
    K = G ⊔ fromEdgeSet s ↔ K.edgeSet \ G.edgeSet = s := by
  have hGs : Disjoint G.edgeSet s := (disjoint_edgeSet.2 disjoint_compl_right).mono_right hs
  rw [← edgeSet_inj, edgeSet_sup, edgeSet_fromEdgeSet, sdiff_diagSet_of_subset_edgeSet hs]
  refine ⟨fun h => ?_, ?_⟩
  · rw [h]
    exact hGs.sup_sdiff_cancel_left
  · rintro rfl
    exact (Set.union_sdiff_cancel (edgeSet_subset_edgeSet.2 hGK)).symm

end SupFromEdgeSet

/-! ### Count identities -/

section Count

variable [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) [Fintype Gᶜ.edgeSet]

/-- Forward identity: every copy of `G` in `H` is an induced copy of exactly one of the graphs
obtained from `G` by adding a set `S` of non-edges of `G`. -/
theorem copyCount_eq_sum_embeddingCount :
    H.copyCount G = ∑ S ∈ Gᶜ.edgeFinset.powerset, H.embeddingCount (G ⊔ fromEdgeSet ↑S) := by
  classical
  have := Fintype.ofFinite (Copy G H)
  -- Partition the copies `f` of `G` by the set of non-edges of `G` in the induced shape of `f`.
  have hmaps : Set.MapsTo
      (fun f : Copy G H => (Set.toFinite (f.inducedShape.edgeSet \ G.edgeSet)).toFinset)
      (univ : Finset (Copy G H)) Gᶜ.edgeFinset.powerset := fun f _ => by
    rw [mem_coe, mem_powerset, Set.Finite.toFinset_subset, coe_edgeFinset, ← edgeSet_sdiff,
      edgeSet_subset_edgeSet, sdiff_le_iff, sup_compl_eq_top]
    exact le_top
  rw [copyCount_eq_nat_card, Nat.card_eq_fintype_card, ← card_univ,
    card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun S hS => ?_
  have hS' : (S : Set (Sym2 V)) ⊆ Gᶜ.edgeSet := by
    rw [← coe_edgeFinset, coe_subset]
    exact mem_powerset.1 hS
  rw [embeddingCount_eq_nat_card, ← Nat.card_congr (Copy.fiberInducedShapeEquiv le_sup_left)]
  refine (Nat.subtype_card _ fun f => ?_).symm
  rw [mem_filter_univ, ← coe_inj, Set.Finite.coe_toFinset,
    eq_sup_fromEdgeSet_iff f.le_inducedShape hS']

/-- The Möbius (signed-sum) inverse to `copyCount_eq_sum_embeddingCount`: the induced copy count
of `G` is the alternating sum of the copy counts of the graphs obtained from `G` by adding a set
`S` of non-edges of `G`. -/
theorem embeddingCount_eq_sum_signed_copyCount :
    (H.embeddingCount G : ℤ) =
      ∑ S ∈ Gᶜ.edgeFinset.powerset, (-1 : ℤ) ^ #S * (H.copyCount (G ⊔ fromEdgeSet ↑S) : ℤ) := by
  classical
  have := Fintype.ofFinite (Copy G H)
  -- `A e` is the set of copies of `G` in `H` mapping the non-edge `e` of `G` to an edge of `H`.
  let A (e : Sym2 V) : Finset (Copy G H) := {f | e ∈ f.inducedShape.edgeSet}
  -- The embeddings of `G` are the copies of `G` lying in no `A e`.
  have hemb : H.embeddingCount G = #(Gᶜ.edgeFinset.inf fun e => (A e)ᶜ) := by
    rw [embeddingCount_eq_nat_card, ← Nat.card_congr (Copy.fiberInducedShapeEquiv le_rfl)]
    refine Nat.subtype_card _ fun f => ?_
    simp only [A, mem_inf, mem_compl, mem_filter_univ, mem_edgeFinset]
    rw [← Set.disjoint_right, disjoint_edgeSet, disjoint_compl_right_iff,
      f.le_inducedShape.ge_iff_eq, eq_comm]
  -- The copies of `G ⊔ fromEdgeSet S` are the copies of `G` lying in `A e` for all `e ∈ S`.
  have hcopy (S : Finset (Sym2 V)) (hS : S ∈ Gᶜ.edgeFinset.powerset) :
      H.copyCount (G ⊔ fromEdgeSet ↑S) = #(S.inf A) := by
    have hS' : (S : Set (Sym2 V)) ⊆ Gᶜ.edgeSet := by
      rw [← coe_edgeFinset, coe_subset]
      exact mem_powerset.1 hS
    rw [copyCount_eq_nat_card, ← Nat.card_congr (Copy.leInducedShapeEquiv le_sup_left)]
    refine Nat.subtype_card _ fun f => ?_
    simp only [A, mem_inf, mem_filter_univ]
    rw [sup_fromEdgeSet_le_iff f.le_inducedShape hS']
    rfl
  rw [hemb, inclusion_exclusion_card_inf_compl]
  exact sum_congr rfl fun S hS => by rw [hcopy S hS]

end Count

end SimpleGraph
