/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.InducedCopy
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Set.Card

/-!
# Möbius inversion between copy counts and induced copy counts

For a guest graph `G : SimpleGraph V` and a host graph `H : SimpleGraph W` with finite
vertex types, this file establishes the standard summation identity expressing the copy
count `H.copyCount G` as a sum over supergraphs of `G` (on the same vertex type `V`) of
induced copy counts `H.embeddingCount G'`, together with its Möbius inverse expressing
`H.embeddingCount G` as a signed sum of `H.copyCount G'`.

Following the convention from `Mathlib/Combinatorics/SimpleGraph/Copy.lean` and
`Mathlib/Combinatorics/SimpleGraph/InducedCopy.lean`, counting operations are host-first
(`H.copyCount G`, `H.embeddingCount G`); types are guest-first (`Copy G H`, `Embedding G H`).

## Main declarations

* `SimpleGraph.Copy.inducedShape` — for `f : Copy G H`, the supergraph of `G` on `V`
  recording the induced adjacency on the image, transported back via `f.toEmbedding`.
* `SimpleGraph.Copy.fiberInducedShapeEquiv` — the per-fiber bijection between copies with a
  prescribed induced shape and graph embeddings of that shape.
* `SimpleGraph.Copy.equivSigmaEmbedding` — the load-bearing bijection
  `Copy G H ≃ Σ G' ∈ Icc G ⊤, Embedding G'.val H`.
* `SimpleGraph.iccEquivPowersetEdgeFinsetSdiff` — for `G ≤ K`, the equivalence
  `Finset.Icc G K ≃ (K.edgeFinset \ G.edgeFinset).powerset` used to reduce the inner
  alternating sum to `Finset.sum_powerset_neg_one_pow_card`.

## Main results

* `SimpleGraph.copyCount_eq_sum_embeddingCount` — forward identity:
  `H.copyCount G = ∑ G' ∈ Icc G ⊤, H.embeddingCount G'`.
* `SimpleGraph.embeddingCount_eq_sum_signed_copyCount` — Möbius inverse over `ℤ`:
  `(H.embeddingCount G : ℤ) = (-1) ^ Nat.card G.edgeSet *
    ∑ G' ∈ Icc G ⊤, (-1) ^ Nat.card G'.edgeSet * (H.copyCount G' : ℤ)`.

## Implementation notes

The forward bijection `Copy.equivSigmaEmbedding` is the only "real" content; the Möbius
direction reduces to it via the classical alternating-sum identity
`Finset.sum_powerset_neg_one_pow_card`, reindexed through the order-isomorphism
`G' ∈ Icc G ⊤ ↔ S ⊆ E(⊤) \ E(G)`.

The Möbius identity is stated in `ℤ` (rather than `ℕ`) because the signs are essential.
The user-facing form uses `Nat.card G.edgeSet` rather than `#(G'.edgeFinset \ G.edgeFinset)`
in the sign exponent: equivalent under `G ≤ G'` by parity, but `Nat.card` has no per-graph
`Fintype` hypothesis, keeping the theorem signature free of `Classical`.

The `LocallyFiniteOrder (SimpleGraph V)` instance consumed by `Finset.Icc G ⊤` comes from
`SimpleGraph.Finite.instLocallyFiniteOrder`, which requires `[DecidableLE (SimpleGraph V)]`.
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

end Copy

@[simp] lemma Embedding.inducedShape_toCopy {G : SimpleGraph V} {H : SimpleGraph W}
    (e : Embedding G H) : e.toCopy.inducedShape = G := by
  ext a b; rw [Copy.inducedShape_adj]; exact e.map_rel_iff

/-! ### Forward bijection and count identity -/

section Forward

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- The load-bearing equivalence: a copy of `G` in `H` is the same data as a choice of
supergraph `G' ∈ Icc G ⊤` (the induced shape) together with a graph embedding
`G' ↪g H`. This expresses every copy uniquely as an induced copy of some shape `G'`
between `G` and the complete graph.

The proof goes via the canonical fiber decomposition `Equiv.sigmaFiberEquiv` for the map
`Copy.inducedShape`. The index `K : SimpleGraph V` is restricted to `Icc G ⊤`, which is
exactly the set of shapes with nonempty fiber. The per-fiber bijection is
`Copy.fiberInducedShapeEquiv`. -/
noncomputable def Copy.equivSigmaEmbedding (G : SimpleGraph V) (H : SimpleGraph W)
    [Fintype V] [DecidableEq V] [DecidableLE (SimpleGraph V)] :
    Copy G H ≃ Σ G' : ↥(Finset.Icc G ⊤), Embedding G'.val H :=
  (Equiv.sigmaFiberEquiv (Copy.inducedShape : Copy G H → SimpleGraph V)).symm.trans <|
  { toFun := fun ⟨K, f⟩ =>
      let hGK : G ≤ K := f.prop ▸ f.val.le_inducedShape
      ⟨⟨K, Finset.mem_Icc.mpr ⟨hGK, le_top⟩⟩,
       Copy.fiberInducedShapeEquiv hGK f⟩
    invFun := fun ⟨⟨K, hK⟩, e⟩ =>
      ⟨K, (Copy.fiberInducedShapeEquiv (Finset.mem_Icc.mp hK).1).symm e⟩
    left_inv := by
      rintro ⟨K, f⟩
      simp
    right_inv := by
      rintro ⟨⟨K, hK⟩, e⟩
      simp only [Equiv.apply_symm_apply] }

/-- Forward identity: every copy of `G` in `H` is an induced copy of some unique
supergraph `G' ∈ Icc G ⊤` of `G`. -/
theorem copyCount_eq_sum_embeddingCount [Fintype V] [DecidableEq V]
    [DecidableLE (SimpleGraph V)] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) :
    H.copyCount G = ∑ G' ∈ Finset.Icc G ⊤, H.embeddingCount G' := by
  rw [copyCount_eq_nat_card, Nat.card_congr (Copy.equivSigmaEmbedding G H), Nat.card_sigma,
    ← Finset.sum_attach (Finset.Icc G ⊤) (fun G' => H.embeddingCount G')]
  refine Finset.sum_congr rfl fun G' _ => ?_
  exact (embeddingCount_eq_nat_card _ _).symm

end Forward

/-! ### Möbius (signed-sum) inverse

The Möbius inverse to the forward identity, expressing `H.embeddingCount G` as a signed
sum of `H.copyCount G'` over supergraphs `G' ∈ Icc G ⊤`. The proof reduces, via the
order-isomorphism `iccEquivPowersetEdgeFinsetSdiff` below, to the alternating-sum
identity `Finset.sum_powerset_neg_one_pow_card`.
-/

section Mobius

variable [Fintype V] [DecidableEq V] [DecidableLE (SimpleGraph V)]

/-! ### Finset of extra edges

Helper construction giving the Finset of edges in `K` but not in `G`, without requiring a
per-graph `Fintype` instance on the edge sets. Uses `Set.Finite.toFinset` (noncomputable). -/

/-- The set difference of edge sets on a finite vertex type is finite. -/
lemma edgeSet_sdiff_finite (G K : SimpleGraph V) : (K.edgeSet \ G.edgeSet).Finite :=
  Set.finite_univ.subset (Set.subset_univ _)

/-- The Finset of edges in `K` but not in `G`. Constructed via `Set.Finite.toFinset`,
so noncomputable, but requires no per-graph `Fintype` synthesis. -/
noncomputable def edgeSetSdiffFinset (G K : SimpleGraph V) : Finset (Sym2 V) :=
  (edgeSet_sdiff_finite G K).toFinset

@[simp] lemma mem_edgeSetSdiffFinset {G K : SimpleGraph V} {e : Sym2 V} :
    e ∈ edgeSetSdiffFinset G K ↔ e ∈ K.edgeSet ∧ e ∉ G.edgeSet :=
  Set.Finite.mem_toFinset _

/-- Under `G ≤ K`, `Nat.card K.edgeSet = Nat.card G.edgeSet + #(edgeSetSdiffFinset G K)`. -/
lemma natCard_edgeSet_eq_add_card_sdiff {G K : SimpleGraph V} (hGK : G ≤ K) :
    Nat.card K.edgeSet = Nat.card G.edgeSet + #(edgeSetSdiffFinset G K) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      show #(edgeSetSdiffFinset G K) = (K.edgeSet \ G.edgeSet).ncard from
        (Set.ncard_eq_toFinset_card _ (edgeSet_sdiff_finite G K)).symm,
      add_comm]
  exact (Set.ncard_diff_add_ncard_of_subset (edgeSet_subset_edgeSet.mpr hGK)).symm

/-! ### Bijection between Icc and powerset of extra edges -/

/-- Equivalence between the closed interval `Finset.Icc G K` of graphs and the powerset of
the Finset of edges in `K` not in `G`, when `G ≤ K`.

Forward: `G' ∈ [G, K]` maps to the Finset `edgeSetSdiffFinset G G'.val` (its extra edges
over `G`, automatically a subset of `edgeSetSdiffFinset G K` since `G' ≤ K`).

Inverse: a subset `S ⊆ edgeSetSdiffFinset G K` maps to `fromEdgeSet (G.edgeSet ∪ ↑S)`. -/
noncomputable def iccEquivPowersetEdgeFinsetSdiff
    {G K : SimpleGraph V} (hGK : G ≤ K) :
    ↥(Finset.Icc G K) ≃ ↥(edgeSetSdiffFinset G K).powerset where
  toFun G' :=
    ⟨edgeSetSdiffFinset G G'.val, by
      rw [Finset.mem_powerset]
      intro e he
      rw [mem_edgeSetSdiffFinset] at he ⊢
      exact ⟨edgeSet_subset_edgeSet.mpr (Finset.mem_Icc.mp G'.prop).2 he.1, he.2⟩⟩
  invFun S :=
    ⟨fromEdgeSet (G.edgeSet ∪ ↑S.val), by
      have hSK : ∀ e ∈ S.val, e ∈ K.edgeSet ∧ e ∉ G.edgeSet := fun e he => by
        have := Finset.mem_powerset.mp S.prop he
        rwa [mem_edgeSetSdiffFinset] at this
      refine Finset.mem_Icc.mpr ⟨fun a b hab => ?_, ?_⟩
      · exact (fromEdgeSet_adj _).mpr ⟨.inl hab, hab.ne⟩
      · rw [fromEdgeSet_le]
        rintro e ⟨heGS | heGS, _⟩
        · exact edgeSet_subset_edgeSet.mpr hGK heGS
        · exact (hSK e (Finset.mem_coe.mp heGS)).1⟩
  left_inv := by
    rintro ⟨G', hG'⟩
    have hGG' : G ≤ G' := (Finset.mem_Icc.mp hG').1
    apply Subtype.ext
    ext a b
    rw [fromEdgeSet_adj]
    simp only [Set.mem_union, Finset.mem_coe, mem_edgeSetSdiffFinset]
    refine ⟨fun ⟨h, _⟩ => h.elim (edgeSet_subset_edgeSet.mpr hGG' ·) (·.1),
            fun h => ⟨?_, h.ne⟩⟩
    by_cases hG : G.Adj a b
    · exact .inl hG
    · exact .inr ⟨h, hG⟩
  right_inv := by
    rintro ⟨S, hS⟩
    have hSK : ∀ e ∈ S, e ∈ K.edgeSet ∧ e ∉ G.edgeSet := fun e he => by
      have := Finset.mem_powerset.mp hS he
      rwa [mem_edgeSetSdiffFinset] at this
    apply Subtype.ext
    apply Finset.ext
    intro e
    rw [mem_edgeSetSdiffFinset, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_union]
    refine ⟨?_, fun heS => ?_⟩
    · rintro ⟨⟨h | h, _⟩, heG⟩
      · exact absurd h heG
      · exact Finset.mem_coe.mp h
    · have ⟨heK, heG⟩ := hSK e heS
      exact ⟨⟨.inr (Finset.mem_coe.mpr heS), fun hd =>
        K.not_isDiag_of_mem_edgeSet heK hd⟩, heG⟩

/-! ### Combinatorial kernel

Split into two pieces, avoiding `if-then-else` (which would require `DecidableEq` on
`SimpleGraph V`). Consumers case-split on `G = L vs G < L` via `eq_or_lt_of_le`. -/

/-- Degenerate case: the alternating sum over a singleton interval. -/
lemma sum_Icc_self_neg_one_pow_natCard_edgeSet (G : SimpleGraph V) :
    ∑ K' ∈ Finset.Icc G G, (-1 : ℤ) ^ Nat.card K'.edgeSet
      = (-1 : ℤ) ^ Nat.card G.edgeSet := by
  rw [Finset.Icc_self, Finset.sum_singleton]

/-- Strictly-larger case: the alternating sum over `Icc G L` with `G < L` is zero.
Reindexes via `iccEquivPowersetEdgeFinsetSdiff`, factors out the `(-1)^Nat.card G.edgeSet`
constant via the cardinality bridge, then collapses via `Finset.sum_powerset_neg_one_pow_card`
(which is zero on a non-empty powerset). -/
lemma sum_Icc_neg_one_pow_natCard_edgeSet_of_lt
    {G L : SimpleGraph V} (hGL : G < L) :
    ∑ K' ∈ Finset.Icc G L, (-1 : ℤ) ^ Nat.card K'.edgeSet = 0 := by
  have hGL' : G ≤ L := hGL.le
  -- Reindex the sum via `iccEquiv` and factor out `(-1)^Nat.card G.edgeSet`.
  have key : ∑ K' ∈ Finset.Icc G L, (-1 : ℤ) ^ Nat.card K'.edgeSet
      = (-1 : ℤ) ^ Nat.card G.edgeSet *
          ∑ S ∈ (edgeSetSdiffFinset G L).powerset, (-1 : ℤ) ^ #S := by
    rw [Finset.mul_sum,
        ← Finset.sum_attach (Finset.Icc G L)
          (fun K' => (-1 : ℤ) ^ Nat.card K'.edgeSet),
        ← Finset.sum_attach (edgeSetSdiffFinset G L).powerset
          (fun S => (-1 : ℤ) ^ Nat.card G.edgeSet * (-1 : ℤ) ^ #S)]
    refine Finset.sum_equiv (iccEquivPowersetEdgeFinsetSdiff hGL')
      (fun _ => by simp) ?_
    intro K' _
    have hGK' : G ≤ K'.val := (Finset.mem_Icc.mp K'.prop).1
    rw [natCard_edgeSet_eq_add_card_sdiff hGK', pow_add]
    rfl
  rw [key, Finset.sum_powerset_neg_one_pow_card, if_neg, mul_zero]
  -- Remaining goal: `edgeSetSdiffFinset G L ≠ ∅`, which would imply `L ≤ G`.
  intro hempty
  have hLsubG : L.edgeSet ⊆ G.edgeSet :=
    Set.diff_eq_empty.mp ((edgeSet_sdiff_finite G L).toFinset_eq_empty.mp hempty)
  exact absurd (le_antisymm (edgeSet_subset_edgeSet.mp hLsubG) hGL') hGL.ne'

/-! ### Main Möbius identity -/

/-- The Möbius (signed-sum) inverse to `copyCount_eq_sum_embeddingCount`. The induced copy
count is expressed as a signed sum of copy counts over supergraphs `G' ∈ Icc G ⊤`, with the
sign factored as `(-1)^Nat.card G.edgeSet * (-1)^Nat.card G'.edgeSet`.

The `Nat.card` form keeps the signature free of per-graph `Fintype` synthesis on edge sets
(and hence free of `Classical`). -/
theorem embeddingCount_eq_sum_signed_copyCount [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (H.embeddingCount G : ℤ) =
      (-1 : ℤ) ^ Nat.card G.edgeSet *
        ∑ G' ∈ Finset.Icc G ⊤,
          (-1 : ℤ) ^ Nat.card G'.edgeSet * (H.copyCount G' : ℤ) := by
  symm
  calc (-1 : ℤ) ^ Nat.card G.edgeSet *
          ∑ G' ∈ Finset.Icc G ⊤,
            (-1 : ℤ) ^ Nat.card G'.edgeSet * (H.copyCount G' : ℤ)
      -- Substitute the forward identity into each `copyCount G'`.
      = (-1 : ℤ) ^ Nat.card G.edgeSet *
          ∑ G' ∈ Finset.Icc G ⊤, ∑ L ∈ Finset.Icc G' ⊤,
            (-1 : ℤ) ^ Nat.card G'.edgeSet * (H.embeddingCount L : ℤ) := by
        simp_rw [copyCount_eq_sum_embeddingCount, Nat.cast_sum, Finset.mul_sum]
      -- Distribute `(-1)^Nat.card G.edgeSet` into the double sum.
    _ = ∑ G' ∈ Finset.Icc G ⊤, ∑ L ∈ Finset.Icc G' ⊤,
            (-1 : ℤ) ^ Nat.card G.edgeSet *
              ((-1 : ℤ) ^ Nat.card G'.edgeSet * (H.embeddingCount L : ℤ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun G' _ => ?_
        rw [Finset.mul_sum]
      -- Swap the order of summation over the triangle `G ≤ G' ≤ L ≤ ⊤`.
    _ = ∑ L ∈ Finset.Icc G ⊤, ∑ G' ∈ Finset.Icc G L,
            (-1 : ℤ) ^ Nat.card G.edgeSet *
              ((-1 : ℤ) ^ Nat.card G'.edgeSet * (H.embeddingCount L : ℤ)) := by
        rw [Finset.sum_comm' (s := Finset.Icc G (⊤ : SimpleGraph V))
            (t := fun G' => Finset.Icc G' ⊤)
            (s' := fun L => Finset.Icc G L) (t' := Finset.Icc G (⊤ : SimpleGraph V))
            (h := fun G' L => by
              simp only [Finset.mem_Icc]
              exact ⟨fun ⟨⟨hGG', _⟩, hG'L, _⟩ => ⟨⟨hGG', hG'L⟩, hGG'.trans hG'L, le_top⟩,
                     fun ⟨⟨hGG', hG'L⟩, _⟩ => ⟨⟨hGG', le_top⟩, hG'L, le_top⟩⟩)]
      -- Factor `H.embeddingCount L` out of each inner sum.
    _ = ∑ L ∈ Finset.Icc G ⊤, (H.embeddingCount L : ℤ) *
          ((-1 : ℤ) ^ Nat.card G.edgeSet *
            ∑ G' ∈ Finset.Icc G L, (-1 : ℤ) ^ Nat.card G'.edgeSet) := by
        refine Finset.sum_congr rfl fun L _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun G' _ => ?_
        ring
      -- Isolate the `L = G` term: all others vanish via the strict-`G < L` kernel.
    _ = (H.embeddingCount G : ℤ) := by
        rw [Finset.sum_eq_single G]
        · rw [sum_Icc_self_neg_one_pow_natCard_edgeSet, ← pow_add,
              Even.neg_one_pow ⟨_, rfl⟩, mul_one]
        · intro L hL hLG
          rcases eq_or_lt_of_le (Finset.mem_Icc.mp hL).1 with rfl | hGL
          · exact absurd rfl hLG
          · rw [sum_Icc_neg_one_pow_natCard_edgeSet_of_lt hGL, mul_zero, mul_zero]
        · intro hG
          exact absurd (Finset.mem_Icc.mpr ⟨le_refl _, le_top⟩) hG

end Mobius

end SimpleGraph
