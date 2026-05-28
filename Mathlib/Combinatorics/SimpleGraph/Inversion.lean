/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.InducedCopy
public import Mathlib.Data.Nat.Choose.Sum

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

attribute [local instance 0] Classical.decRel

/-- Order-isomorphism between the closed interval `Finset.Icc G K` of graphs and the
powerset of the edge difference `K.edgeFinset \ G.edgeFinset`, valid when `G ≤ K`.

The forward map sends a graph `G'` with `G ≤ G' ≤ K` to its "extra edges over `G`",
namely `G'.edgeFinset \ G.edgeFinset`. The inverse sends a subset `S` of "missing edges
of `G` inside `K`" to the graph whose edge set is `G.edgeFinset ∪ S`, constructed via
`fromEdgeSet`. -/
noncomputable def iccEquivPowersetEdgeFinsetSdiff [Fintype V] [DecidableEq V]
    [DecidableLE (SimpleGraph V)] {G K : SimpleGraph V} (hGK : G ≤ K) :
    ↥(Finset.Icc G K) ≃ ↥(K.edgeFinset \ G.edgeFinset).powerset where
  toFun G' :=
    ⟨G'.val.edgeFinset \ G.edgeFinset, by
      simp only [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff (edgeFinset_mono (Finset.mem_Icc.mp G'.prop).2)
        Finset.Subset.rfl⟩
  invFun S :=
    ⟨fromEdgeSet ((G.edgeFinset : Set (Sym2 V)) ∪ S.val), by
      have hSK : S.val ⊆ K.edgeFinset \ G.edgeFinset := Finset.mem_powerset.mp S.prop
      refine Finset.mem_Icc.mpr ⟨fun a b hab => ?_, ?_⟩
      · exact (fromEdgeSet_adj _).mpr ⟨.inl (mem_coe.mpr <| mem_edgeFinset.mpr hab), hab.ne⟩
      · rw [fromEdgeSet_le]
        rintro e ⟨heGS | heGS, _⟩
        · exact edgeSet_subset_edgeSet.mpr hGK (mem_edgeFinset.mp heGS)
        · exact mem_edgeFinset.mp (Finset.mem_sdiff.mp (hSK heGS)).1⟩
  left_inv := by
    rintro ⟨G', hG'⟩
    have hGG' : G ≤ G' := (Finset.mem_Icc.mp hG').1
    apply Subtype.ext
    ext a b
    simp only [fromEdgeSet_adj, Set.mem_union, mem_coe, mem_edgeFinset, Finset.coe_sdiff,
      Set.mem_diff]
    refine ⟨fun ⟨h, _⟩ => h.elim (hGG' ·) (·.1), fun h => ⟨?_, h.ne⟩⟩
    by_cases hG : G.Adj a b
    · exact .inl hG
    · exact .inr ⟨h, hG⟩
  right_inv := by
    rintro ⟨S, hS⟩
    have hSK : S ⊆ K.edgeFinset \ G.edgeFinset := Finset.mem_powerset.mp hS
    apply Subtype.ext
    ext e
    simp only [Finset.mem_sdiff, mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_diff,
      Set.mem_union, mem_coe]
    refine ⟨?_, fun heS => ?_⟩
    · rintro ⟨⟨h | h, _⟩, heG⟩
      · exact absurd h heG
      · exact h
    · have heKsd := Finset.mem_sdiff.mp (hSK heS)
      refine ⟨⟨.inr heS, fun hd =>
        K.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp heKsd.1) hd⟩, ?_⟩
      exact fun heG => heKsd.2 (mem_edgeFinset.mpr heG)

/-- The combinatorial kernel of Möbius inversion at the graph level: the alternating sum of
`(-1) ^ #(K' \ G)` over `K'` in a closed interval `[G, L]` collapses to `1` when `L = G` and
`0` otherwise. Reindexes via `iccEquivPowersetEdgeFinsetSdiff` to
`Finset.sum_powerset_neg_one_pow_card`. -/
private theorem sum_Icc_neg_one_pow_card_edgeFinset_sdiff_eq_ite
    [Fintype V] [DecidableEq V] [DecidableLE (SimpleGraph V)]
    {G L : SimpleGraph V} (hGL : G ≤ L) :
    ∑ K' ∈ Finset.Icc G L, (-1 : ℤ) ^ #(K'.edgeFinset \ G.edgeFinset)
      = if L = G then 1 else 0 := by
  have key : ∑ K' ∈ Finset.Icc G L, (-1 : ℤ) ^ #(K'.edgeFinset \ G.edgeFinset)
      = ∑ S ∈ (L.edgeFinset \ G.edgeFinset).powerset, (-1 : ℤ) ^ #S := by
    rw [← Finset.sum_attach (Finset.Icc G L)
          (fun K' => (-1 : ℤ) ^ #(K'.edgeFinset \ G.edgeFinset)),
        ← Finset.sum_attach (L.edgeFinset \ G.edgeFinset).powerset
          (fun S => (-1 : ℤ) ^ #S)]
    exact Finset.sum_equiv (iccEquivPowersetEdgeFinsetSdiff hGL)
      (fun _ => by simp) (fun _ _ => rfl)
  rw [key, Finset.sum_powerset_neg_one_pow_card]
  obtain rfl | hLG := eq_or_ne L G
  · simp
  · rw [if_neg, if_neg hLG]
    intro hempty
    apply hLG
    have hsub : L ≤ G := by
      simpa [Finset.sdiff_eq_empty_iff_subset, edgeFinset_subset_edgeFinset] using hempty
    exact le_antisymm hsub hGL

/-- Auxiliary form of the Möbius inverse with sign `(-1) ^ #(G'.edgeFinset \ G.edgeFinset)`.
The user-facing version `embeddingCount_eq_sum_signed_copyCount` factors the sign through
`Nat.card G.edgeSet * Nat.card G'.edgeSet`, eliminating per-graph `Fintype` hypotheses from
the signature. -/
private theorem embeddingCount_eq_sum_signed_copyCount_aux [Fintype V] [DecidableEq V]
    [DecidableLE (SimpleGraph V)] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) :
    (H.embeddingCount G : ℤ) =
      ∑ G' ∈ Finset.Icc G ⊤,
        (-1 : ℤ) ^ #(G'.edgeFinset \ G.edgeFinset) * (H.copyCount G' : ℤ) := by
  symm
  calc ∑ G' ∈ Finset.Icc G ⊤,
          (-1 : ℤ) ^ #(G'.edgeFinset \ G.edgeFinset) * (H.copyCount G' : ℤ)
      -- Substitute the forward identity into each summand.
      = ∑ G' ∈ Finset.Icc G ⊤, ∑ L ∈ Finset.Icc G' ⊤,
          (-1 : ℤ) ^ #(G'.edgeFinset \ G.edgeFinset) * (H.embeddingCount L : ℤ) := by
        simp_rw [copyCount_eq_sum_embeddingCount, Nat.cast_sum, Finset.mul_sum]
      -- Swap the order of summation over the triangle `G ≤ G' ≤ L ≤ ⊤`.
    _ = ∑ L ∈ Finset.Icc G ⊤, ∑ G' ∈ Finset.Icc G L,
          (-1 : ℤ) ^ #(G'.edgeFinset \ G.edgeFinset) * (H.embeddingCount L : ℤ) := by
        rw [Finset.sum_comm' (s := Finset.Icc G (⊤ : SimpleGraph V))
            (t := fun G' => Finset.Icc G' ⊤)
            (s' := fun L => Finset.Icc G L) (t' := Finset.Icc G (⊤ : SimpleGraph V))
            (h := fun G' L => by
              simp only [Finset.mem_Icc]
              exact ⟨fun ⟨⟨hGG', _⟩, hG'L, _⟩ => ⟨⟨hGG', hG'L⟩, hGG'.trans hG'L, le_top⟩,
                     fun ⟨⟨hGG', hG'L⟩, _⟩ => ⟨⟨hGG', le_top⟩, hG'L, le_top⟩⟩)]
      -- Factor `H.embeddingCount L` out of the inner sum.
    _ = ∑ L ∈ Finset.Icc G ⊤, (H.embeddingCount L : ℤ) *
          ∑ G' ∈ Finset.Icc G L, (-1 : ℤ) ^ #(G'.edgeFinset \ G.edgeFinset) := by
        simp_rw [mul_comm ((-1 : ℤ) ^ _) ((H.embeddingCount _ : ℤ)), ← Finset.mul_sum]
      -- Inner sum collapses to `δ_{L = G}` by the kernel lemma.
    _ = ∑ L ∈ Finset.Icc G ⊤, (H.embeddingCount L : ℤ) * (if L = G then 1 else 0) := by
        refine Finset.sum_congr rfl fun L hL => ?_
        rw [sum_Icc_neg_one_pow_card_edgeFinset_sdiff_eq_ite (Finset.mem_Icc.mp hL).1]
      -- Only the `L = G` term survives.
    _ = (H.embeddingCount G : ℤ) := by
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' (Finset.Icc G ⊤) G fun L => (H.embeddingCount L : ℤ),
            if_pos (Finset.mem_Icc.mpr ⟨le_refl _, le_top⟩)]

/-- Sign factorization: under `G ≤ G'`, the parity of `#(G'.edgeFinset \ G.edgeFinset)`
equals the sum of the parities of `Nat.card G.edgeSet` and `Nat.card G'.edgeSet`. -/
private lemma neg_one_pow_card_edgeFinset_sdiff [Fintype V] [DecidableEq V]
    {G G' : SimpleGraph V} (hGG' : G ≤ G') :
    (-1 : ℤ) ^ #(G'.edgeFinset \ G.edgeFinset)
      = (-1 : ℤ) ^ Nat.card G.edgeSet * (-1 : ℤ) ^ Nat.card G'.edgeSet := by
  rw [show Nat.card G.edgeSet = #G.edgeFinset from
        Nat.card_eq_fintype_card.trans G.card_edgeSet,
      show Nat.card G'.edgeSet = #G'.edgeFinset from
        Nat.card_eq_fintype_card.trans G'.card_edgeSet,
      show #G'.edgeFinset = #G.edgeFinset + #(G'.edgeFinset \ G.edgeFinset) by
        have := Finset.card_sdiff_add_card_eq_card (edgeFinset_mono hGG'); omega,
      pow_add, ← mul_assoc, ← pow_add,
      show (-1 : ℤ) ^ (#G.edgeFinset + #G.edgeFinset) = 1 from Even.neg_one_pow ⟨_, rfl⟩,
      one_mul]

/-- The Möbius (signed-sum) inverse to `copyCount_eq_sum_embeddingCount`. The induced copy
count is expressed as a signed sum of copy counts over supergraphs `G' ∈ Icc G ⊤`, with the
sign factored as `(-1) ^ Nat.card G.edgeSet * (-1) ^ Nat.card G'.edgeSet` — equivalently
`(-1) ^ #(G'.edgeFinset \ G.edgeFinset)`, but stated via `Nat.card` so no per-graph
`Fintype` hypothesis on the edge sets appears in the signature. -/
theorem embeddingCount_eq_sum_signed_copyCount [Fintype V] [DecidableEq V]
    [DecidableLE (SimpleGraph V)] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) :
    (H.embeddingCount G : ℤ) =
      (-1 : ℤ) ^ Nat.card G.edgeSet *
        ∑ G' ∈ Finset.Icc G ⊤,
          (-1 : ℤ) ^ Nat.card G'.edgeSet * (H.copyCount G' : ℤ) := by
  rw [embeddingCount_eq_sum_signed_copyCount_aux, Finset.mul_sum]
  refine Finset.sum_congr rfl fun G' hG' => ?_
  rw [neg_one_pow_card_edgeFinset_sdiff (Finset.mem_Icc.mp hG').1, mul_assoc]

end Mobius

end SimpleGraph
