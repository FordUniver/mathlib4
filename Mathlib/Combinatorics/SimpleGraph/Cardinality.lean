/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card

/-!
# Cardinality of a simple graph

This file introduces the two primary cardinality concepts of a simple graph:

* `SimpleGraph.order` — the number of vertices, `Nat.card V`. Defined for any vertex type,
  with the usual junk-value convention (`0` if `V` is infinite).
* `SimpleGraph.size` — the number of edges, `G.edgeSet.ncard`. Defined for any graph,
  with the usual junk-value convention (`0` if the edge set is infinite).

Both definitions are stated in terms of `Nat.card` / `Set.ncard` rather than `Fintype.card`
/ `#G.edgeFinset`. They do not require any `Fintype` instances. Bridge lemmas connect them
to the `Fintype`-flavoured representation when those instances are in scope.

The definitions are `@[expose] noncomputable def`, not `abbrev`: the body is cross-module
visible (so the `rfl` bridges `order_eq_natCard` / `size_eq_ncard` typecheck downstream),
but the elaborator treats `G.size` / `G.order` as opaque concepts. `simp`, `rw`, and
typeclass synthesis do not unfold them automatically — clients use the named bridges to
descend to the underlying representation when needed.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The **order** of a graph: the number of vertices.

This is `Nat.card V`, so it equals `0` when `V` is infinite (junk-value convention). -/
@[expose] noncomputable def order (_G : SimpleGraph V) : ℕ := Nat.card V

/-- The **size** of a graph: the number of edges.

This is `G.edgeSet.ncard`, so it equals `0` when `G.edgeSet` is infinite. -/
@[expose] noncomputable def size : ℕ := G.edgeSet.ncard

theorem order_eq_natCard : G.order = Nat.card V := rfl

theorem size_eq_ncard : G.size = G.edgeSet.ncard := rfl

theorem order_eq_fintype_card [Fintype V] : G.order = Fintype.card V :=
  Nat.card_eq_fintype_card

theorem size_eq_card_edgeFinset [Fintype G.edgeSet] : G.size = #G.edgeFinset := by
  rw [size_eq_ncard, edgeFinset, Set.ncard_eq_toFinset_card']

end SimpleGraph
