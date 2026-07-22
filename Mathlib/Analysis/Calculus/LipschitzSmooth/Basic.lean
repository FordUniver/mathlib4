/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Lipschitz smoothness

A differentiable function `f : E → F` between normed vector spaces over a nontrivially normed
field `𝕜` is **`K`-smooth** if its first-order Taylor remainder is bounded quadratically:

`‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ (K / 2) * dist x y ^ 2`.

We define setwise, global, and neighborhood-wise versions. The setwise predicate uses ambient
Fréchet derivatives at the points of the set; it is not a within-set differentiability notion.
The corresponding technical predicates phrased using `lineDeriv`, which do not assume
differentiability, and their connection to these predicates are developed in
`Mathlib.Analysis.Calculus.LipschitzSmooth.LineDeriv`.
-/

public section

open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜)

/-- `LipschitzSmoothOnWith 𝕜 K f s` means that `f` is Fréchet differentiable at every point of
`s` and that its first-order Taylor remainder is bounded by `K / 2 * dist x y ^ 2` for all
`x`, `y` in `s`.

The derivatives are ambient Fréchet derivatives, not derivatives within `s`. -/
def LipschitzSmoothOnWith (K : NNReal) (f : E → F) (s : Set E) : Prop :=
  (∀ x ∈ s, DifferentiableAt 𝕜 f x) ∧
    ∀ x ∈ s, ∀ y ∈ s,
      ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2

/-- `LipschitzSmoothWith 𝕜 K f` means that `f` is globally Fréchet differentiable and that its
first-order Taylor remainder is bounded by `K / 2 * dist x y ^ 2` for all `x`, `y`. -/
def LipschitzSmoothWith (K : NNReal) (f : E → F) : Prop :=
  LipschitzSmoothOnWith 𝕜 K f Set.univ

/-- `LipschitzSmoothWithAt 𝕜 K f x` means that `f` is `K`-smooth on some neighborhood of `x`.

This is a neighborhood-wise condition, not merely a remainder bound whose first point is `x`. -/
def LipschitzSmoothWithAt (K : NNReal) (f : E → F) (x : E) : Prop :=
  ∃ s ∈ 𝓝 x, LipschitzSmoothOnWith 𝕜 K f s

theorem lipschitzSmoothOnWith_iff_fderiv {K : NNReal} {f : E → F} {s : Set E} :
    LipschitzSmoothOnWith 𝕜 K f s ↔
      (∀ x ∈ s, DifferentiableAt 𝕜 f x) ∧
        ∀ x ∈ s, ∀ y ∈ s,
          ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  Iff.rfl

theorem lipschitzSmoothWith_iff_fderiv {K : NNReal} {f : E → F} :
    LipschitzSmoothWith 𝕜 K f ↔
      Differentiable 𝕜 f ∧
        ∀ x y, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 := by
  rw [LipschitzSmoothWith, lipschitzSmoothOnWith_iff_fderiv]
  simp only [Set.mem_univ, forall_const]
  constructor <;> intro h <;> exact ⟨fun x ↦ h.1 x, h.2⟩

theorem lipschitzSmoothWithAt_iff_fderiv {K : NNReal} {f : E → F} {x : E} :
    LipschitzSmoothWithAt 𝕜 K f x ↔
      ∃ s ∈ 𝓝 x, (∀ y ∈ s, DifferentiableAt 𝕜 f y) ∧
        ∀ y ∈ s, ∀ z ∈ s,
          ‖f z - f y - fderiv 𝕜 f y (z - y)‖ ≤ K / 2 * dist y z ^ 2 := by
  rw [LipschitzSmoothWithAt]
  refine exists_congr fun s ↦ and_congr_right fun _ ↦ ?_
  exact lipschitzSmoothOnWith_iff_fderiv 𝕜

variable {𝕜}

namespace LipschitzSmoothOnWith

variable {K : NNReal} {f : E → F} {s t : Set E}

/-- A function smooth on `s` is differentiable at every point of `s`. -/
theorem differentiableAt (h : LipschitzSmoothOnWith 𝕜 K f s) {x : E} (hx : x ∈ s) :
    DifferentiableAt 𝕜 f x :=
  (lipschitzSmoothOnWith_iff_fderiv 𝕜 |>.mp h).1 x hx

/-- The defining quadratic bound on the first-order Taylor remainder. -/
theorem fderiv_norm_le (h : LipschitzSmoothOnWith 𝕜 K f s)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  (lipschitzSmoothOnWith_iff_fderiv 𝕜 |>.mp h).2 x hx y hy

/-- Restricting a smoothness bound to a smaller set. -/
theorem mono (h : LipschitzSmoothOnWith 𝕜 K f s) (hts : t ⊆ s) :
    LipschitzSmoothOnWith 𝕜 K f t :=
  lipschitzSmoothOnWith_iff_fderiv 𝕜 |>.mpr
    ⟨fun _ hx ↦ h.differentiableAt (hts hx), fun _ hx _ hy ↦ h.fderiv_norm_le (hts hx) (hts hy)⟩

end LipschitzSmoothOnWith

namespace LipschitzSmoothWith

variable {K : NNReal} {f : E → F}

/-- A globally smooth function is Fréchet differentiable. -/
theorem differentiable (h : LipschitzSmoothWith 𝕜 K f) : Differentiable 𝕜 f :=
  (lipschitzSmoothWith_iff_fderiv 𝕜 |>.mp h).1

/-- The defining quadratic bound on the first-order Taylor remainder. -/
theorem fderiv_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E) :
    ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  (lipschitzSmoothWith_iff_fderiv 𝕜 |>.mp h).2 x y

/-- A globally smooth function is smooth on every set. -/
theorem lipschitzSmoothOnWith (h : LipschitzSmoothWith 𝕜 K f) (s : Set E) :
    LipschitzSmoothOnWith 𝕜 K f s := by
  rw [LipschitzSmoothWith] at h
  exact h.mono (Set.subset_univ s)

/-- A globally smooth function is smooth at every point. -/
theorem lipschitzSmoothWithAt (h : LipschitzSmoothWith 𝕜 K f) (x : E) :
    LipschitzSmoothWithAt 𝕜 K f x :=
  ⟨Set.univ, Filter.univ_mem, h.lipschitzSmoothOnWith Set.univ⟩

end LipschitzSmoothWith

namespace LipschitzSmoothWithAt

variable {K : NNReal} {f : E → F} {x : E}

/-- Extract a neighborhood on which a function smooth at `x` is smooth. -/
theorem exists_lipschitzSmoothOnWith (h : LipschitzSmoothWithAt 𝕜 K f x) :
    ∃ s ∈ 𝓝 x, LipschitzSmoothOnWith 𝕜 K f s :=
  h

/-- A function smooth in a neighborhood of `x` is differentiable at `x`. -/
theorem differentiableAt (h : LipschitzSmoothWithAt 𝕜 K f x) : DifferentiableAt 𝕜 f x := by
  obtain ⟨s, hs, hfs⟩ := h.exists_lipschitzSmoothOnWith
  exact hfs.differentiableAt (mem_of_mem_nhds hs)

end LipschitzSmoothWithAt
