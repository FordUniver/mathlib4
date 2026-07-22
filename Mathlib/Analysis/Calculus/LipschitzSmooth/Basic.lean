/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.QuadraticRemainder

/-!
# Lipschitz smoothness

A function `f : E → F` between normed vector spaces over a nontrivially normed
field `𝕜` is **`K`-smooth** if the first-order Taylor remainder is bounded quadratically:

`‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ (K / 2) * (dist x y) ^ 2`

for all `x, y`. The predicate uses `lineDeriv` so as not to presuppose Fréchet
differentiability. It does, however, force the line derivative to be linear in its
direction. Equivalent characterisations in `fderiv`, 1D `deriv`, and Hilbert-space
gradient form live in the sibling files in this directory.

This two-sided (norm) form is orientation-agnostic (closed under `f ↦ -f`) — matching,
when `𝕜 = ℝ` and `f` is real-valued, the textbook notion of L-smoothness (Lipschitz
gradient, the class `C^{1,1}`). The one-sided descent bounds require an order
on the codomain and are stated for real-valued `f` in a dedicated section.
-/

public section

section NormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A function `f : E → F` between normed vector spaces over `𝕜` is `K`-smooth
if the first-order Taylor remainder is bounded quadratically:
`‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ (K / 2) * (dist x y) ^ 2` for all `x, y`.

The predicate is two-sided (norm), so closed under `f ↦ -f` and matching, when `𝕜 = ℝ`
and `f` is real-valued, the textbook L-smoothness / `C^{1,1}` class. The `lineDeriv`
form is the weakest possible underlying derivative form — the predicate implies
line-differentiability everywhere (`LipschitzSmoothWith.hasLineDerivAt`) and makes
the line derivative linear in its direction (`LipschitzSmoothWith.lineDerivLinearMap`).

Equivalent characterisations in `fderiv`, `gradient`, and `deriv` form are
provided in the sibling files, predicated on `Differentiable` where useful.
The one-sided descent bounds, which require an order on the codomain, are
stated for real-valued `f`. -/
def LipschitzSmoothWith (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (K : NNReal) (f : E → F) :=
  HasQuadraticLineRemainderWith 𝕜 (K / 2) f

theorem lipschitzSmoothWith_iff_lineDeriv {K : NNReal} {f : E → F} :
    LipschitzSmoothWith 𝕜 K f ↔
      ∀ x y : E, ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2 :=
  Iff.rfl

end NormedField

namespace LipschitzSmoothWith

section NormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F}

/-- The quadratic line-remainder condition underlying `K`-smoothness. -/
theorem hasQuadraticLineRemainderWith (h : LipschitzSmoothWith 𝕜 K f) :
    HasQuadraticLineRemainderWith 𝕜 (K / 2) f :=
  h

/-- The two-sided quadratic bound on the first-order Taylor remainder, restated
from the definition for dot notation. -/
theorem lineDeriv_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E) :
    ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2 :=
  h.hasQuadraticLineRemainderWith x y

/-- Two-sided bound on the variation of the line derivative along `y - x`. -/
theorem lineDeriv_apply_sub_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E) :
    ‖lineDeriv 𝕜 f y (y - x) - lineDeriv 𝕜 f x (y - x)‖ ≤ K * (dist x y) ^ 2 := by
  have hyx := h.lineDeriv_norm_le y x
  rw [← neg_sub y x, lineDeriv_neg, sub_neg_eq_add, dist_comm] at hyx
  have key := (norm_add_le _ _).trans (add_le_add hyx (h.lineDeriv_norm_le x y))
  rw [show f x - f y + lineDeriv 𝕜 f y (y - x) + (f y - f x - lineDeriv 𝕜 f x (y - x))
      = lineDeriv 𝕜 f y (y - x) - lineDeriv 𝕜 f x (y - x) from by abel] at key
  linarith

/-- The line derivative of a `K`-smooth function at `x`, bundled as a linear map in its
direction. -/
@[expose]
noncomputable def lineDerivLinearMap (h : LipschitzSmoothWith 𝕜 K f) (x : E) : E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ <| h.hasQuadraticLineRemainderWith.isLinearMap_lineDeriv x

@[simp]
theorem lineDerivLinearMap_apply (h : LipschitzSmoothWith 𝕜 K f) (x v : E) :
    h.lineDerivLinearMap x v = lineDeriv 𝕜 f x v :=
  rfl

/-- The line derivative of a `K`-smooth function is additive in its direction. -/
theorem lineDeriv_add (h : LipschitzSmoothWith 𝕜 K f) (x u v : E) :
    lineDeriv 𝕜 f x (u + v) = lineDeriv 𝕜 f x u + lineDeriv 𝕜 f x v :=
  (h.lineDerivLinearMap x).map_add u v

/-- `K`-smoothness implies line-differentiability: the actual line derivative
exists at every `x, v` and equals `lineDeriv 𝕜 f x v`. The predicate bound
`‖f (x + tv) - f x - t • L‖ ≤ K/2 · ‖t‖² ‖v‖²` (via `lineDeriv_smul` to factor `t`)
is `o(t)`. -/
theorem hasLineDerivAt (h : LipschitzSmoothWith 𝕜 K f) (x v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  h.hasQuadraticLineRemainderWith.hasLineDerivAt x v

/-- A `K`-smooth function is line-differentiable everywhere. -/
theorem lineDifferentiableAt (h : LipschitzSmoothWith 𝕜 K f) (x v : E) :
    LineDifferentiableAt 𝕜 f x v :=
  (h.hasLineDerivAt x v).lineDifferentiableAt

end NormedField

/-! ### Real-valued functions

The one-sided (order-based) bounds require an order on the codomain, so they are
stated for real-valued `f`. The norm and the absolute value agree on `ℝ`
(`Real.norm_eq_abs`), so the two-sided bounds above apply verbatim. -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : NNReal} {f : E → ℝ}

/-- The quadratic upper bound on `f y`, traditionally called the *descent lemma*. -/
theorem lineDeriv_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) + K / 2 * (dist x y) ^ 2 := by
  linarith [(abs_le.mp (h.lineDeriv_norm_le x y)).2]

/-- The quadratic lower bound on `f y`, sometimes referred to as the *ascent lemma*, obtained by
applying the descent lemma to `-f`. -/
theorem lineDeriv_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    f x + lineDeriv ℝ f x (y - x) - K / 2 * (dist x y) ^ 2 ≤ f y := by
  linarith [(abs_le.mp (h.lineDeriv_norm_le x y)).1]

/-- One-sided bound on the variation of the line derivative along `y - x`. -/
theorem lineDeriv_apply_sub_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ K * (dist x y) ^ 2 :=
  le_of_abs_le (h.lineDeriv_apply_sub_norm_le x y)

/-- The one-sided variation bound in functional form: the difference of
line-derivative maps applied to `y - x`. -/
theorem lineDeriv_sub_apply_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    (lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x) ≤ K * (dist x y) ^ 2 :=
  Pi.sub_apply (lineDeriv ℝ f _) _ _ ▸ h.lineDeriv_apply_sub_le x y

end Real

end LipschitzSmoothWith
