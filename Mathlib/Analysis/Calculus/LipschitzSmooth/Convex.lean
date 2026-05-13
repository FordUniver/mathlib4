/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.Gradient
public import Mathlib.Analysis.Convex.Gradient

/-!
# Convex Lipschitz-smooth functions and the Baillon-Haddad theorem

For a differentiable convex function on a Hilbert space, the following are equivalent:

* `LipschitzSmoothWith K f` — the quadratic descent inequality (`K`-smoothness)
* `LipschitzWith K (fderiv ℝ f)` — the Fréchet derivative is `K`-Lipschitz
* `LipschitzWith K (∇ f)` — the gradient is `K`-Lipschitz
* `CocoerciveWith K f` — `K`-cocoercivity of the gradient

The non-convex direction (`LipschitzWith K (fderiv ℝ f) → LipschitzSmoothWith K f`)
was established as the descent lemma in
`Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv`. The non-convex direction
`CocoerciveWith K f → LipschitzWith K (∇ f)` was established in
`Mathlib.Analysis.Calculus.LipschitzSmooth.Gradient`. This file establishes the
converse implications under `ConvexOn ℝ Set.univ f`, all of which follow from a
single atomic statement, the Baillon-Haddad theorem
(`ConvexOn.cocoerciveWith_of_lipschitzSmoothWith`).

## Main results

* `ConvexOn.cocoerciveWith_of_lipschitzSmoothWith` — **Baillon-Haddad theorem**:
  a differentiable convex `K`-smooth function on a Hilbert space is `K`-cocoercive.
* `ConvexOn.lipschitzSmoothWith_iff_cocoerciveWith`,
  `ConvexOn.lipschitzSmoothWith_iff_lipschitzWith_gradient`,
  `ConvexOn.lipschitzSmoothWith_iff_lipschitzWith_fderiv`,
  `ConvexOn.cocoerciveWith_iff_lipschitzWith_gradient` — the four pairwise equivalences
  under `ConvexOn ℝ Set.univ f`.
-/

public section

namespace ConvexOn

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open InnerProductSpace
open scoped Gradient RealInnerProductSpace

/-- Core Baillon-Haddad estimate (`K > 0` case): for convex differentiable `K`-smooth `f`,
`‖∇f y - ∇f x‖² ≤ 2K · (f y - f x - ⟪∇f x, y - x⟫)`. Direct proof via the descent inequality
applied at the auxiliary point `u := y - (1/K) · (∇f y - ∇f x)` combined with the
first-order convexity inequality at `(x, u)`. -/
private theorem norm_gradient_sub_sq_le_aux (hc : ConvexOn ℝ Set.univ f)
    (hf : Differentiable ℝ f) (hs : LipschitzSmoothWith K f) (hKp : 0 < (K : ℝ)) (x y : F) :
    ‖∇ f y - ∇ f x‖ ^ 2 ≤ 2 * K * (f y - f x - ⟪∇ f x, y - x⟫) := by
  set g := ∇ f y - ∇ f x with hg
  set u := y - ((1 : ℝ) / K) • g with hu
  have huy : u - y = -((1 / (K : ℝ)) • g) := by rw [hu]; module
  have hux : u - x = (y - x) - ((1 / (K : ℝ)) • g) := by rw [hu]; module
  have h_foc : f x + ⟪∇ f x, u - x⟫ ≤ f u :=
    hc.add_inner_gradient_le (Set.mem_univ x) (Set.mem_univ u) (hf x)
  have h_desc : f u ≤ f y + ⟪∇ f y, u - y⟫ + (K : ℝ) / 2 * ‖u - y‖ ^ 2 :=
    hs.inner_gradient_descent_le hf y u
  -- Simplify the inner products and norm appearing in h_foc and h_desc
  have huy_inner : ⟪∇ f y, u - y⟫_ℝ = -(1 / (K : ℝ) * ⟪∇ f y, g⟫_ℝ) := by
    rw [huy, inner_neg_right, inner_smul_right]
  have hux_inner : ⟪∇ f x, u - x⟫_ℝ = ⟪∇ f x, y - x⟫_ℝ - 1 / (K : ℝ) * ⟪∇ f x, g⟫_ℝ := by
    rw [hux, inner_sub_right, inner_smul_right]
  have huy_norm : (K : ℝ) / 2 * ‖u - y‖ ^ 2 = ‖g‖ ^ 2 / (2 * K) := by
    rw [huy, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / K)]
    field_simp
  rw [hux_inner] at h_foc
  rw [huy_inner, huy_norm] at h_desc
  -- Inner-product identity: (1/K) (⟪∇f y, g⟫ - ⟪∇f x, g⟫) = ‖g‖² / K
  have h_inner_diff :
      1 / (K : ℝ) * ⟪∇ f y, g⟫_ℝ - 1 / (K : ℝ) * ⟪∇ f x, g⟫_ℝ = ‖g‖ ^ 2 / K := by
    rw [← mul_sub, ← inner_sub_left, ← hg, real_inner_self_eq_norm_sq]
    ring
  -- ‖g‖²/K = 2 · ‖g‖²/(2K)
  have h_div_rel : ‖g‖ ^ 2 / (K : ℝ) = 2 * (‖g‖ ^ 2 / (2 * K)) := by field_simp
  -- Combine: ‖g‖²/(2K) ≤ f y - f x - ⟪∇f x, y - x⟫
  have h_half : ‖g‖ ^ 2 / (2 * (K : ℝ)) ≤ f y - f x - ⟪∇ f x, y - x⟫_ℝ := by
    linarith [h_foc, h_desc, h_inner_diff, h_div_rel]
  -- Multiply by 2K
  have h_norm_eq : ‖g‖ ^ 2 = 2 * (K : ℝ) * (‖g‖ ^ 2 / (2 * K)) := by field_simp
  rw [h_norm_eq]
  exact mul_le_mul_of_nonneg_left h_half (by positivity)

/-- **Baillon-Haddad theorem.** A differentiable convex `K`-smooth function on a Hilbert
space is `K`-cocoercive.

The standard proof: define `φₓ(z) := f(z) - ⟨∇f(x), z⟩`, which is convex and `K`-smooth
with minimum at `x` (since `∇φₓ(x) = 0`). Apply the descent inequality of `φₓ` at `y`
stepping by `-∇φₓ(y) / K`; using `φₓ(x) = min φₓ` yields
`‖∇f(y) - ∇f(x)‖² ≤ 2K (f(y) - f(x) - ⟨∇f(x), y - x⟩)`. Sum with the symmetric bound from
`φᵧ`, and the linear terms in `f` cancel to give the cocoercive inequality. -/

theorem cocoerciveWith_of_lipschitzSmoothWith
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (hs : LipschitzSmoothWith K f) : CocoerciveWith K f := by
  intro x y
  by_cases hK : (K : ℝ) = 0
  · -- K = 0: gradient is forced constant; both sides become 0.
    sorry
  · have hKp : 0 < (K : ℝ) := lt_of_le_of_ne K.coe_nonneg (Ne.symm hK)
    have h1 := norm_gradient_sub_sq_le_aux hc hf hs hKp x y
    have h2 := norm_gradient_sub_sq_le_aux hc hf hs hKp y x
    have h_norm_sym : ‖∇ f x - ∇ f y‖ ^ 2 = ‖∇ f y - ∇ f x‖ ^ 2 := by
      rw [← neg_sub, norm_neg]
    rw [h_norm_sym] at h2
    -- h1: ‖∇f y - ∇f x‖² ≤ 2K (f y - f x - ⟪∇f x, y - x⟫)
    -- h2: ‖∇f y - ∇f x‖² ≤ 2K (f x - f y - ⟪∇f y, x - y⟫)
    -- Sum: 2 ‖∇f y - ∇f x‖² ≤ 2K (- ⟪∇f x, y - x⟫ - ⟪∇f y, x - y⟫)
    --                       = 2K ⟪∇f y - ∇f x, y - x⟫
    -- So ‖∇f y - ∇f x‖² ≤ K ⟪∇f y - ∇f x, y - x⟫
    have h_inner_split : ⟪∇ f x, y - x⟫_ℝ + ⟪∇ f y, x - y⟫_ℝ
        = -⟪∇ f y - ∇ f x, y - x⟫_ℝ := by
      rw [show (x - y : F) = -(y - x) from (neg_sub y x).symm, inner_neg_right,
        inner_sub_left]
      ring
    nlinarith [h1, h2, h_inner_split, K.coe_nonneg]

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to `K`-cocoercivity. The forward direction is the Baillon-Haddad theorem; the backward
direction goes via `K`-Lipschitz gradient and the descent lemma, no convexity needed. -/
theorem lipschitzSmoothWith_iff_cocoerciveWith
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ CocoerciveWith K f :=
  ⟨hc.cocoerciveWith_of_lipschitzSmoothWith hf,
    fun h => hf.lipschitzSmoothWith_of_lipschitzWith_gradient h.lipschitzWith_gradient⟩

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to `K`-Lipschitz gradient. Forward: K-smooth → cocoercive (Baillon-Haddad) → Lipschitz
gradient. Backward: the descent lemma in Hilbert form. -/
theorem lipschitzSmoothWith_iff_lipschitzWith_gradient
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ LipschitzWith K (∇ f) :=
  ⟨fun hs => (hc.cocoerciveWith_of_lipschitzSmoothWith hf hs).lipschitzWith_gradient,
    hf.lipschitzSmoothWith_of_lipschitzWith_gradient⟩

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to a `K`-Lipschitz Fréchet derivative. -/
theorem lipschitzSmoothWith_iff_lipschitzWith_fderiv
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ LipschitzWith K (fderiv ℝ f) :=
  (hc.lipschitzSmoothWith_iff_lipschitzWith_gradient hf).trans
    lipschitzWith_fderiv_iff_lipschitzWith_gradient.symm

/-- **Baillon-Haddad theorem** (`iff` form): for a differentiable convex function on a Hilbert
space, `K`-Lipschitz gradient is equivalent to `K`-cocoercivity. -/
theorem cocoerciveWith_iff_lipschitzWith_gradient
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    CocoerciveWith K f ↔ LipschitzWith K (∇ f) :=
  (hc.lipschitzSmoothWith_iff_cocoerciveWith hf).symm.trans
    (hc.lipschitzSmoothWith_iff_lipschitzWith_gradient hf)

end ConvexOn
