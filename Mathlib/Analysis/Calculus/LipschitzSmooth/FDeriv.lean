/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Lipschitz smoothness via the Fréchet derivative

Fréchet-derivative restatements of the `LipschitzSmoothWith` predicate from
`Mathlib.Analysis.Calculus.LipschitzSmooth.Basic`, and the descent lemma:
a Lipschitz Fréchet derivative implies `K`-smoothness.

For differentiable `f`, `lineDeriv` and `fderiv` agree pointwise, allowing
the line-derivative variation bound `LipschitzSmoothWith.lineDeriv_apply_sub_le`
to be restated in terms of `fderiv`. The descent direction goes through the
fundamental theorem of calculus along a line segment, expressed using
`Mathlib.MeasureTheory.Integral.CurveIntegral`.

## Main results

* `lipschitzSmoothWith_iff_fderiv` — characterisation in Fréchet form under `Differentiable`.
* `LipschitzSmoothWith.fderiv_descent_le` — the descent inequality in Fréchet form.
* `LipschitzSmoothWith.fderiv_apply_sub_le` — variance bound on the Fréchet derivative.
* `LipschitzSmoothWith.fderiv_sub_apply_le` — function-subtraction restatement.
* `LipschitzSmoothOnSegmentWith.of_lipschitzWith_fderiv` — a `K`-Lipschitz Fréchet
  derivative implies the segment-pointwise smoothness bound.
* `LipschitzSmoothOnSegmentWith.lipschitzSmoothWith` — under `Differentiable ℝ f` and
  continuity of `fderiv ℝ f`, the segment-pointwise bound integrates to `K`-smoothness
  via the fundamental theorem of calculus.
* `Differentiable.lipschitzSmoothWith_of_lipschitzWith` — descent lemma: differentiability
  plus a `K`-Lipschitz Fréchet derivative implies `K`-smoothness.
-/

public section

open AffineMap MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : NNReal} {f : F → ℝ}

/-! ### Segment-pointwise form -/

/-- The pointwise Lipschitz-smoothness bound on the Fréchet derivative along the segment from
`x` to `y`: `(fderiv ℝ f z - fderiv ℝ f x) (y - x) ≤ K · dist x z · dist x y` for all
`z ∈ [x -[ℝ] y]`. This is the segment-pointwise form that integrates to the descent inequality. -/
abbrev LipschitzSmoothOnSegmentWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ x y : F, ∀ z ∈ segment ℝ x y,
    (fderiv ℝ f z - fderiv ℝ f x) (y - x) ≤ ↑K * dist x z * dist x y

/-! ### Fréchet-derivative restatements of K-smoothness -/

theorem lipschitzSmoothWith_iff_fderiv (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔
      ∀ x y : F, f y ≤ f x + fderiv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 := by
  rw [lipschitzSmoothWith_iff_lineDeriv]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [(hf x).lineDeriv_eq_fderiv]

namespace LipschitzSmoothWith

theorem fderiv_descent_le (h : LipschitzSmoothWith K f) (x y : F)
    (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + fderiv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_descent_le x y

theorem fderiv_apply_sub_le (h : LipschitzSmoothWith K f) (x y : F)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  rw [← hfy.lineDeriv_eq_fderiv, ← hfx.lineDeriv_eq_fderiv]
  exact h.lineDeriv_apply_sub_le x y

theorem fderiv_sub_apply_le (h : LipschitzSmoothWith K f) (x y : F)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    (fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  rw [ContinuousLinearMap.sub_apply]
  exact h.fderiv_apply_sub_le x y hfx hfy

end LipschitzSmoothWith

/-! ### Descent lemma -/

/-- A `K`-Lipschitz Fréchet derivative implies the segment-pointwise smoothness bound:
`(fderiv ℝ f z - fderiv ℝ f x) (y - x) ≤ K · dist x z · dist x y` for every `z ∈ [x -[ℝ] y]`.
The argument is Cauchy-Schwarz / `le_opNorm` plus the Lipschitz bound at the pair `(z, x)`. -/
theorem LipschitzSmoothOnSegmentWith.of_lipschitzWith_fderiv
    (hL : LipschitzWith K (fderiv ℝ f)) : LipschitzSmoothOnSegmentWith K f := fun x y z _ =>
  calc (fderiv ℝ f z - fderiv ℝ f x) (y - x)
      ≤ ‖fderiv ℝ f z - fderiv ℝ f x‖ * ‖y - x‖ :=
        (Real.le_norm_self _).trans (ContinuousLinearMap.le_opNorm _ _)
    _ = dist (fderiv ℝ f x) (fderiv ℝ f z) * dist x y := by repeat rw [← dist_eq_norm']
    _ ≤ ↑K * dist x z * dist x y := mul_le_mul_of_nonneg_right (hL.dist_le_mul _ _) dist_nonneg

/-- For a segment-pointwise Lipschitz-smooth function with continuous Fréchet derivative, the
curve integral of `fderiv ℝ f z - fderiv ℝ f x` along the segment from `x` to `y` is bounded
by `K/2 · (dist x y)²`. The quantitative FTC step of the descent lemma. -/
theorem LipschitzSmoothOnSegmentWith.curveIntegral_le
      (h : LipschitzSmoothOnSegmentWith K f) (hcont : Continuous (fderiv ℝ f)) (x y : F) :
      ∫ᶜ z in .segment x y, (fderiv ℝ f z - fderiv ℝ f x) ≤ ↑K / 2 * (dist x y) ^ 2 := 
    calc ∫ᶜ z in .segment x y, (fderiv ℝ f z - fderiv ℝ f x)
      _ = ∫ t in 0..1, (fderiv ℝ f (lineMap x y t) - fderiv ℝ f x) (y - x) :=
          curveIntegral_segment _ _ _
      _ ≤ ∫ t in 0..1, ↑K * (dist x y) ^ 2 * t :=
          intervalIntegral.integral_mono_on (by norm_num)
            (curveIntegrable_segment_iff.mp <|
              (hcont.curveIntegrable_segment x y).sub (curveIntegrable_segment_const _ x y))
            (Continuous.intervalIntegrable (by fun_prop) _ _) (fun t ht =>
              (h _ _ _ (lineMap_mem_segment ℝ x y ht)).trans_eq <| by
                rw [dist_left_lineMap, Real.norm_of_nonneg ht.1]; ring)
      _ = ↑K * (dist x y) ^ 2 * ∫ t in 0..1, t := intervalIntegral.integral_const_mul _ _
      _ = ↑K / 2 * (dist x y) ^ 2 := by rw [integral_id]; ring

/-- The segment-pointwise smoothness bound, together with differentiability and continuity of
the Fréchet derivative, implies `K`-smoothness. The proof integrates the pointwise bound
`K · dist x z · dist x y` along the segment from `x` to `y` using FTC. -/
theorem LipschitzSmoothOnSegmentWith.lipschitzSmoothWith
    (hptwise : LipschitzSmoothOnSegmentWith K f) (hf : Differentiable ℝ f)
    (hcont : Continuous (fderiv ℝ f)) : LipschitzSmoothWith K f := by
  refine lipschitzSmoothWith_iff_lineDeriv.mpr fun x y => ?_
  have := calc f y - f x - lineDeriv ℝ f x (y - x)
    _ = f y - f x - (fderiv ℝ f x) (y - x) := by rw [(hf x).lineDeriv_eq_fderiv]
    _ = (∫ᶜ z in .segment x y, fderiv ℝ f z) - ∫ᶜ _ in .segment x y, fderiv ℝ f x := by
        rw [← curveIntegral_fderiv_segment hf hcont, ← curveIntegral_segment_const]
    _ = ∫ᶜ z in .segment x y, (fderiv ℝ f z - fderiv ℝ f x) :=
          (curveIntegral_fun_sub (hcont.curveIntegrable_segment x y)
            (curveIntegrable_segment_const _ x y)).symm
    _ ≤ ↑K / 2 * dist x y ^ 2 := hptwise.curveIntegral_le hcont x y
  linarith

/-- **Descent lemma.** If `f` is differentiable and its Fréchet derivative is
`K`-Lipschitz, then `f` is `K`-smooth (without convexity assumption). -/
theorem Differentiable.lipschitzSmoothWith_of_lipschitzWith
    (hf : Differentiable ℝ f) (hL : LipschitzWith K (fderiv ℝ f)) : LipschitzSmoothWith K f :=
  (LipschitzSmoothOnSegmentWith.of_lipschitzWith_fderiv hL).lipschitzSmoothWith hf hL.continuous
