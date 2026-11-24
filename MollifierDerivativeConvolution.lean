import SmoothMollification
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The convolution formula for the derivative on the mollifier side
-/

open ContinuousLinearMap MeasureTheory
open scoped Convolution

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [HasContDiffBump X] [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [μ.IsAddHaarMeasure]

/-- Differentiation against the smooth kernel requires no derivative
of the input profile. -/
theorem fderiv_mollify_apply_eq_integral_mollifier_fderiv {f : X → ℝ}
    (hf : Integrable f μ) (n : ℕ) (x e : X) :
    fderiv ℝ (mollify μ n f) x e =
      ∫ y, fderiv ℝ ((mollifierBump n).normed μ) y e * f (x - y) ∂μ := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  let K := (mollifierBump n).normed μ
  have hK : ContDiff ℝ 1 K := (mollifierBump n).contDiff_normed
  have hKs : HasCompactSupport K := (mollifierBump n).hasCompactSupport_normed
  have hd := hKs.hasFDerivAt_convolution_left L hK hf.locallyIntegrable x
  change HasFDerivAt (mollify μ n f) _ x at hd
  rw [hd.fderiv, convolution_def]
  have hInt := (hKs.fderiv ℝ).convolutionExists_left (L.precompL X)
    (hK.continuous_fderiv (by norm_num)) hf.locallyIntegrable x
  exact ContinuousLinearMap.integral_apply hInt e

end CarpetEnergy
