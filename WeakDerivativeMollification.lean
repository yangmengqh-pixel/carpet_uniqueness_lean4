import SmoothMollification
import PlanarDensityWeakDerivative

/-!
# Mollification commutes with weak differentiation

The reflected mollifier is a compactly supported smooth test.
The weak derivative identity for that test identifies the classical
derivative of the mollification.
-/

open ContinuousLinearMap Filter Function MeasureTheory Set
open scoped Convolution

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [HasContDiffBump X] [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [μ.IsAddHaarMeasure]

set_option maxHeartbeats 1450000 in
theorem fderiv_mollify_apply_eq_mollify_of_weakDerivative
    {u v : X → ℝ} {e : X} (hu : Integrable u μ)
    (h : HasWeakDirectionalDerivative μ u v e) (n : ℕ) (x : X) :
    fderiv ℝ (mollify μ n u) x e = mollify μ n v x := by
  let B := mollifierBump (X := X) n
  let K := B.normed μ
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  have hK : ContDiff ℝ 1 K := B.contDiff_normed
  have hKs : HasCompactSupport K := B.hasCompactSupport_normed
  have hcomm (w : X → ℝ) : mollify μ n w = w ⋆[L, μ] K := by
    funext y
    change (K ⋆[L, μ] w) y = (w ⋆[L, μ] K) y
    rw [convolution_eq_swap L, convolution_def]
    simp only [L, lsmul_apply, smul_eq_mul]
    congr 1
    funext t
    exact mul_comm _ _
  have hd := hKs.hasFDerivAt_convolution_right L hu.locallyIntegrable hK x
  rw [hcomm, hd.fderiv, convolution_precompR_apply L hu.locallyIntegrable (hKs.fderiv ℝ)
    (hK.continuous_fderiv (by norm_num)), hcomm]
  let ψ (y : X) := K (x - y)
  have hψ : ContDiff ℝ 1 ψ := hK.comp (contDiff_const.sub contDiff_id)
  have hψs : HasCompactSupport ψ := by
    apply HasCompactSupport.of_support_subset_isCompact
      (hKs.image (continuous_const.sub continuous_id : Continuous (fun y : X ↦ x - y)))
    intro y hy
    exact ⟨x - y, subset_tsupport K hy, sub_sub_cancel _ _⟩
  have hψd (y : X) : fderiv ℝ ψ y e = -(fderiv ℝ K (x - y) e) := by
    have hinner := (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id (𝕜 := ℝ) y)
    have houter := (hK.differentiable (by norm_num) (x - y)).hasFDerivAt.comp y hinner
    change HasFDerivAt ψ _ y at houter
    rw [houter.fderiv, zero_sub, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, map_neg]
  have hh := h ψ hψ hψs
  simp_rw [hψd, mul_neg, integral_neg] at hh
  change (∫ y, u y * fderiv ℝ K (x - y) e ∂μ) = ∫ y, v y * K (x - y) ∂μ
  exact neg_injective hh

end CarpetEnergy
