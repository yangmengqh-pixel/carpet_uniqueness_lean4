import MollifierDerivativeBudget
import PlanarLowerDensity

/-!
# Comparing planar mollification with ball integrals
-/

open ContinuousLinearMap Filter Function MeasureTheory Metric Set
open scoped Convolution ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 2800000 in
/-- The normalized kernel is constant on the inner half ball,
bounded by that constant everywhere, and supported in the outer ball. -/
theorem exists_planar_mollifier_ball_integral_bounds :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (f : PlanarCoordinates → ℝ), Integrable f volume →
      (∀ x, 0 ≤ f x) → ∀ x : PlanarCoordinates,
      let r := (mollifierBump (X := PlanarCoordinates) n).rOut
      (C / r ^ (2 : ℕ)) * (∫ y in ball x (r / 2), f y ∂volume) ≤ mollify volume n f x ∧
      mollify volume n f x ≤ (C / r ^ (2 : ℕ)) * ∫ y in ball x r, f y ∂volume := by
  let B₀ := mollifierBump (X := PlanarCoordinates) 0
  let C := (∫ y, B₀ y ∂volume)⁻¹
  have hC : 0 < C := inv_pos.mpr B₀.integral_pos
  refine ⟨C, hC, fun n f hf hf₀ x ↦ ?_⟩
  let B := mollifierBump (X := PlanarCoordinates) n
  let r := B.rOut
  let K := B.normed volume
  let D := C / r ^ (2 : ℕ)
  have hr : 0 < r := B.rOut_pos
  have hD : 0 ≤ D := div_nonneg hC.le (sq_nonneg r)
  have hnorm (y : PlanarCoordinates) : K y = D * B₀ (r⁻¹ • y) := by
    dsimp only [K, B]
    rw [mollifier_normed_eq_dilation, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    change (r ^ (2 : ℕ))⁻¹ * B₀.normed volume (r⁻¹ • y) = C / r ^ (2 : ℕ) * B₀ (r⁻¹ • y)
    rw [ContDiffBump.normed_def, div_eq_mul_inv, div_eq_mul_inv]
    dsimp only [C]
    ring
  have hK₀ (y : PlanarCoordinates) : 0 ≤ K y := B.nonneg_normed y
  have hKle (y : PlanarCoordinates) : K y ≤ D := by
    rw [hnorm]
    exact mul_le_of_le_one_right hD B₀.le_one
  have hKI (y : PlanarCoordinates) (hy : ‖y‖ < r / 2) : K y = D := by
    rw [hnorm, B₀.one_of_mem_closedBall, mul_one]
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
      ← div_eq_inv_mul]
    apply (div_le_iff₀ hr).mpr
    convert hy.le using 1
    change B₀.rIn * r = _
    change ((1 / (((0 : ℕ) : ℝ) + 1)) / 2) * r = r / 2
    norm_num
    ring
  have hK0 (y : PlanarCoordinates) (hy : r ≤ ‖y‖) : K y = 0 := by
    apply notMem_support.mp
    rw [B.support_normed_eq (μ := volume), mem_ball, dist_zero_right]
    exact not_lt.mpr hy
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  have hconv : mollify volume n f x = ∫ y, K (x - y) * f y ∂volume := by
    change (K ⋆[L, volume] f) x = _
    rw [convolution_eq_swap L]
    simp only [L, lsmul_apply, smul_eq_mul]
  have hprod : Integrable (fun y ↦ K (x - y) * f y) volume := by
    refine hf.bdd_mul (c := D) ((B.continuous_normed.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hK₀ (x - y))]; exact hKle _
  change D * (∫ y in ball x (r / 2), f y ∂volume) ≤ mollify volume n f x ∧
    mollify volume n f x ≤ D * ∫ y in ball x r, f y ∂volume
  rw [hconv, ← integral_const_mul, ← integral_const_mul,
    ← integral_indicator isOpen_ball.measurableSet, ← integral_indicator isOpen_ball.measurableSet]
  constructor
  · apply integral_mono ((hf.const_mul D).indicator isOpen_ball.measurableSet) hprod
    intro y
    change (ball x (r / 2)).indicator (fun z ↦ D * f z) y ≤ K (x - y) * f y
    by_cases hy : y ∈ ball x (r / 2)
    · rw [indicator_of_mem hy, hKI]
      simpa only [mem_ball, dist_comm y x, dist_eq_norm] using hy
    · rw [indicator_of_notMem hy]
      exact mul_nonneg (hK₀ _) (hf₀ y)
  · apply integral_mono hprod ((hf.const_mul D).indicator isOpen_ball.measurableSet)
    intro y
    change K (x - y) * f y ≤ (ball x r).indicator (fun z ↦ D * f z) y
    by_cases hy : y ∈ ball x r
    · rw [indicator_of_mem hy]
      exact mul_le_mul_of_nonneg_right (hKle _) (hf₀ y)
    · rw [indicator_of_notMem hy, hK0, zero_mul]
      apply le_of_not_gt
      simpa only [mem_ball, dist_comm y x, dist_eq_norm] using hy

end CarpetEnergy
