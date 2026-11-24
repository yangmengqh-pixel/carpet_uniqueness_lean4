import PlanarSegmentAveraging
import SmoothSegmentMoment

/-!
# The pairwise oscillation estimate on a planar ball
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 3100000 in
theorem lintegral_ball_pair_abs_sub_rpow_le {p : ℝ} (hp : 1 ≤ p)
    {f : PlanarCoordinates → ℝ} (hf : ContDiff ℝ 1 f)
    (x : PlanarCoordinates) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, ∫⁻ z in ball x r, ENNReal.ofReal (|f z - f y| ^ p) ∂volume ∂volume) ≤
      ENNReal.ofReal (4 * (2 * r) ^ p) * volume (ball x r) *
        ∫⁻ y in ball x r, ENNReal.ofReal (‖fderiv ℝ f y‖ ^ p) ∂volume := by
  let B := ball x r
  let μ := (volume : Measure PlanarCoordinates).restrict B
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  let F (y : PlanarCoordinates) := ‖fderiv ℝ f y‖ ^ p
  let C := (2 * r) ^ p
  have hp₀ : 0 ≤ p := zero_le_one.trans hp
  have hF : Continuous F := (hf.continuous_fderiv (by norm_num)).norm.rpow_const (fun _ ↦ Or.inr hp₀)
  have hF₀ (y : PlanarCoordinates) : 0 ≤ F y := Real.rpow_nonneg (norm_nonneg _) _
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity : 0 ≤ 2 * r) _
  have hpoint (y z : PlanarCoordinates) (hy : y ∈ B) (hz : z ∈ B) :
      ENNReal.ofReal (|f z - f y| ^ p) ≤ ENNReal.ofReal C *
        (∫⁻ t, ENNReal.ofReal (F (AffineMap.lineMap y z t)) ∂ν) := by
    have hdiff : ‖z - y‖ ≤ 2 * r := by
      rw [← dist_eq_norm]
      have hy' := mem_ball.mp hy
      have hz' := mem_ball.mp hz
      exact (dist_triangle_right z y x).trans (by linarith)
    have hcont : Continuous (fun t : ℝ ↦ F (AffineMap.lineMap y z t)) := by
      simp only [AffineMap.lineMap_apply_module']
      fun_prop
    have hI : Integrable (fun t ↦ F (AffineMap.lineMap y z t)) ν :=
      (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hpath : (∫ t, F (AffineMap.lineMap y z t) ∂ν) =
        ∫ t, F (y + t • (z - y)) ∂ν := by
      simp only [AffineMap.lineMap_apply_module', add_comm]
    have hh := abs_sub_rpow_le_segment_fderiv_moment hp hf y z
    change _ ≤ ‖z - y‖ ^ p * ∫ t, F (y + t • (z - y)) ∂ν at hh
    rw [← hpath] at hh
    have hfinal := hh.trans (mul_le_mul_of_nonneg_right
      (show ‖z - y‖ ^ p ≤ C from Real.rpow_le_rpow (norm_nonneg _) hdiff hp₀)
      (integral_nonneg (fun t ↦ hF₀ _)))
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun _ ↦ hF₀ _),
      ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hfinal
  change (∫⁻ y, ∫⁻ z, ENNReal.ofReal (|f z - f y| ^ p) ∂μ ∂μ) ≤ _
  have hb : (∫⁻ y, ∫⁻ z, ENNReal.ofReal (|f z - f y| ^ p) ∂μ ∂μ) ≤
      ∫⁻ y, ∫⁻ z, ENNReal.ofReal C *
        (∫⁻ t, ENNReal.ofReal (F (AffineMap.lineMap y z t)) ∂ν) ∂μ ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
    apply lintegral_mono_ae
    exact (ae_restrict_mem isOpen_ball.measurableSet).mono fun z hz ↦ hpoint y z hy hz
  refine hb.trans ?_
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hseg := lintegral_ball_segment_average_le hF hF₀ x r
  change (∫⁻ y, ∫⁻ z, ∫⁻ t, ENNReal.ofReal (F (AffineMap.lineMap y z t)) ∂ν ∂μ ∂μ) ≤ _ at hseg
  refine (mul_le_mul_of_nonneg_left hseg bot_le).trans_eq ?_
  change ENNReal.ofReal C * (4 * volume B * (∫⁻ y in B, ENNReal.ofReal (F y) ∂volume)) =
    ENNReal.ofReal (4 * C) * volume B * _
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have h4 : ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) := by norm_num
  rw [h4]
  let V := volume B
  let J := ∫⁻ y in B, ENNReal.ofReal (F y) ∂volume
  let U := ENNReal.ofReal C
  change U * (4 * V * J) = 4 * U * V * J
  calc
    _ = (U * 4) * V * J := by
      rw [mul_assoc (U * 4) V J, mul_assoc U 4 (V * J), mul_assoc 4 V J]
    _ = _ := by rw [mul_comm U 4]

end CarpetEnergy
