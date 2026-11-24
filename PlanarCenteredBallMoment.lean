import PlanarBallPairMoment

/-!
# Centered (L^p) Poincaré estimate on planar balls
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 3400000 in
theorem integral_abs_sub_ballMean_rpow_le {p : ℝ} (hp : 1 ≤ p)
    {f : PlanarCoordinates → ℝ} (hf : ContDiff ℝ 1 f)
    (x : PlanarCoordinates) {r : ℝ} (hr : 0 < r) :
    let B := ball x r
    let a := (volume.real B)⁻¹ * ∫ y in B, f y ∂volume
    (∫ y in B, |f y - a| ^ p ∂volume) ≤
      (4 * (2 * r) ^ p) * ∫ y in B, ‖fderiv ℝ f y‖ ^ p ∂volume := by
  let B := ball x r
  let μ := (volume : Measure PlanarCoordinates).restrict B
  let m := volume B
  let ν := m⁻¹ • μ
  let a := m.toReal⁻¹ * ∫ y, f y ∂μ
  have hmpos : m ≠ 0 := by
    rw [show m = volume (ball x r) from rfl, planar_volume_ball x hr.le]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hmtop : m ≠ ∞ := by
    rw [show m = volume (ball x r) from rfl, planar_volume_ball x hr.le]
    exact ENNReal.ofReal_ne_top
  have hminv : m⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hmpos
  have : IsProbabilityMeasure ν := ⟨by
    change (m⁻¹ • μ) univ = 1
    rw [smul_apply, smul_eq_mul, show μ univ = m from Measure.restrict_apply_univ B,
      ENNReal.inv_mul_cancel hmpos hmtop]⟩
  have hp₀ : 0 ≤ p := zero_le_one.trans hp
  have hC : 0 ≤ 4 * (2 * r) ^ p := by positivity
  have hI {F : PlanarCoordinates → ℝ} (hF : Continuous F) : Integrable F μ :=
    (hF.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hIv {F : PlanarCoordinates → ℝ} (hF : Continuous F) : Integrable F ν :=
    (hI hF).smul_measure hminv
  have hmean : ∫ y, f y ∂ν = a := by
    change ∫ y, f y ∂(m⁻¹ • μ) = _
    rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  have hJ (y : PlanarCoordinates) :
      ENNReal.ofReal (|f y - a| ^ p) ≤ m⁻¹ * ∫⁻ z, ENNReal.ofReal (|f z - f y| ^ p) ∂μ := by
    let g (z : PlanarCoordinates) := f z - f y
    have hg : Continuous g := hf.continuous.sub continuous_const
    have hgP : Continuous (fun z ↦ |g z| ^ p) := hg.abs.rpow_const (fun _ ↦ Or.inr hp₀)
    have he : (∫ z, g z ∂ν) = a - f y := by
      dsimp only [g]
      rw [integral_sub (hIv hf.continuous) (integrable_const _), hmean, integral_const, measureReal_def,
        measure_univ, ENNReal.toReal_one, one_smul]
    have hA : |f y - a| ≤ ∫ z, |g z| ∂ν := by
      rw [abs_sub_comm, ← he]
      exact abs_integral_le_integral_abs
    have hh := (convexOn_rpow hp).map_integral_le (Real.continuous_rpow_const hp₀).continuousOn
      isClosed_Ici (Eventually.of_forall fun z ↦ abs_nonneg (g z)) (hIv hg.abs) (hIv hgP)
    have hle := (Real.rpow_le_rpow (abs_nonneg _) hA hp₀).trans hh
    have hL := ENNReal.ofReal_le_ofReal hle
    rw [ofReal_integral_eq_lintegral_ofReal (hIv hgP)
      (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)] at hL
    change _ ≤ ∫⁻ z, ENNReal.ofReal (|f z - f y| ^ p) ∂(m⁻¹ • μ) at hL
    rwa [lintegral_smul_measure, smul_eq_mul] at hL
  have hL : (∫⁻ y, ENNReal.ofReal (|f y - a| ^ p) ∂μ) ≤
      ∫⁻ y, m⁻¹ * ∫⁻ z, ENNReal.ofReal (|f z - f y| ^ p) ∂μ ∂μ :=
    lintegral_mono hJ
  rw [lintegral_const_mul' _ _ hminv] at hL
  have hP := lintegral_ball_pair_abs_sub_rpow_le hp hf x hr
  have hQ := hL.trans (mul_le_mul_of_nonneg_left hP (bot_le : (0 : ℝ≥0∞) ≤ _))
  have hcancel (T : ℝ≥0∞) : m⁻¹ * (ENNReal.ofReal (4 * (2 * r) ^ p) * m * T) =
      ENNReal.ofReal (4 * (2 * r) ^ p) * T := by
    calc
      _ = (m⁻¹ * m) * (ENNReal.ofReal (4 * (2 * r) ^ p) * T) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hmpos hmtop, one_mul]
  change _ ≤ m⁻¹ * (ENNReal.ofReal (4 * (2 * r) ^ p) * m * _) at hQ
  rw [hcancel] at hQ
  have hfi : Integrable (fun y ↦ |f y - a| ^ p) μ :=
    hI ((hf.continuous.sub continuous_const).abs.rpow_const (fun _ ↦ Or.inr hp₀))
  have hdi : Integrable (fun y ↦ ‖fderiv ℝ f y‖ ^ p) μ :=
    hI ((hf.continuous_fderiv (by norm_num)).norm.rpow_const (fun _ ↦ Or.inr hp₀))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun y ↦ Real.rpow_nonneg (abs_nonneg _) _),
    ← ofReal_integral_eq_lintegral_ofReal hdi (Eventually.of_forall fun y ↦ Real.rpow_nonneg (norm_nonneg _) _),
    ← ENNReal.ofReal_mul hC] at hQ
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _))).mp hQ

end CarpetEnergy
