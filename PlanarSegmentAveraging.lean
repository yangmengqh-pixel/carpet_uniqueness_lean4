import PlanarAffineBallIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Averaging a line-segment integral over the endpoints in a ball
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 4400000 in
theorem lintegral_ball_segment_average_le {F : PlanarCoordinates → ℝ}
    (hF : Continuous F) (hF₀ : ∀ x, 0 ≤ F x) (x : PlanarCoordinates) (r : ℝ) :
    (∫⁻ y in ball x r, ∫⁻ z in ball x r, ∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (F (AffineMap.lineMap y z t)) ∂volume ∂volume ∂volume) ≤
      4 * volume (ball x r) * ∫⁻ y in ball x r, ENNReal.ofReal (F y) ∂volume := by
  let B := ball x r
  let μ := (volume : Measure PlanarCoordinates).restrict B
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  let G (t : ℝ) (y z : PlanarCoordinates) := ENNReal.ofReal (F (AffineMap.lineMap y z t))
  let J := ∫⁻ y, ENNReal.ofReal (F y) ∂μ
  have hI : Integrable F μ :=
    (hF.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hJ : J = ENNReal.ofReal (∫ y, F y ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hF₀)).symm
  have hpair (t : ℝ) : Measurable (uncurry (G t)) := by
    have hcont : Continuous (fun a : PlanarCoordinates × PlanarCoordinates ↦
        F ((1 - t) • a.1 + t • a.2)) := by fun_prop
    simpa only [uncurry_def, G, AffineMap.lineMap_apply_module] using hcont.measurable.ennreal_ofReal
  have hsingle (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) 1)
      (y : PlanarCoordinates) (hy : y ∈ B) :
      (∫⁻ z, G t y z ∂μ) ≤ 4 * J := by
    have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 1 / 2).trans_le ht.1
    have hcont : Continuous (fun z ↦ F (AffineMap.lineMap y z t)) := by
      simp only [AffineMap.lineMap_apply_module]
      exact hF.comp (continuous_const.add (continuous_id.const_smul t))
    have hGint : Integrable (fun z ↦ F (AffineMap.lineMap y z t)) μ :=
      (hcont.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
    have hh := integral_lineMap_ball_le hF hF₀ hy ht₀ ht.2
    have hinv : (t ^ (2 : ℕ))⁻¹ ≤ 4 := by
      apply (inv_le_iff_one_le_mul₀ (sq_pos_of_pos ht₀)).mpr
      nlinarith only [ht.1, (sq_nonneg (t - 1 / 2))]
    have ht' := hh.trans (mul_le_mul_of_nonneg_right hinv (integral_nonneg fun y ↦ hF₀ y))
    change (∫⁻ z, ENNReal.ofReal (F (AffineMap.lineMap y z t)) ∂μ) ≤ 4 * J
    rw [← ofReal_integral_eq_lintegral_ofReal hGint (Eventually.of_forall fun z ↦ hF₀ _),
      hJ, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal ht'
  have htPair (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (∫⁻ y, ∫⁻ z, G t y z ∂μ ∂μ) ≤ 4 * (μ univ) * J := by
    have haux (q : ℝ) (hq : q ∈ Icc (1 / 2 : ℝ) 1) :
        (∫⁻ y, ∫⁻ z, G q y z ∂μ ∂μ) ≤ 4 * (μ univ) * J := by
      calc
        _ ≤ ∫⁻ _y, 4 * J ∂μ := lintegral_mono_ae
          ((ae_restrict_mem isOpen_ball.measurableSet).mono fun y hy ↦ hsingle q hq y hy)
        _ = _ := by rw [lintegral_const]; ac_rfl
    by_cases h : (1 / 2 : ℝ) ≤ t
    · exact haux t ⟨h, ht.2⟩
    · rw [lintegral_lintegral_swap (hpair t).aemeasurable]
      have he (y z : PlanarCoordinates) : G t y z = G (1 - t) z y := by
        simp only [G, AffineMap.lineMap_apply_one_sub]
      simp only [he]
      exact haux (1 - t) ⟨by linarith, by linarith [ht.1]⟩
  have hswap :
      (∫⁻ y, ∫⁻ z, ∫⁻ t, G t y z ∂ν ∂μ ∂μ) =
        ∫⁻ t, ∫⁻ y, ∫⁻ z, G t y z ∂μ ∂μ ∂ν := by
    have hflip (y : PlanarCoordinates) : Measurable (uncurry (fun z t ↦ G t y z)) := by
      have hcont : Continuous (fun a : PlanarCoordinates × ℝ ↦ F ((1 - a.2) • y + a.2 • a.1)) := by
        fun_prop
      simpa only [uncurry_def, G, AffineMap.lineMap_apply_module] using hcont.measurable.ennreal_ofReal
    have hinner : Measurable (uncurry (fun (y : PlanarCoordinates) (t : ℝ) ↦ ∫⁻ z, G t y z ∂μ)) := by
      have hcont : Continuous (fun a : (PlanarCoordinates × ℝ) × PlanarCoordinates ↦
          F ((1 - a.1.2) • a.1.1 + a.1.2 • a.2)) := by fun_prop
      have h : Measurable (fun a : (PlanarCoordinates × ℝ) × PlanarCoordinates ↦
          G a.1.2 a.1.1 a.2) := by
        simpa only [G, AffineMap.lineMap_apply_module] using hcont.measurable.ennreal_ofReal
      exact h.lintegral_prod_right'
    calc
      _ = ∫⁻ y, ∫⁻ t, ∫⁻ z, G t y z ∂μ ∂ν ∂μ :=
        lintegral_congr fun y ↦ lintegral_lintegral_swap (hflip y).aemeasurable
      _ = _ := lintegral_lintegral_swap hinner.aemeasurable
  have hν : ν univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
  change (∫⁻ y, ∫⁻ z, ∫⁻ t, G t y z ∂ν ∂μ ∂μ) ≤ 4 * volume B * J
  rw [hswap]
  calc
    _ ≤ ∫⁻ _t, 4 * (μ univ) * J ∂ν := lintegral_mono_ae
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ htPair t ht)
    _ = _ := by rw [lintegral_const, hν, mul_one, Measure.restrict_apply_univ]

end CarpetEnergy
