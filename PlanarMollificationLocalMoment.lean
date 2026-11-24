import SmoothMollificationLp
import PlanarLowerDensity
import Mathlib.MeasureTheory.Measure.Prod

/-!
# A local mollified moment uses mass only in the enlarged ball
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 4000000 in
theorem integral_abs_mollify_rpow_ball_le {p : ℝ} (hp : 1 ≤ p)
    {f : PlanarCoordinates → ℝ} (hfm : Measurable f) (hf : Integrable f volume)
    (hfP : Integrable (fun x ↦ |f x| ^ p) volume)
    (x : PlanarCoordinates) {r : ℝ} (_hr : 0 < r) {n : ℕ}
    (hn : (mollifierBump (X := PlanarCoordinates) n).rOut ≤ r) :
    (∫ y in ball x r, |mollify volume n f y| ^ p ∂volume) ≤
      ∫ y in ball x (2 * r), |f y| ^ p ∂volume := by
  let B := mollifierBump (X := PlanarCoordinates) n
  let K := B.normed volume
  let ν := (volume : Measure PlanarCoordinates).withDensity (fun z ↦ ENNReal.ofReal (K z))
  let μ := (volume : Measure PlanarCoordinates).restrict (ball x r)
  let P (y : PlanarCoordinates) := |f y| ^ p
  let F := ENNReal.ofReal ∘ P
  have hP₀ (y : PlanarCoordinates) : 0 ≤ P y := Real.rpow_nonneg (abs_nonneg _) _
  have hK₀ (z : PlanarCoordinates) : 0 ≤ K z := B.nonneg_normed z
  have hKm : Measurable (fun z ↦ ENNReal.ofReal (K z)) := B.continuous_normed.measurable.ennreal_ofReal
  have hmass : ν univ = 1 := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal B.integrable_normed (Eventually.of_forall hK₀),
      B.integral_normed, ENNReal.ofReal_one]
  let : IsProbabilityMeasure ν := ⟨hmass⟩
  have hν : ∀ᵐ z ∂ν, ‖z‖ ≤ r := by
    rw [ae_withDensity_iff hKm]
    refine Eventually.of_forall fun z hz ↦ ?_
    have hz' : z ∈ support K := mem_support.mpr fun h ↦ hz (h ▸ ENNReal.ofReal_zero)
    have hh : z ∈ ball (0 : PlanarCoordinates) B.rOut := (B.support_normed_eq (μ := volume)) ▸ hz'
    exact ((by simpa only [mem_ball, dist_zero_right] using hh : ‖z‖ < B.rOut).le.trans hn)
  have hshift {g : PlanarCoordinates → ℝ} (hg : Integrable g volume) (y : PlanarCoordinates) :
      Integrable (fun z ↦ g (y - z)) volume := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using (hg.comp_add_left y).comp_neg
  obtain ⟨M, hM⟩ := (B.hasCompactSupport_normed (μ := volume)).exists_bound_of_continuous (B.continuous_normed (μ := volume))
  have hFm : Measurable F :=
    (ENNReal.continuous_ofReal.measurable.comp ((Real.continuous_rpow_const (zero_le_one.trans hp)).measurable.comp
      (continuous_abs.measurable.comp hfm)))
  have hpoint (y : PlanarCoordinates) :
      ENNReal.ofReal (|mollify volume n f y| ^ p) ≤ ∫⁻ z, F (y - z) ∂ν := by
    refine (ENNReal.ofReal_le_ofReal (abs_mollify_rpow_le_mollify_abs_rpow volume hp n hf hfP y)).trans_eq ?_
    have hi : Integrable (fun z ↦ K z * P (y - z)) volume :=
      (hshift hfP y).bdd_mul B.continuous_normed.aestronglyMeasurable (Eventually.of_forall hM)
    change ENNReal.ofReal (∫ z, K z * P (y - z) ∂volume) = _
    have hFsub : Measurable (fun z : PlanarCoordinates ↦ F (y - z)) := by
      have hsub : Measurable (fun z : PlanarCoordinates ↦ y - z) := measurable_const.sub measurable_id
      exact hFm.comp hsub
    dsimp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul _ hKm hFsub,
      ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun z ↦ mul_nonneg (hK₀ z) (hP₀ _))]
    simp only [F, Function.comp_apply, Pi.mul_apply, ENNReal.ofReal_mul (hK₀ _)]
  have hprod : AEMeasurable (uncurry (fun y z : PlanarCoordinates ↦ F (y - z))) (μ.prod ν) :=
    (hFm.comp (measurable_fst.sub measurable_snd)).aemeasurable
  have hloc (z : PlanarCoordinates) (hz : ‖z‖ ≤ r) :
      (∫⁻ y, F (y - z) ∂μ) ≤ ∫⁻ y in ball x (2 * r), F y ∂volume := by
    let H := (ball x (2 * r)).indicator F
    calc
      _ = ∫⁻ y, H (y - z) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
        have hdist : dist (y - z) y = ‖z‖ := by rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
        have hmem' : y - z ∈ ball x (2 * r) := mem_ball.mpr
          ((dist_triangle (y - z) y x).trans_lt (by linarith [mem_ball.mp hy]))
        exact (indicator_of_mem hmem' F).symm
      _ ≤ ∫⁻ y, H (y - z) ∂volume := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = _ := by
        simp only [sub_eq_add_neg, lintegral_add_right_eq_self]
        dsimp only [H]
        rw [lintegral_indicator isOpen_ball.measurableSet]
  have hle : (∫⁻ y, ENNReal.ofReal (|mollify volume n f y| ^ p) ∂μ) ≤
      ∫⁻ y in ball x (2 * r), F y ∂volume := by
    calc
      _ ≤ ∫⁻ y, ∫⁻ z, F (y - z) ∂ν ∂μ := lintegral_mono hpoint
      _ = ∫⁻ z, ∫⁻ y, F (y - z) ∂μ ∂ν := lintegral_lintegral_swap hprod
      _ ≤ ∫⁻ _ : PlanarCoordinates, (∫⁻ y in ball x (2 * r), F y ∂volume) ∂ν :=
        lintegral_mono_ae (hν.mono hloc)
      _ = _ := by rw [lintegral_const, hmass, mul_one]
  have hI := (integrable_abs_rpow_mollify_and_integral_le volume hp n hf hfP).1
  change _ ≤ ∫⁻ y in ball x (2 * r), ENNReal.ofReal (P y) ∂volume at hle
  rw [← ofReal_integral_eq_lintegral_ofReal hI.restrict
    (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _),
    ← ofReal_integral_eq_lintegral_ofReal hfP.restrict (Eventually.of_forall hP₀)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hP₀)).mp hle

end CarpetEnergy
