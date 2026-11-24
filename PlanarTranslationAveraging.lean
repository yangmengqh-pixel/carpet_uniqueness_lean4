import PlanarSobolevTranslation
import LintegralHolderMass
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Averaging the (L^p) translation estimate against a finite kernel
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

set_option maxHeartbeats 3000000 in
/-- The averaged translation bound used for the convolution errors
in (8.10). The kernel enters only through its mass and support radius. -/
theorem lintegral_planar_translation_average_rpow_le {p : ℝ} (hp : 1 < p)
    {u : Plane2 → ℝ} (huM : Measurable u) (hu : Integrable u volume)
    (v : Fin 2 → Plane2 → ℝ) (hv : ∀ i, Integrable (v i) volume)
    (hvp : ∀ i, Integrable (fun x ↦ |v i x| ^ p) volume)
    (h : ∀ i, HasWeakDirectionalDerivative volume u (v i) (planarDirection i))
    (ν : Measure Plane2) [IsFiniteMeasure ν] {r : ℝ} (hr : 0 ≤ r)
    (hνr : ∀ᵐ z ∂ν, ‖z‖ ≤ r) :
    (∫⁻ x, (∫⁻ z, ENNReal.ofReal |u (x - z) - u x| ∂ν) ^ p ∂volume) ≤
      (ν univ * ENNReal.ofReal r) ^ p * ENNReal.ofReal
        ((2 : ℝ) ^ (p - 1) * ((∫ x, |v 0 x| ^ p ∂volume) + ∫ x, |v 1 x| ^ p ∂volume)) := by
  let F (x z : Plane2) := ENNReal.ofReal |u (x - z) - u x|
  let C := (2 : ℝ) ^ (p - 1) * ((∫ x, |v 0 x| ^ p ∂volume) + ∫ x, |v 1 x| ^ p ∂volume)
  have hp₀ := zero_lt_one.trans hp
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (add_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _))
  have hM : Measurable (Function.uncurry (fun x z ↦ F x z ^ p)) := by
    exact (continuous_abs.measurable.comp ((huM.comp (measurable_fst.sub measurable_snd)).sub
      (huM.comp measurable_fst))).ennreal_ofReal.pow_const _
  calc
    _ ≤ ∫⁻ x, ν univ ^ (p - 1) * ∫⁻ z, F x z ^ p ∂ν ∂volume := by
      apply lintegral_mono
      intro x
      exact lintegral_rpow_le_mass_rpow_mul hp
        ((continuous_abs.measurable.comp
          ((huM.comp (measurable_const.sub measurable_id)).sub measurable_const)).ennreal_ofReal.aemeasurable)
    _ = ν univ ^ (p - 1) * ∫⁻ z, ∫⁻ x, F x z ^ p ∂volume ∂ν := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hp.le) (measure_ne_top _ _)),
        lintegral_lintegral_swap hM.aemeasurable]
    _ ≤ ν univ ^ (p - 1) * (ENNReal.ofReal (C * r ^ p) * ν univ) := by
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      rw [← lintegral_const (μ := ν) (ENNReal.ofReal (C * r ^ p))]
      apply lintegral_mono_ae
      filter_upwards [hνr] with z hz
      obtain ⟨hI, hle⟩ := integral_abs_planar_translation_sub_rpow_le hp.le hu v hv hvp h (-z)
      simp only [← sub_eq_add_neg, norm_neg] at hI hle
      have hle' : (∫ x, |u (x - z) - u x| ^ p ∂volume) ≤ C * r ^ p := by
        refine hle.trans ?_
        have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hz hp₀.le) hC
        convert hh using 1
        dsimp only [C]
        ring
      simp only [F, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp₀.le]
      rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal hle'
    _ = _ := by
      rw [ENNReal.ofReal_mul hC, ← ENNReal.ofReal_rpow_of_nonneg hr hp₀.le, ENNReal.mul_rpow_of_nonneg _ _ hp₀.le]
      calc
        _ = (ν univ ^ (p - 1) * ν univ ^ (1 : ℝ)) * ENNReal.ofReal r ^ p * ENNReal.ofReal C := by
          simp only [ENNReal.rpow_one]
          ac_rfl
        _ = _ := by
          rw [← ENNReal.rpow_add_of_nonneg (p - 1) 1 (sub_nonneg.mpr hp.le) zero_le_one,
            sub_add_cancel]

end CarpetEnergy
