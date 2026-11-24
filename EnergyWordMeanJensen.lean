import CarpetWordIntegral

/-!
# A Jensen bound for word means

The centered mean to the p-th power is bounded by the normalized
integral of the centered p-th power over the word cell.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1100000 in
theorem abs_wordMean_sub_rpow_mul_le (w : List (Fin 8)) (f : E.domain) (c : ℝ) :
    ((8 : ℝ)⁻¹) ^ w.length * |E.wordMean w f - c| ^ p ≤
      ∫ x in range (wordMap w), |(f : CarpetLp p) x - c| ^ p ∂carpetMeasure := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp := zero_lt_one.trans E.one_lt_p
  let g : CarpetLp p := E.pullbackWord w f
  let a := constantLp p c
  let T : CarpetLp p →L[ℝ] ℝ := lpSetIntegral univ
  have ha : T a = c := by
    change (∫ x in univ, a x ∂carpetMeasure) = c
    dsimp only [a, constantLp]
    rw [Measure.restrict_univ, integral_congr_ae (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c)]
    change (∫ _ : CarpetPoints, c ∂carpetMeasure) = c
    rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hg : T g = E.wordMean w f := by
    change (∫ x in univ, g x ∂carpetMeasure) = _
    rw [Measure.restrict_univ]
    rfl
  have hm : |E.wordMean w f - c| ≤ ‖g - a‖ := by
    rw [← hg, ← ha, ← map_sub, ← Real.norm_eq_abs]
    exact norm_setIntegral_le univ (g - a)
  let φ (t : ℝ) := |t - c| ^ p
  have hφ : Continuous φ :=
    (continuous_id.sub continuous_const).abs.rpow_const (fun _ ↦ Or.inr hp.le)
  have hInt : (∫ x, φ (g x) ∂carpetMeasure) = ‖g - a‖ ^ p := by
    rw [← integral_abs_rpow_eq_norm_rpow hp]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub g a, Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c] with x hx hx'
    have he : (g - a) x = g x - a x := hx
    change a x = c at hx'
    rw [he, hx']
  change _ ≤ ∫ x in range (wordMap w), φ ((f : CarpetLp p) x) ∂carpetMeasure
  rw [setIntegral_wordMap_of_isLpPullback w (E.pullbackWord_isLpPullback w f) hφ]
  change _ ≤ ((8 : ℝ)⁻¹) ^ w.length * ∫ x, φ (g x) ∂carpetMeasure
  rw [hInt]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hm hp.le) (by positivity)

end CarpetEnergy.SelfSimilarPEnergy
