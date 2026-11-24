import EnergySpectralGap
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Integration on a word cell

The normalized carpet probability transports along a word map with
factor `8 ^ (-|w|)`. Integrals and p-th moments of Lp pullbacks
therefore give the corresponding cell averages and moments.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

theorem carpetMeasure_restrict_wordMap (w : List (Fin 8)) :
    carpetMeasure.restrict (range (wordMap w)) =
      ((8 : ℝ≥0∞)⁻¹) ^ w.length • carpetMeasure.map (wordMap w) := by
  ext A hA
  rw [Measure.restrict_apply hA, smul_apply, smul_eq_mul, (measurableEmbedding_wordMap w).map_apply,
    ← carpetMeasure_image_wordMap w (hA.preimage (measurableEmbedding_wordMap w).measurable),
    image_preimage_eq_inter_range]

/-- Transport a real integral to a word cell. -/
theorem setIntegral_wordMap_of_isLpPullback {p : ℝ} (w : List (Fin 8))
    {f g : CarpetLp p} (h : IsLpPullback (wordMap w) f g)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ x in range (wordMap w), φ (f x) ∂carpetMeasure) =
      ((8 : ℝ)⁻¹) ^ w.length * ∫ x, φ (g x) ∂carpetMeasure := by
  have hmap : AEStronglyMeasurable (φ ∘ (f : CarpetPoints → ℝ))
      (carpetMeasure.map (wordMap w)) :=
    hφ.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable f).mono_ac (SelfSimilarPEnergy.quasiMeasurePreserving_wordMap w).absolutelyContinuous)
  rw [carpetMeasure_restrict_wordMap, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_inv]
  norm_num only [ENNReal.toReal_ofNat, smul_eq_mul]
  congr 1
  exact (integral_map (continuous_wordMap w).measurable.aemeasurable hmap).trans
    (integral_congr_ae (h.mono fun x hx ↦ congrArg φ hx.symm))

/-- The p-th power of the carpet Lp norm is the integral of the p-th
power of the absolute value. -/
theorem integral_abs_rpow_eq_norm_rpow {p : ℝ} (hp : 0 < p) (f : CarpetLp p) :
    (∫ x, |f x| ^ p ∂carpetMeasure) = ‖f‖ ^ p := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top (Lp.aestronglyMeasurable f), ENNReal.toReal_ofReal hp.le]
  simp only [Real.norm_eq_abs]
  exact (Real.rpow_inv_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) hp.ne').symm

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The mean of the pullback, equal to the normalized cell average. -/
noncomputable def wordMean (w : List (Fin 8)) (f : E.domain) : ℝ :=
  ∫ x, (E.pullbackWord w f : CarpetLp p) x ∂carpetMeasure

theorem setIntegral_wordMap_eq_wordMean (w : List (Fin 8)) (f : E.domain) :
    (∫ x in range (wordMap w), (f : CarpetLp p) x ∂carpetMeasure) =
      ((8 : ℝ)⁻¹) ^ w.length * E.wordMean w f :=
  setIntegral_wordMap_of_isLpPullback w (E.pullbackWord_isLpPullback w f) continuous_id

/-- The cell Poincaré estimate (4.8), on the whole energy domain. -/
theorem exists_cell_poincare :
    ∃ C > (0 : ℝ), ∀ (w : List (Fin 8)) (f : E.domain),
      (∫ x in range (wordMap w), |(f : CarpetLp p) x - E.wordMean w f| ^ p ∂carpetMeasure) ≤
        C * ((8 : ℝ)⁻¹) ^ w.length * (E.energy (E.pullbackWord w f) : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨C, hC, hgap⟩ := E.exists_spectral_gap
  refine ⟨C, hC, fun w f ↦ ?_⟩
  let g := E.pullbackWord w f
  let a := E.wordMean w f
  let φ (t : ℝ) := |t - a| ^ p
  have hφ : Continuous φ := ((continuous_id.sub continuous_const).abs).rpow_const
    (fun _ ↦ Or.inr hp.le)
  have he : (∫ x, φ ((g : CarpetLp p) x) ∂carpetMeasure) =
      ‖(g : CarpetLp p) - constantLp p a‖ ^ p := by
    rw [← integral_abs_rpow_eq_norm_rpow hp]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (g : CarpetLp p) (constantLp p a),
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a] with x hx hy
    dsimp only [φ]
    rw [hx, Pi.sub_apply, show constantLp p a x = a from hy]
  calc
    _ = ((8 : ℝ)⁻¹) ^ w.length * ∫ x, φ ((g : CarpetLp p) x) ∂carpetMeasure :=
      setIntegral_wordMap_of_isLpPullback w (E.pullbackWord_isLpPullback w f) hφ
    _ ≤ ((8 : ℝ)⁻¹) ^ w.length * (C * (E.energy g : ℝ)) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left (hgap g) (by positivity)
    _ = _ := by ring

end SelfSimilarPEnergy
end CarpetEnergy
