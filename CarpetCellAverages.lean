import CarpetWordIntegral
import CarpetNeighborhoodMass
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Cell averages for the discrete energies

A word cell's normalized average is integration against the pushforward
probability. Jensen's inequality gives the cell p-moment bound used to
control the discrete averaging and lifting operators.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

open SelfSimilarPEnergy

theorem carpetMeasure_carpetOuterBoundary_eq_zero :
    carpetMeasure carpetOuterBoundary = 0 := by
  apply measure_iUnion_null
  intro j
  apply measure_iUnion_null
  intro a
  exact carpetMeasure_coordinateLevel j a.val

theorem carpetMeasure_carpetCellBoundary_eq_zero (n : ℕ) :
    carpetMeasure (carpetCellBoundary n) = 0 := by
  apply measure_iUnion_null
  intro w
  rw [carpetMeasure_image_wordMap _ measurableSet_carpetOuterBoundary,
    carpetMeasure_carpetOuterBoundary_eq_zero, mul_zero]

theorem carpetMeasure_map_wordMap (w : List (Fin 8)) :
    carpetMeasure.map (wordMap w) =
      (8 : ℝ≥0∞) ^ w.length • carpetMeasure.restrict (range (wordMap w)) := by
  have h : (8 : ℝ≥0∞) ^ w.length ≠ 0 := pow_ne_zero _ (by norm_num)
  have h' : (8 : ℝ≥0∞) ^ w.length ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
  rw [carpetMeasure_restrict_wordMap, ← ENNReal.inv_pow, smul_smul, ENNReal.mul_inv_cancel h h', one_smul]

/-- A cell mean, viewed as a continuous linear functional on the ambient Lp space. -/
noncomputable def ambientWordMean (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (w : List (Fin 8)) :
    CarpetLp p →L[ℝ] ℝ :=
  ((8 : ℝ) ^ w.length) • lpSetIntegral (range (wordMap w))

theorem ambientWordMean_eq_integral {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (w : List (Fin 8)) (f : CarpetLp p) :
    ambientWordMean p w f = ∫ x, f x ∂carpetMeasure.map (wordMap w) := by
  rw [carpetMeasure_map_wordMap, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  rfl

/-- The average on a word cell has p-moment at most the average p-moment. -/
theorem ambientWordMean_abs_rpow_le {p : ℝ} (hp : 1 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)]
    (w : List (Fin 8)) (f : CarpetLp p) :
    |ambientWordMean p w f| ^ p ≤ (8 : ℝ) ^ w.length *
      ∫ x in range (wordMap w), |f x| ^ p ∂carpetMeasure := by
  let μ := carpetMeasure.map (wordMap w)
  have hm : AEMeasurable (wordMap w) carpetMeasure := (continuous_wordMap _).measurable.aemeasurable
  have : IsProbabilityMeasure μ := ⟨by rw [Measure.map_apply_of_aemeasurable hm MeasurableSet.univ,
    preimage_univ, measure_univ]⟩
  have hLp : MemLp f (ENNReal.ofReal p) μ := by
    dsimp only [μ]
    rw [carpetMeasure_map_wordMap]
    exact ((Lp.memLp f).restrict _).smul_measure (ENNReal.pow_ne_top (by norm_num))
  have hpos : 0 < p := zero_lt_one.trans_le hp
  have hi : Integrable f μ := memLp_one_iff_integrable.mp
    (hLp.mono_exponent (ENNReal.one_le_ofReal.mpr hp))
  have hI : Integrable (fun x ↦ |f x| ^ p) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hpos.le] using
      hLp.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hpos) ENNReal.ofReal_ne_top
  have hj := (convexOn_rpow hp).map_integral_le
    ((Real.continuous_rpow_const hpos.le).continuousOn) isClosed_Ici
    (Eventually.of_forall fun x ↦ (abs_nonneg (f x) : 0 ≤ |f x|))
    (by simpa only [Real.norm_eq_abs] using hi.norm) hI
  have h₀ : 0 ≤ ∫ x, |f x| ∂μ := integral_nonneg fun _ ↦ abs_nonneg _
  have ha : |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
  rw [ambientWordMean_eq_integral]
  calc
    _ ≤ (∫ x, |f x| ∂μ) ^ p := Real.rpow_le_rpow (abs_nonneg _) ha hpos.le
    _ ≤ ∫ x, |f x| ^ p ∂μ := hj
    _ = _ := by
      dsimp only [μ]
      rw [carpetMeasure_map_wordMap, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
        smul_eq_mul]

end CarpetEnergy
