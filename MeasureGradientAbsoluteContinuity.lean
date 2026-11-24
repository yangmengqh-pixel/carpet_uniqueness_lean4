import MeasureDerivativeTranslation
import SmoothEuclideanCutoff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Absolute continuity from bounded distributional derivatives

For a compact Haar-null set with positive measure, a smooth cutoff has
positive integral even under sufficiently small translations. Averaging
the translated cutoffs gives the opposite bound when their support has
arbitrarily small Haar measure.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CarpetEnergy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [HasContDiffBump V] [MeasurableSpace V] [BorelSpace V]

/-- The absolute-continuity step of Proposition 5.6, in distributional
form. A finite measure with bounded distributional first derivatives
is absolutely continuous with respect to additive Haar measure. -/
theorem absoluteContinuous_of_boundedDistributionalGradient (μ ν : Measure V)
    [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [ν.IsAddHaarMeasure] [ν.OuterRegular]
    {C : ℝ} (hC : 0 ≤ C) (hμ : HasBoundedDistributionalGradient μ C) :
    μ ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hνA
  by_contra hμA
  obtain ⟨K, hKA, hK, hKpos⟩ := hA.exists_lt_isCompact_of_ne_top (measure_ne_top μ A)
    (pos_iff_ne_zero.mpr hμA)
  have hKν : ν K = 0 := measure_mono_null hKA hνA
  let L := μ.real K
  have hL : 0 < L := ENNReal.toReal_pos hKpos.ne' (measure_ne_top μ K)
  let r := L / (2 * (C + 1))
  have hr : 0 < r := by dsimp only [r]; positivity
  let B := ball (0 : V) r
  have hB : MeasurableSet B := measurableSet_ball
  let η := ν.restrict B
  let : IsFiniteMeasure η := ⟨by
    dsimp only [η]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact measure_ball_lt_top⟩
  let b := ν.real B
  have hb : 0 < b := ENNReal.toReal_pos (measure_ball_pos ν 0 hr).ne' measure_ball_lt_top.ne
  let m := μ.real univ
  have hm : 0 < m := ENNReal.toReal_pos (hKpos.trans_le (measure_mono (subset_univ _))).ne'
    (measure_ne_top μ univ)
  let ε := (L / 2 * b) / (m + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨U, hKU, hU, hνU⟩ := K.exists_isOpen_lt_of_lt (μ := ν) (ENNReal.ofReal ε)
    (by rw [hKν]; exact ENNReal.ofReal_pos.mpr hε)
  have hνUfin : ν U ≠ ∞ := (hνU.trans ENNReal.ofReal_lt_top).ne
  have hUε : ν.real U < ε := by
    change (ν U).toReal < ε
    rw [← ENNReal.toReal_ofReal hε.le]
    exact ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hνU
  obtain ⟨φ, hφ, hφc, hφs, hφb, hφK⟩ := exists_smooth_cutoff_compact hK hU hKU
  let F (t x : V) := φ (x + t)
  have hF : Continuous (uncurry F) := hφ.continuous.comp (continuous_snd.add continuous_fst)
  have hi : Integrable (uncurry F) (η.prod μ) := Integrable.of_bound hF.aestronglyMeasurable 1
    (Eventually.of_forall fun z ↦ by
      change ‖φ (z.2 + z.1)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hφb _).1]
      exact (hφb _).2)
  have hi₀ : Integrable φ μ := Integrable.of_bound hφ.continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hφb x).1]; exact (hφb x).2)
  have hiK : L ≤ ∫ x, φ x ∂μ := by
    have hKi := (integrable_const (μ := μ) (1 : ℝ)).indicator hK.isClosed.measurableSet
    have h := integral_mono hKi hi₀ (fun x ↦ by
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx, hφK hx]
      · rw [indicator_of_notMem hx]; exact (hφb x).1)
    rw [integral_indicator hK.isClosed.measurableSet, integral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
    exact h
  have hlo (t : V) (ht : t ∈ B) : L / 2 ≤ ∫ x, F t x ∂μ := by
    have hd := hμ.abs_integral_translate_sub_le μ φ hφ hφc hφb t
    have hnorm : ‖t‖ ≤ r := by simpa only [B, mem_ball, dist_zero_right] using (show dist t 0 < r from ht).le
    have hbnd : C * r ≤ L / 2 := by
      dsimp only [r]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (show 0 < 2 * (C + 1) by positivity)).mpr
      nlinarith
    have h := (mul_le_mul_of_nonneg_left hnorm hC).trans hbnd
    have habs := (abs_le.mp (hd.trans h)).1
    change L / 2 ≤ ∫ x, φ (x + t) ∂μ
    linarith only [habs, hiK]
  have hlo' : L / 2 * b ≤ ∫ t, ∫ x, F t x ∂μ ∂η := by
    have h := integral_mono_ae (integrable_const (μ := η) (L / 2)) hi.integral_prod_left
      ((ae_restrict_mem hB).mono fun t ht ↦ hlo t ht)
    rw [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, mul_comm] at h
    exact h
  have hhi (x : V) : (∫ t, F t x ∂η) ≤ ν.real U := by
    let P := (fun t : V ↦ x + t) ⁻¹' U
    have hP : MeasurableSet P := hU.measurableSet.preimage (continuous_const.add continuous_id).measurable
    have hνP : ν P = ν U := by
      have hpres := measurePreserving_add_left ν x
      rw [← Measure.map_apply hpres.measurable hU.measurableSet, hpres.map_eq]
    have hxint : Integrable (fun t ↦ F t x) η :=
      Integrable.of_bound ((hφ.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
      1 (Eventually.of_forall fun t ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφb _).1]
        exact (hφb _).2)
    have hPint := (integrable_const (μ := η) (1 : ℝ)).indicator hP
    have hc := integral_mono hxint hPint (fun t ↦ by
      by_cases ht : t ∈ P
      · rw [indicator_of_mem ht]
        exact (hφb _).2
      · rw [indicator_of_notMem ht]
        by_contra! h
        exact ht (hφs (show x + t ∈ support φ from h.ne')))
    rw [integral_indicator hP, integral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter] at hc
    refine hc.trans (ENNReal.toReal_mono hνUfin ?_)
    exact (Measure.restrict_le_self _).trans_eq hνP
  have hhi' : (∫ x, ∫ t, F t x ∂η ∂μ) ≤ m * ν.real U := by
    have h := integral_mono hi.integral_prod_right (integrable_const (μ := μ) (ν.real U)) hhi
    rw [integral_const, smul_eq_mul] at h
    exact h
  rw [integral_integral_swap hi] at hlo'
  have hle := hlo'.trans hhi'
  have hlt : m * ν.real U < L / 2 * b := by
    apply (mul_lt_mul_of_pos_left hUε hm).trans
    dsimp only [ε]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show 0 < m + 1 by positivity)).mpr
    have hpos : 0 < L / 2 * b := by positivity
    nlinarith
  exact hlt.not_ge hle

end CarpetEnergy
