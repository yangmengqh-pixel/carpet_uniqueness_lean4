import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Strong moments from a truncated tail bound
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Interval

namespace CarpetEnergy

set_option maxHeartbeats 3500000 in
theorem lintegral_rpow_le_of_truncated_tail_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SigmaFinite μ] {p C : ℝ} (hp : 1 < p) (hC : 0 ≤ C)
    {f F : X → ℝ} (hf : Measurable f) (hF : Measurable F)
    (hf₀ : ∀ x, 0 ≤ f x) (hF₀ : ∀ x, 0 ≤ F x)
    (hTail : ∀ t > (0 : ℝ), μ {x | t < F x} ≤ ENNReal.ofReal (C / t) *
      ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal (f x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) ≤
      ENNReal.ofReal (C * (p / (p - 1)) * 2 ^ (p - 1)) *
        ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let G (t : ℝ) := p * t ^ (p - 1)
  let H (t : ℝ) := C * p * t ^ (p - 2)
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hG : Continuous G := continuous_const.mul (Real.continuous_rpow_const (sub_nonneg.mpr hp.le))
  have hG₀ (t : ℝ) (ht : 0 < t) : 0 ≤ G t := mul_nonneg hp₀.le (Real.rpow_nonneg ht.le _)
  have hGi (t : ℝ) (ht : 0 ≤ t) : ∫ s in 0..t, G s = t ^ p := by
    dsimp only [G]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < p - 1)),
      sub_add_cancel, Real.zero_rpow hp₀.ne', sub_zero, mul_div_cancel₀ _ hp₀.ne']
  have hLayer := lintegral_comp_eq_lintegral_meas_lt_mul μ (Eventually.of_forall hF₀) hF.aemeasurable
    (fun t _ ↦ hG.intervalIntegrable 0 t)
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦ hG₀ t ht)
  simp_rw [hGi _ (hF₀ _)] at hLayer
  let A (x : X) := Iio (2 * f x)
  let W (t : ℝ) (x : X) := (A x).indicator (fun _ ↦ ENNReal.ofReal (H t * f x)) t
  have hMeas : Measurable (uncurry W) := by
    have hS : MeasurableSet {y : ℝ × X | y.1 < 2 * f y.2} :=
      measurableSet_lt measurable_fst (measurable_const.mul (hf.comp measurable_snd))
    have hHm : Measurable H := measurable_const.mul
      (measurable_of_continuousOn_compl_singleton 0 fun t ht ↦
        (Real.continuousAt_rpow_const t (p - 2) (Or.inl ht)).continuousWithinAt)
    have hh : Measurable (fun y : ℝ × X ↦ ENNReal.ofReal (H y.1 * f y.2)) :=
      ((hHm.comp measurable_fst).mul (hf.comp measurable_snd)).ennreal_ofReal
    convert hh.indicator hS using 1
    funext y
    simp only [W, uncurry, A, Set.indicator, mem_Iio, mem_ofPred_eq]
  have hPoint (t : ℝ) (ht : 0 < t) :
      μ {x | t < F x} * ENNReal.ofReal (G t) ≤ ∫⁻ x, W t x ∂μ := by
    have hcoeff : ENNReal.ofReal (C / t) * ENNReal.ofReal (G t) = ENNReal.ofReal (H t) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hC ht.le)]
      congr 1
      dsimp only [G, H]
      have hh : t ^ (p - 1) / t = t ^ (p - 2) := by
        calc
          _ = t ^ (p - 1) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub ht, show p - 1 - 1 = p - 2 by ring]
      calc
        _ = C * p * (t ^ (p - 1) / t) := by ring
        _ = _ := by rw [hh]
    calc
      _ ≤ (ENNReal.ofReal (C / t) * (∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal (f x) ∂μ)) *
          ENNReal.ofReal (G t) := mul_le_mul_of_nonneg_right (hTail t ht) bot_le
      _ = ENNReal.ofReal (H t) * (∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal (f x) ∂μ) := by
        rw [← hcoeff]
        ac_rfl
      _ = _ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator
          (measurableSet_lt measurable_const hf)]
        apply lintegral_congr
        intro x
        have hx : t / 2 < f x ↔ t < 2 * f x := by
          constructor <;> intro h <;> linarith only [h]
        by_cases ht' : t < 2 * f x
        · rw [indicator_of_mem (show x ∈ {x | t / 2 < f x} from hx.mpr ht')]
          change ENNReal.ofReal (H t) * ENNReal.ofReal (f x) = (A x).indicator _ t
          rw [indicator_of_mem (show t ∈ A x from ht'), ← ENNReal.ofReal_mul (by dsimp only [H]; positivity)]
        · rw [indicator_of_notMem (show x ∉ {x | t / 2 < f x} from fun h ↦ ht' (hx.mp h))]
          exact (indicator_of_notMem (show t ∉ A x from ht') _).symm
  have hFinal (x : X) : (∫⁻ t, W t x ∂ν) =
      ENNReal.ofReal (C * (p / (p - 1)) * 2 ^ (p - 1) * f x ^ p) := by
    have hA : MeasurableSet (A x) := measurableSet_Iio
    change ∫⁻ t, (A x).indicator (fun t ↦ ENNReal.ofReal (H t * f x)) t ∂ν = _
    rw [lintegral_indicator hA, Measure.restrict_restrict hA]
    have hset : A x ∩ Ioi 0 = Ioo 0 (2 * f x) := Iio_inter_Ioi
    rw [hset]
    have hI : IntervalIntegrable (fun t : ℝ ↦ t ^ (p - 2)) volume 0 (2 * f x) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p - 2)
    have h2 : 0 ≤ 2 * f x := mul_nonneg (by norm_num) (hf₀ x)
    have hIo : Integrable (fun t ↦ H t * f x) (volume.restrict (Ioc 0 (2 * f x))) := by
      exact (hI.1.const_mul (C * p)).mul_const _
    have heq : (volume : Measure ℝ).restrict (Ioo 0 (2 * f x)) =
        volume.restrict (Ioc 0 (2 * f x)) := by
      exact Measure.restrict_congr_set Ioo_ae_eq_Ioc
    rw [heq, ← ofReal_integral_eq_lintegral_ofReal hIo]
    · rw [← intervalIntegral.integral_of_le h2]
      dsimp only [H]
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : -1 < p - 2)),
        show p - 2 + 1 = p - 1 by ring, Real.zero_rpow (sub_pos.mpr hp).ne',
        sub_zero, Real.mul_rpow (by norm_num) (hf₀ x)]
      congr 1
      have hm : f x ^ (p - 1) * f x = f x ^ p := by
        have hh := Real.rpow_add_of_nonneg (hf₀ x) (sub_nonneg.mpr hp.le) (zero_le_one : (0 : ℝ) ≤ 1)
        rwa [sub_add_cancel, Real.rpow_one, eq_comm] at hh
      calc
        _ = C * (p / (p - 1)) * 2 ^ (p - 1) * (f x ^ (p - 1) * f x) := by ring
        _ = _ := by rw [hm]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (mul_nonneg (mul_nonneg hC hp₀.le) (Real.rpow_nonneg ht.1.le _)) (hf₀ x)
  rw [hLayer]
  calc
    _ ≤ ∫⁻ t, ∫⁻ x, W t x ∂μ ∂ν := lintegral_mono_ae
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦ hPoint t ht)
    _ = ∫⁻ x, ∫⁻ t, W t x ∂ν ∂μ := lintegral_lintegral_swap hMeas.aemeasurable
    _ = _ := by
      simp only [hFinal, ENNReal.ofReal_mul (show 0 ≤ C * (p / (p - 1)) * 2 ^ (p - 1) by positivity)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end CarpetEnergy
