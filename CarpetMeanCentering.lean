import EnergyNeighborhoodPoincare
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Changing a centering constant to the mean of a carpet region
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

open SelfSimilarPEnergy

theorem measureReal_mul_abs_setAverage_sub_rpow_le {p : ℝ} (hp : 1 ≤ p)
    (u : CarpetLp p) {B : Set CarpetPoints} (hB : carpetMeasure B ≠ 0) (c : ℝ) :
    carpetMeasure.real B * |(⨍ x in B, u x ∂carpetMeasure) - c| ^ p ≤
      ∫ x in B, |u x - c| ^ p ∂carpetMeasure := by
  have hp₀ := zero_lt_one.trans_le hp
  let m := ⨍ x in B, u x ∂carpetMeasure
  let M := carpetMeasure.real B
  let J := ∫ x in B, |u x - c| ^ p ∂carpetMeasure
  have hM : 0 < M := ENNReal.toReal_pos hB (measure_ne_top _ _)
  have hU : Integrable u carpetMeasure := memLp_one_iff_integrable.mp
    ((Lp.memLp u).mono_exponent (ENNReal.one_le_ofReal.mpr hp))
  have hInt : IntegrableOn (fun x ↦ u x - c) B carpetMeasure :=
    (hU.sub (integrable_const _)).integrableOn
  have hJ : IntegrableOn (fun x ↦ |u x - c| ^ p) B carpetMeasure :=
    (integrable_abs_sub_const_rpow hp₀ u c).integrableOn
  have hmean : (⨍ x in B, u x - c ∂carpetMeasure) = m - c := by
    have h := setAverage_sub (s := B) hU.integrableOn (integrable_const c).integrableOn
    simpa only [Pi.sub_apply, setAverage_const hB (measure_ne_top _ _), m] using h
  have hA : |m - c| ≤ ⨍ x in B, |u x - c| ∂carpetMeasure := by
    rw [← hmean, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hM.le)]
    exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs)
      (inv_nonneg.mpr hM.le)
  have hJensen := (convexOn_rpow hp).map_set_average_le
    (Real.continuous_rpow_const hp₀.le).continuousOn isClosed_Ici hB (measure_ne_top _ _)
    (Eventually.of_forall fun x ↦ (abs_nonneg (u x - c) : 0 ≤ |u x - c|)) hInt.abs hJ
  have hh := (Real.rpow_le_rpow (abs_nonneg _) hA hp₀.le).trans hJensen
  rw [setAverage_eq, smul_eq_mul] at hh
  exact (le_inv_mul_iff₀ hM).mp hh

set_option maxHeartbeats 1950000 in
theorem integral_abs_sub_setAverage_rpow_le {p : ℝ} (hp : 1 ≤ p)
    (u : CarpetLp p) {B : Set CarpetPoints} (hB : carpetMeasure B ≠ 0) (c : ℝ) :
    ∫ x in B, |u x - (⨍ y in B, u y ∂carpetMeasure)| ^ p ∂carpetMeasure ≤
      (2 : ℝ) ^ p * ∫ x in B, |u x - c| ^ p ∂carpetMeasure := by
  have hp₀ := zero_lt_one.trans_le hp
  let m := ⨍ x in B, u x ∂carpetMeasure
  let J := ∫ x in B, |u x - c| ^ p ∂carpetMeasure
  have hmeanp := measureReal_mul_abs_setAverage_sub_rpow_le hp u hB c
  have hJ : IntegrableOn (fun x ↦ |u x - c| ^ p) B carpetMeasure :=
    (integrable_abs_sub_const_rpow hp₀ u c).integrableOn
  let T := (2 : ℝ) ^ (p - 1)
  have hI : IntegrableOn (fun x ↦ |u x - m| ^ p) B carpetMeasure :=
    (integrable_abs_sub_const_rpow hp₀ u m).integrableOn
  have hconst : Integrable (fun _ : CarpetPoints ↦ |m - c| ^ p)
      (carpetMeasure.restrict B) := integrable_const _
  have hPT := integral_mono hI ((hJ.add hconst).const_mul T)
    (fun x ↦ by
      change |u x - m| ^ p ≤ T * (|u x - c| ^ p + |m - c| ^ p)
      rw [abs_sub_comm m c]
      exact abs_sub_rpow_le hp (u x) c m)
  change (∫ x in B, |u x - m| ^ p ∂carpetMeasure) ≤
    ∫ x in B, T * (|u x - c| ^ p + |m - c| ^ p) ∂carpetMeasure at hPT
  rw [integral_const_mul, integral_add hJ hconst,
    integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hPT
  have hT : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hcoef : T * 2 = (2 : ℝ) ^ p := by
    calc
      T * 2 = (2 : ℝ) ^ (p - 1) * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), sub_add_cancel]
  exact hPT.trans ((mul_le_mul_of_nonneg_left (add_le_add_right hmeanp J) hT).trans_eq (by
    rw [← two_mul J, ← mul_assoc, hcoef]))

end CarpetEnergy
