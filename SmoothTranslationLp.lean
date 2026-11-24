import SmoothMollification
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Translation estimates from a directional derivative
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [μ.IsAddHaarMeasure]

set_option maxHeartbeats 2200000 in
/-- The (p)-moment of a translation difference of a smooth scalar
function is bounded by the moment of its derivative in the translation
direction. -/
theorem integral_abs_translation_sub_rpow_le_of_contDiff {p : ℝ} (hp : 1 ≤ p)
    {f : X → ℝ} (hf : ContDiff ℝ 1 f) (z : X)
    (hD : Integrable (fun x ↦ |fderiv ℝ f x z| ^ p) μ) :
    Integrable (fun x ↦ |f (x + z) - f x| ^ p) μ ∧
      (∫ x, |f (x + z) - f x| ^ p ∂μ) ≤ ∫ x, |fderiv ℝ f x z| ^ p ∂μ := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]⟩
  let d (x : X) := fderiv ℝ f x z
  let D (x : X) := |d x| ^ p
  have hd : Continuous d := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDc : Continuous D := hd.abs.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hp)
  have hD₀ (x : X) : 0 ≤ D x := Real.rpow_nonneg (abs_nonneg _) _
  let P (x : X) (t : ℝ) := x + t • z
  have hcont (x : X) : Continuous (P x) := continuous_const.add (continuous_id.smul continuous_const)
  have hI (x : X) (g : X → ℝ) (hg : Continuous g) : Integrable (g ∘ P x) ν :=
    (hg.comp (hcont x)).continuousOn.integrableOn_compact (K := Icc (0 : ℝ) 1) isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  let F (x : X) (t : ℝ) := D (P x t)
  have hpoint (x : X) : |f (x + z) - f x| ^ p ≤ ∫ t, F x t ∂ν := by
    have hpath (t : ℝ) : HasDerivAt (P x) z t := by
      simpa only [one_smul, id_eq, P] using ((hasDerivAt_id t).smul_const z).const_add x
    have hdd (t : ℝ) : HasDerivAt (f ∘ P x) (d (P x t)) t :=
      ((hf.differentiable (by norm_num) (P x t)).hasFDerivAt.comp_hasDerivAt t (hpath t))
    have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hdd t) ((hd.comp (hcont x)).intervalIntegrable (0 : ℝ) 1)
    rw [intervalIntegral.integral_of_le zero_le_one] at hft
    have hft' : (∫ t, d (P x t) ∂ν) = f (x + z) - f x := by
      simpa only [Function.comp_apply, P, one_smul, zero_smul, add_zero] using hft
    have hM : |f (x + z) - f x| ≤ ∫ t, |d (P x t)| ∂ν := by
      rw [← hft']
      exact abs_integral_le_integral_abs
    have hJ := (convexOn_rpow hp).map_integral_le
      (Real.continuous_rpow_const (zero_le_one.trans hp)).continuousOn isClosed_Ici
      (Eventually.of_forall fun t ↦ (abs_nonneg (d (P x t)) : 0 ≤ |d (P x t)|))
      (hI x d hd).abs (hI x D hDc)
    exact (Real.rpow_le_rpow (abs_nonneg _) hM (zero_le_one.trans hp)).trans hJ
  have hFP : Continuous (uncurry F) := hDc.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hDtr (t : ℝ) : Integrable (fun x ↦ F x t) μ := hD.comp_add_right _
  have hconst (t : ℝ) : (∫ x, F x t ∂μ) = ∫ x, D x ∂μ := integral_add_right_eq_self D (t • z)
  have hFPi : Integrable (uncurry F) (μ.prod ν) := by
    apply (integrable_prod_iff' hFP.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hDtr, ?_⟩
    have hEq : (fun t ↦ ∫ x, ‖F x t‖ ∂μ) = fun _ ↦ ∫ x, D x ∂μ := by
      funext t
      simp only [Real.norm_eq_abs, abs_of_nonneg (hD₀ _), F] at *
      exact hconst t
    change Integrable (fun t ↦ ∫ x, ‖F x t‖ ∂μ) ν
    rw [hEq]
    exact integrable_const _
  have hMr (x : X) : 0 ≤ ∫ t, F x t ∂ν := integral_nonneg fun t ↦ hD₀ _
  have hA : Integrable (fun x ↦ |f (x + z) - f x| ^ p) μ := by
    have hM : Continuous (fun x ↦ |f (x + z) - f x| ^ p) :=
      ((hf.continuous.comp (continuous_id.add (continuous_const (y := z)))).sub hf.continuous).abs.rpow_const
      (fun _ ↦ Or.inr (zero_le_one.trans hp))
    apply (hFPi.integral_prod_left).mono hM.aestronglyMeasurable
    exact Eventually.of_forall (fun x ↦ by
      change ‖|f (x + z) - f x| ^ p‖ ≤ ‖∫ t, F x t ∂ν‖
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        Real.norm_eq_abs, abs_of_nonneg (hMr x)]
      exact hpoint x)
  refine ⟨hA, (integral_mono hA hFPi.integral_prod_left hpoint).trans_eq ?_⟩
  change (∫ x, ∫ t, F x t ∂ν ∂μ) = ∫ x, D x ∂μ
  rw [integral_integral_swap hFPi]
  simp only [hconst, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

end CarpetEnergy
