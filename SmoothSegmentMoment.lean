import SmoothTranslationLp

/-!
# A derivative moment controlling the increment along a segment
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

set_option maxHeartbeats 2500000 in
/-- A segment increment is bounded by its length and the mean derivative
moment along the segment. -/
theorem abs_sub_rpow_le_segment_fderiv_moment {p : ℝ} (hp : 1 ≤ p)
    {f : X → ℝ} (hf : ContDiff ℝ 1 f) (x y : X) :
    |f y - f x| ^ p ≤ ‖y - x‖ ^ p *
      ∫ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x + t • (y - x))‖ ^ p := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]⟩
  let z := y - x
  let P (t : ℝ) := x + t • z
  let d (t : ℝ) := fderiv ℝ f (P t) z
  let D (t : ℝ) := ‖fderiv ℝ f (P t)‖ ^ p
  have hP : Continuous P := continuous_const.add (continuous_id.smul continuous_const)
  have hF : Continuous (fun t ↦ fderiv ℝ f (P t)) := (hf.continuous_fderiv (by norm_num)).comp hP
  have hd : Continuous d := hF.clm_apply continuous_const
  have hp₀ : 0 ≤ p := zero_le_one.trans hp
  have hD : Continuous D := hF.norm.rpow_const (fun _ ↦ Or.inr hp₀)
  have hI {g : ℝ → ℝ} (hg : Continuous g) : Integrable g ν :=
    hg.continuousOn.integrableOn_compact (K := Icc (0 : ℝ) 1) isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  have hpath (t : ℝ) : HasDerivAt P z t := by
    simpa only [one_smul, id_eq, P] using ((hasDerivAt_id t).smul_const z).const_add x
  have hφ (t : ℝ) : HasDerivAt (f ∘ P) (d t) t :=
    ((hf.differentiable (by norm_num) (P t)).hasFDerivAt.comp_hasDerivAt t (hpath t))
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hφ t)
    (hd.intervalIntegrable (0 : ℝ) 1)
  rw [intervalIntegral.integral_of_le zero_le_one] at hft
  have hft' : (∫ t, d t ∂ν) = f y - f x := by
    simpa only [Function.comp_apply, P, z, one_smul, zero_smul, add_zero, add_sub_cancel] using hft
  have hA : |f y - f x| ≤ ∫ t, |d t| ∂ν := by
    rw [← hft']
    exact abs_integral_le_integral_abs
  have hJ := (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const hp₀).continuousOn isClosed_Ici
    (Eventually.of_forall fun t ↦ (abs_nonneg (d t) : 0 ≤ |d t|))
    (hI hd.abs) (hI (hd.abs.rpow_const (fun _ ↦ Or.inr hp₀)))
  refine (Real.rpow_le_rpow (abs_nonneg _) hA hp₀).trans (hJ.trans ?_)
  change (∫ t, |d t| ^ p ∂ν) ≤ ‖z‖ ^ p * ∫ t, D t ∂ν
  rw [← integral_const_mul]
  apply integral_mono (hI (hd.abs.rpow_const (fun _ ↦ Or.inr hp₀))) ((hI hD).const_mul _)
  intro t
  change |fderiv ℝ f (P t) z| ^ p ≤ ‖z‖ ^ p * ‖fderiv ℝ f (P t)‖ ^ p
  rw [mul_comm, ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← Real.norm_eq_abs]
  exact Real.rpow_le_rpow (norm_nonneg _) ((fderiv ℝ f (P t)).le_opNorm z) hp₀

end CarpetEnergy
