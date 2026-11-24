import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Translating smooth test integrals

A uniform bound on the distributional derivatives controls how a
finite measure integrates translated smooth tests. The proof follows
the line segment of translations and differentiates under the integral.
-/

open Filter Function MeasureTheory Metric Set
open scoped Topology

namespace CarpetEnergy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A measure whose distributional gradient acts on smooth compactly
supported tests with a uniform bound. -/
def HasBoundedDistributionalGradient [MeasurableSpace V] (μ : Measure V) (C : ℝ) : Prop :=
  ∀ (φ : V → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∀ v : V,
      |∫ x, fderiv ℝ φ x v ∂μ| ≤ C * ‖v‖

omit [NormedSpace ℝ V] in
private theorem hasCompactSupport_translate (φ : V → ℝ) (hφ : HasCompactSupport φ) (u : V) :
    HasCompactSupport (fun x ↦ φ (x + u)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hφ.image (continuous_id.sub continuous_const : Continuous (fun x : V ↦ x - u)))
  intro x hx
  exact ⟨x + u, subset_tsupport φ hx, add_sub_cancel_right x u⟩

private theorem fderiv_translate (φ : V → ℝ) (hφ : Differentiable ℝ φ) (x u : V) :
    fderiv ℝ (fun y ↦ φ (y + u)) x = fderiv ℝ φ (x + u) := by
  have ht := (hasFDerivAt_id (𝕜 := ℝ) x).add_const u
  have hc := (hφ (x + u)).hasFDerivAt.comp x ht
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using hc.fderiv

theorem HasBoundedDistributionalGradient.abs_integral_translate_sub_le
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasure μ] {C : ℝ}
    (hμ : HasBoundedDistributionalGradient μ C)
    (φ : V → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (h01 : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (v : V) :
    |(∫ x, φ (x + v) ∂μ) - ∫ x, φ x ∂μ| ≤ C * ‖v‖ := by
  let F (t : ℝ) (x : V) := φ (x + t • v)
  let D (t : ℝ) (x : V) := fderiv ℝ φ (x + t • v) v
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hDf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  obtain ⟨B, hB⟩ := hDf.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  have hFcont (t : ℝ) : Continuous (F t) := hφ.continuous.comp (continuous_id.add continuous_const)
  have hDcont (t : ℝ) : Continuous (D t) :=
    (hDf.clm_apply continuous_const).comp (continuous_id.add continuous_const)
  have hFint (t : ℝ) : Integrable (F t) μ := Integrable.of_bound (hFcont t).aestronglyMeasurable 1
    (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (h01 _).1]
      exact (h01 _).2)
  have hpoint (t : ℝ) (x : V) : HasDerivAt (fun s ↦ F s x) (D t x) t := by
    have hline : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
    exact (hdφ _).hasFDerivAt.comp_hasDerivAt t hline
  have hdiff (t : ℝ) : HasDerivAt (fun s ↦ ∫ x, F s x ∂μ) (∫ x, D t x ∂μ) t := by
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := F) (F' := D) (bound := fun _ ↦ B * ‖v‖) (s := univ) univ_mem
      (Eventually.of_forall fun s ↦ (hFcont s).aestronglyMeasurable) (hFint t)
      (hDcont t).aestronglyMeasurable
      (Eventually.of_forall fun x s _ ↦ (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)))
      (integrable_const _) (Eventually.of_forall fun x s _ ↦ hpoint s x)).2
  have hb (t : ℝ) : ‖∫ x, D t x ∂μ‖ ≤ C * ‖v‖ := by
    let ψ (x : V) := φ (x + t • v)
    have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.add contDiff_const)
    have ht := hμ ψ hψ (hasCompactSupport_translate φ hc _) (fun _ ↦ h01 _) v
    simp only [Real.norm_eq_abs, D]
    exact (show (∫ x, fderiv ℝ φ (x + t • v) v ∂μ) = ∫ x, fderiv ℝ ψ x v ∂μ from
      integral_congr_ae (Eventually.of_forall fun x ↦ congrArg (fun T : V →L[ℝ] ℝ ↦ T v)
        (fderiv_translate φ hdφ x (t • v)).symm)) ▸ ht
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ ↦ (hdiff t).hasDerivWithinAt) (fun t _ ↦ hb t)
  simpa only [Real.norm_eq_abs, F, one_smul, zero_smul, add_zero] using h

end CarpetEnergy
