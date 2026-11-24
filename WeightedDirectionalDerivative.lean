import LinearFunctionalExtension
import LpFunctionalDensity
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Weighted representation of distributional derivatives

A derivative bound on compactly supported C¹ tests defines a
functional on their Lq classes. It extends to Lq and consequently
has a representing Lp density with respect to the original measure.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]

/-- The real linear space of compactly supported C¹ scalar tests. -/
def compactC1Tests (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    Submodule ℝ (X → ℝ) where
  carrier := {f | ContDiff ℝ 1 f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_zero_fun, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' _ _ hf := ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

private theorem memLp_compactC1Test (μ : Measure X) [IsFiniteMeasure μ] (q : ℝ≥0∞)
    (u : compactC1Tests X) : MemLp u.val q μ := by
  have h : ContDiff ℝ 1 u.val ∧ HasCompactSupport u.val := u.property
  obtain ⟨B, hB⟩ := h.2.exists_bound_of_continuous h.1.continuous
  exact MemLp.of_bound h.1.continuous.aestronglyMeasurable B (Eventually.of_forall hB)

private noncomputable def compactC1TestToLp (μ : Measure X) [IsFiniteMeasure μ] (q : ℝ≥0∞) :
    compactC1Tests X →ₗ[ℝ] Lp ℝ q μ where
  toFun u := (memLp_compactC1Test μ q u).toLp u.val
  map_add' u v := MemLp.toLp_add (memLp_compactC1Test μ q u) (memLp_compactC1Test μ q v)
  map_smul' c u := MemLp.toLp_const_smul c (memLp_compactC1Test μ q u)

private theorem compactC1Test_deriv_integrable (μ : Measure X) [IsFiniteMeasure μ] (v : X)
    (u : compactC1Tests X) : Integrable (fun x ↦ fderiv ℝ u.val x v) μ := by
  have h : ContDiff ℝ 1 u.val ∧ HasCompactSupport u.val := u.property
  exact ((h.1.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.fderiv_apply ℝ h.2 v)

private noncomputable def directionalTestIntegral (μ : Measure X) [IsFiniteMeasure μ] (v : X) :
    compactC1Tests X →ₗ[ℝ] ℝ where
  toFun u := ∫ x, fderiv ℝ u.val x v ∂μ
  map_add' u w := by
    have hu : ContDiff ℝ 1 u.val := u.property.1
    have hw : ContDiff ℝ 1 w.val := w.property.1
    change (∫ x, fderiv ℝ (u.val + w.val) x v ∂μ) =
      (∫ x, fderiv ℝ u.val x v ∂μ) + ∫ x, fderiv ℝ w.val x v ∂μ
    simp_rw [fderiv_add (hu.differentiable (by norm_num) _)
      (hw.differentiable (by norm_num) _), add_apply,
      integral_add (compactC1Test_deriv_integrable μ v u) (compactC1Test_deriv_integrable μ v w)]
  map_smul' c u := by
    change (∫ x, fderiv ℝ (c • u.val) x v ∂μ) = c * ∫ x, fderiv ℝ u.val x v ∂μ
    simp_rw [fderiv_const_smul_field, Pi.smul_apply, smul_apply, smul_eq_mul, integral_const_mul]

set_option maxHeartbeats 1600000 in
theorem exists_weighted_directional_derivative_density (μ : Measure X) [IsFiniteMeasure μ]
    {p q C : ℝ} (hpq : p.HolderConjugate q) (hC : 0 ≤ C) (v : X)
    (h : ∀ φ : X → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      |∫ x, fderiv ℝ φ x v ∂μ| ≤ C * (∫ x, |φ x| ^ q ∂μ) ^ q⁻¹) :
    ∃ a : X → ℝ, Measurable a ∧ MemLp a (ENNReal.ofReal p) μ ∧
      ∀ φ : X → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ x, fderiv ℝ φ x v ∂μ) = ∫ x, a x * φ x ∂μ := by
  have hq : 0 < q := zero_lt_one.trans hpq.symm.lt
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
  let T := compactC1TestToLp μ (ENNReal.ofReal q)
  let F := directionalTestIntegral μ v
  have hF (u : compactC1Tests X) : ‖F u‖ ≤ C * ‖T u‖ := by
    have hu : ContDiff ℝ 1 u.val ∧ HasCompactSupport u.val := u.property
    change ‖∫ x, fderiv ℝ u.val x v ∂μ‖ ≤
      C * ‖(memLp_compactC1Test μ (ENNReal.ofReal q) u).toLp u.val‖
    rw [Lp.norm_toLp, toReal_eLpNorm,
      lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
        hu.1.continuous.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
    simp only [Real.norm_eq_abs]
    exact h u.val hu.1 hu.2
  obtain ⟨L, _, hL⟩ := exists_continuousLinearMap_factor_of_bound T F hC hF
  obtain ⟨a, ha, haLp, haRep⟩ := exists_memLp_density_of_LpFunctional hpq L
  refine ⟨a, ha, haLp, fun φ hφ hφs ↦ ?_⟩
  obtain ⟨B, hB⟩ := hφs.exists_bound_of_continuous hφ.continuous
  have hB' (x : X) : |φ x| ≤ max B 0 := by
    rw [← Real.norm_eq_abs]
    exact (hB x).trans (le_max_left _ _)
  let u : compactC1Tests X := ⟨φ, hφ, hφs⟩
  exact (hL u).symm.trans (haRep φ hφ.continuous.measurable (max B 0) (le_max_right _ _) hB')

end CarpetEnergy
