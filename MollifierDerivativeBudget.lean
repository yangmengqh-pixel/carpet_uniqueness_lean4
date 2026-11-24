import SmoothMollification
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Scaling and cancellation of the mollifier derivative
-/

open Filter Function Metric MeasureTheory Set
open scoped Convolution

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [HasContDiffBump X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
private theorem mollifierBump_apply_eq_dilation (n : ℕ) (x : X) :
    (mollifierBump n : ContDiffBump (0 : X)) x =
      (mollifierBump 0 : ContDiffBump (0 : X)) ((mollifierBump (X := X) n).rOut⁻¹ • x) := by
  let r := (mollifierBump (X := X) n).rOut
  have hr : 0 < r := (mollifierBump n).rOut_pos
  rw [ContDiffBump.apply, ContDiffBump.apply]
  have hIn : (mollifierBump (X := X) n).rIn = r / 2 := rfl
  have h0 : (mollifierBump (X := X) 0).rOut = 1 := by norm_num [mollifierBump]
  have h0' : (mollifierBump (X := X) 0).rIn = 1 / 2 := by norm_num [mollifierBump]
  rw [hIn, h0, h0', sub_zero, sub_zero, smul_smul]
  change (someContDiffBumpBase X).toFun (r / (r / 2)) ((r / 2)⁻¹ • x) =
    (someContDiffBumpBase X).toFun (1 / (1 / 2)) (((1 / 2)⁻¹ * r⁻¹) • x)
  have hratio : r / (r / 2) = 1 / (1 / 2) := by field_simp
  have hscale : (r / 2)⁻¹ = ((1 : ℝ) / 2)⁻¹ * r⁻¹ := by
    rw [inv_div, inv_div, div_eq_mul_inv]
    norm_num
  rw [hratio, hscale]

set_option maxHeartbeats 1700000 in
theorem mollifier_normed_eq_dilation (n : ℕ) :
    (mollifierBump (X := X) n).normed μ =
      fun x ↦ ((mollifierBump (X := X) n).rOut ^ Module.finrank ℝ X)⁻¹ *
        (mollifierBump 0).normed μ ((mollifierBump (X := X) n).rOut⁻¹ • x) := by
  let r := (mollifierBump (X := X) n).rOut
  let B := (mollifierBump 0 : ContDiffBump (0 : X))
  have hr : 0 < r := (mollifierBump n).rOut_pos
  have hpow := pow_pos hr (Module.finrank ℝ X)
  have hI : (∫ x, (mollifierBump n : ContDiffBump (0 : X)) x ∂μ) =
      r ^ Module.finrank ℝ X * ∫ x, B x ∂μ := by
    simp only [mollifierBump_apply_eq_dilation n]
    rw [Measure.integral_comp_inv_smul_of_nonneg μ B hr.le, smul_eq_mul]
  funext x
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, hI, mollifierBump_apply_eq_dilation n]
  change B (r⁻¹ • x) / (r ^ Module.finrank ℝ X * ∫ x, B x ∂μ) =
    (r ^ Module.finrank ℝ X)⁻¹ * (B (r⁻¹ • x) / ∫ x, B x ∂μ)
  rw [div_mul_eq_div_div, div_eq_mul_inv _ (r ^ Module.finrank ℝ X), mul_comm]
  ring

set_option maxHeartbeats 2200000 in
/-- The inverse radius is the entire scale dependence of the derivative
budget for normalized mollifiers. -/
theorem mul_integral_abs_fderiv_mollifier_eq (n : ℕ) (z : X) :
    (mollifierBump (X := X) n).rOut *
        (∫ x, |fderiv ℝ ((mollifierBump n).normed μ) x z| ∂μ) =
      ∫ x, |fderiv ℝ ((mollifierBump 0).normed μ) x z| ∂μ := by
  let r := (mollifierBump (X := X) n).rOut
  let K := (mollifierBump (X := X) 0).normed μ
  let J (x : X) := |fderiv ℝ K x z|
  let N := Module.finrank ℝ X
  have hr : 0 < r := (mollifierBump n).rOut_pos
  have hb := (mollifierBump (X := X) 0).contDiff_normed (μ := μ) (n := 1)
  have hd (x : X) : fderiv ℝ ((mollifierBump n).normed μ) x z =
      ((r ^ N)⁻¹ * r⁻¹) * fderiv ℝ K (r⁻¹ • x) z := by
    rw [mollifier_normed_eq_dilation]
    have hh := (((hb.differentiable (by norm_num) (r⁻¹ • x)).hasFDerivAt).comp x
      ((ContinuousLinearMap.id ℝ X).hasFDerivAt.const_smul r⁻¹)).const_mul (r ^ N)⁻¹
    change HasFDerivAt (fun y ↦ (r ^ N)⁻¹ * K (r⁻¹ • y)) _ x at hh
    change fderiv ℝ (fun y ↦ (r ^ N)⁻¹ * K (r⁻¹ • y)) x z = _
    rw [hh.fderiv, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, mul_assoc]
  have hn : 0 ≤ (r ^ N)⁻¹ * r⁻¹ := mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) (inv_nonneg.mpr hr.le)
  simp only [hd, abs_mul, abs_of_nonneg hn, integral_const_mul]
  change r * (((r ^ N)⁻¹ * r⁻¹) * ∫ x, J (r⁻¹ • x) ∂μ) = ∫ x, J x ∂μ
  rw [Measure.integral_comp_inv_smul_of_nonneg μ J hr.le, smul_eq_mul]
  field_simp [hr.ne']
  ring

theorem integral_fderiv_mollifier_eq_zero (n : ℕ) (z : X) :
    (∫ x, fderiv ℝ ((mollifierBump n).normed μ) x z ∂μ) = 0 := by
  let B := mollifierBump (X := X) n
  let K := B.normed μ
  have hs := B.hasCompactSupport_normed (μ := μ)
  have hK : ContDiff ℝ 1 K := B.contDiff_normed
  have hI : Integrable K μ := B.integrable_normed
  have hD : Integrable (fun x ↦ fderiv ℝ K x z) μ :=
    ((hK.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ z)
  have hz (x : X) : fderiv ℝ (fun _ : X ↦ (1 : ℝ)) x = 0 :=
    (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).fderiv
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (v := z)
    (f := fun _ ↦ (1 : ℝ)) (g := K)
    (by simp only [hz, zero_apply, zero_mul]; exact integrable_zero _ _ _)
    (by simpa only [one_mul] using hD)
    (by simpa only [one_mul] using hI)
    (fun _ _ ↦ differentiableAt_const _)
    (fun x _ ↦ hK.differentiable (by norm_num) x)
  simpa only [one_mul, hz, zero_apply, zero_mul, integral_zero, neg_zero] using h

end CarpetEnergy
