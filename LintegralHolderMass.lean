import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# A moment bound with the mass of the underlying measure
-/

open MeasureTheory
open scoped ENNReal

namespace CarpetEnergy

theorem lintegral_rpow_le_mass_rpow_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ} (hp : 1 < p) {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ p ≤ μ Set.univ ^ (p - 1) * ∫⁻ x, f x ^ p ∂μ := by
  let q := p.conjExponent
  have h := Real.HolderConjugate.conjExponent hp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ h hf
    (aemeasurable_const : AEMeasurable (fun _ : X ↦ (1 : ℝ≥0∞)) μ)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul, one_div] at hh
  have hp₀ := zero_lt_one.trans hp
  have hpow := ENNReal.rpow_le_rpow hh hp₀.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp₀.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ hp₀.ne', ENNReal.rpow_one] at hpow
  have hq : q⁻¹ * p = p - 1 := by
    dsimp only [q, Real.conjExponent]
    rw [inv_div, div_mul_cancel₀ _ hp₀.ne']
  rwa [hq, mul_comm] at hpow

end CarpetEnergy
