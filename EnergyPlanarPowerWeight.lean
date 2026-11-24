import EnergyWeightedPlanarRows
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The weighted test norm for the planar pushforward
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy

/-- Weight a carpet measure by the p-th power of a scalar cutoff. -/
noncomputable def powerWeightedMeasure (p : ℝ) (μ : Measure CarpetPoints)
    (χ : C(CarpetPoints, ℝ)) : Measure CarpetPoints :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (χ x ^ p))

theorem powerWeightedMeasure_le (p : ℝ) (hp : 0 < p) (μ : Measure CarpetPoints)
    (χ : C(CarpetPoints, ℝ)) (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) :
    powerWeightedMeasure p μ χ ≤ μ := by
  have h (x : CarpetPoints) : ENNReal.ofReal (χ x ^ p) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (hχ x).1 (hχ x).2 hp.le)
  calc
    powerWeightedMeasure p μ χ ≤ μ.withDensity 1 :=
      withDensity_mono (Eventually.of_forall h)
    _ = μ := withDensity_one

private theorem integral_powerWeightedMeasure (p : ℝ) (hp : 0 < p)
    (μ : Measure CarpetPoints) (χ : C(CarpetPoints, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (f : CarpetPoints → ℝ) :
    (∫ x, f x ∂powerWeightedMeasure p μ χ) =
      ∫ x, χ x ^ p * f x ∂μ := by
  unfold powerWeightedMeasure
  have hm : Measurable (fun x ↦ ENNReal.ofReal (χ x ^ p)) :=
    (ENNReal.continuous_ofReal.comp (χ.continuous.rpow_const (fun _ ↦ Or.inr hp.le))).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg (hχ _) _), smul_eq_mul]

private theorem deriv_abs_rpow_of_nonneg {p x : ℝ} (hp : 1 < p) (hx : 0 ≤ x) :
    deriv (fun t : ℝ ↦ |t| ^ p) x = p * x ^ (p - 1) := by
  rw [(hasDerivAt_abs_rpow x hp).deriv, abs_of_nonneg hx]
  by_cases h : x = 0
  · simp only [h, mul_zero, Real.zero_rpow (sub_ne_zero.mpr hp.ne'), mul_zero]
  · have hx' := lt_of_le_of_ne hx (Ne.symm h)
    calc
      _ = p * (x ^ (p - 2) * x ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hx']; congr 2; ring

private theorem abs_rpow_deriv_mul_power {p x y : ℝ} (hp : 1 < p) (hx : 0 ≤ x) :
    |deriv (fun t : ℝ ↦ |t| ^ p) x * y| ^ p.conjExponent =
      p ^ p.conjExponent * (x ^ p * |y| ^ p.conjExponent) := by
  let q := p.conjExponent
  have hp₀ := zero_lt_one.trans hp
  have hq := Real.HolderConjugate.conjExponent hp
  have hmul : (p - 1) * q = p := by
    change (p - 1) * (p / (p - 1)) = p
    rw [mul_div_cancel₀ _ (sub_ne_zero.mpr hp.ne')]
  rw [deriv_abs_rpow_of_nonneg hp hx, abs_mul, abs_of_nonneg (mul_nonneg hp₀.le (Real.rpow_nonneg hx _)),
    Real.mul_rpow (mul_nonneg hp₀.le (Real.rpow_nonneg hx _)) (abs_nonneg _),
    Real.mul_rpow hp₀.le (Real.rpow_nonneg hx _), ← Real.rpow_mul hx, hmul]
  ring

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 2200000 in
/-- The stationary row bound with the exact planar Lq test norm for
the measure weighted by the p-th power of a cutoff. -/
theorem abs_planar_power_row_le (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (f : E.domain) (hf : E.IsInteriorHarmonic f)
    (g : Fin 2 → E.continuousCore) (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (hμ : ∀ n, μ (carpetCellBoundary n) = 0)
    (hstat : ∀ i : Fin 2, ∀ t : ℝ,
      E.energyMeasure (f + t • E.continuousCoreToDomain (g i)) =
        ((E.energy (f + t • E.continuousCoreToDomain (g i)) : NNReal) : ℝ≥0∞) • μ)
    (χ : E.continuousCore) (hχ : ∀ x ∈ carpetOuterBoundary, χ.val x = 0)
    (hχ₀ : ∀ x, 0 ≤ χ.val x)
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) :
    let q := p.conjExponent
    let κ := (powerWeightedMeasure p μ χ.val).map (E.continuousCoreTuple g)
    |∑ i : Fin 2, E.variation h f (E.continuousCoreToDomain (g i)) *
        ∫ x, fderiv ℝ φ x (planarDirection i) ∂κ| ≤
      p * (E.energy f : ℝ) ^ q⁻¹ * (E.energy (E.continuousCoreToDomain χ) : ℝ) ^ p⁻¹ *
        (∫ x, |φ x| ^ q ∂κ) ^ q⁻¹ := by
  let q := p.conjExponent
  let G := E.continuousCoreTuple g
  let ν := powerWeightedMeasure p μ χ.val
  let κ := ν.map G
  let ω (t : ℝ) := |t| ^ p
  have hp := zero_lt_one.trans E.one_lt_p
  have hq : p.HolderConjugate q := Real.HolderConjugate.conjExponent E.one_lt_p
  have hω : ContDiff ℝ 1 ω := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow (E := ℝ) E.one_lt_p)
  have hω0 : ω 0 = 0 := by simp only [ω, abs_zero, Real.zero_rpow hp.ne']
  have hrow := E.abs_weighted_planar_row_le h hc f hf g μ hμ hstat χ hχ ω hω hω0 φ hφ
  change |∑ i : Fin 2, E.variation h f (E.continuousCoreToDomain (g i)) *
      ∫ x, ω (χ.val x) * fderiv ℝ φ (G x) (planarDirection i) ∂μ| ≤
    (∫ x, |deriv ω (χ.val x) * φ (G x)| ^ q ∂E.energyMeasure f) ^ q⁻¹ *
      (E.energy (E.continuousCoreToDomain χ) : ℝ) ^ p⁻¹ at hrow
  have hleft (i : Fin 2) :
      (∫ x, fderiv ℝ φ x (planarDirection i) ∂κ) =
        ∫ x, ω (χ.val x) * fderiv ℝ φ (G x) (planarDirection i) ∂μ := by
    have hc := (hφ.continuous_fderiv (by norm_num)).clm_apply
      (continuous_const : Continuous (fun _ : Fin 2 → ℝ ↦ planarDirection i))
    change (∫ x, fderiv ℝ φ x (planarDirection i) ∂ν.map G) = _
    rw [integral_map G.continuous.measurable.aemeasurable hc.aestronglyMeasurable,
      integral_powerWeightedMeasure p hp μ χ.val hχ₀]
    simp only [ω, abs_of_nonneg (hχ₀ _)]
  have hmass : E.energyMeasure f = ((E.energy f : NNReal) : ℝ≥0∞) • μ := by
    simpa only [zero_smul, add_zero] using hstat 0 0
  let A := (E.energy f : ℝ)
  let I := ∫ x, |φ x| ^ q ∂κ
  have hI : 0 ≤ I := integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hint :
      (∫ x, |deriv ω (χ.val x) * φ (G x)| ^ q ∂E.energyMeasure f) =
        A * (p ^ q * I) := by
    rw [hmass, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
    congr 1
    dsimp only [ω, q]
    simp_rw [abs_rpow_deriv_mul_power E.one_lt_p (hχ₀ _)]
    rw [integral_const_mul]
    dsimp only [I, κ, ν]
    rw [integral_map G.continuous.measurable.aemeasurable
      (hφ.continuous.abs.rpow_const (fun _ ↦ Or.inr hq.symm.nonneg)).aestronglyMeasurable,
      integral_powerWeightedMeasure p hp μ χ.val hχ₀]
  change |∑ i : Fin 2, E.variation h f (E.continuousCoreToDomain (g i)) *
      ∫ x, fderiv ℝ φ x (planarDirection i) ∂κ| ≤
    p * A ^ q⁻¹ * (E.energy (E.continuousCoreToDomain χ) : ℝ) ^ p⁻¹ * I ^ q⁻¹
  simp only [hleft]
  rw [hint, Real.mul_rpow (NNReal.coe_nonneg _) (mul_nonneg (Real.rpow_nonneg hp.le _) hI),
    Real.mul_rpow (Real.rpow_nonneg hp.le _) hI, Real.rpow_rpow_inv hp.le hq.symm.ne_zero] at hrow
  exact hrow.trans_eq (by ring)

end SelfSimilarPEnergy

end CarpetEnergy
