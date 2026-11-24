import PlanarWeightedDerivatives
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Weak derivatives of the planar Radon–Nikodym density

An Lp derivative density with respect to an absolutely continuous
planar measure gives a weak derivative of its Lebesgue density.
The same weighted bound controls the product with its p-th root.
-/

open Filter Function MeasureTheory
open scoped ENNReal

namespace CarpetEnergy

/-- Distributional directional derivative, tested on compactly supported
C¹ functions. -/
def HasWeakDirectionalDerivative {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] (μ : Measure X) (u v : X → ℝ) (e : X) : Prop :=
  ∀ φ : X → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ x, u x * fderiv ℝ φ x e ∂μ) = -(∫ x, v x * φ x ∂μ)

/-- The root-weighted product has finite p-energy in Lebesgue measure
whenever the coefficient belongs to Lp for the original measure. -/
theorem memLp_mul_rnDeriv_rpow_inv {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    {p : ℝ} (hp : 0 < p) {f : X → ℝ} (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x ↦ (μ.rnDeriv ν x).toReal ^ p⁻¹ * f x) (ENNReal.ofReal p) ν := by
  let ξ (x : X) := (μ.rnDeriv ν x).toReal
  have hξ : Measurable ξ := ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv μ ν)
  have hξRoot : Measurable (fun x ↦ ξ x ^ p⁻¹) :=
    (Real.continuous_rpow_const (inv_nonneg.mpr hp.le)).measurable.comp hξ
  have hg := (hξRoot.mul hfm).aestronglyMeasurable (μ := ν)
  have hp₀ := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hi := hf.integrable_norm_rpow hp₀ ENNReal.ofReal_ne_top
  have hi' := (integrable_toReal_rnDeriv_mul_iff hμν).mpr hi
  apply (integrable_norm_rpow_iff hg hp₀ ENNReal.ofReal_ne_top).mp
  refine hi'.congr ?_
  apply Eventually.of_forall
  intro x
  change ξ x * ‖f x‖ ^ (ENNReal.ofReal p).toReal =
    ‖ξ x ^ p⁻¹ * f x‖ ^ (ENNReal.ofReal p).toReal
  have hξ₀ : 0 ≤ ξ x := ENNReal.toReal_nonneg
  rw [ENNReal.toReal_ofReal hp.le, norm_mul, Real.norm_eq_abs (ξ x ^ p⁻¹),
    abs_of_nonneg (Real.rpow_nonneg hξ₀ _),
    Real.mul_rpow (Real.rpow_nonneg hξ₀ _) (norm_nonneg _), Real.rpow_inv_rpow hξ₀ hp.ne']

theorem exists_planar_density_with_weak_derivative (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) {p : ℝ} (hp : 1 < p)
    (r : Fin 2 → (Fin 2 → ℝ) → ℝ)
    (hr : ∀ i, Measurable (r i) ∧ MemLp (r i) (ENNReal.ofReal p) μ)
    (h : ∀ i (φ : (Fin 2 → ℝ) → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, fderiv ℝ φ x (planarDirection i) ∂μ) = ∫ x, r i x * φ x ∂μ) :
    ∃ ξ : (Fin 2 → ℝ) → ℝ,
      Measurable ξ ∧ (∀ x, 0 ≤ ξ x) ∧ Integrable ξ volume ∧
      volume.withDensity (fun x ↦ ENNReal.ofReal (ξ x)) = μ ∧
      ∀ i, Integrable (fun x ↦ -(ξ x * r i x)) volume ∧
        HasWeakDirectionalDerivative volume ξ (fun x ↦ -(ξ x * r i x)) (planarDirection i) ∧
        MemLp (fun x ↦ ξ x ^ p⁻¹ * r i x) (ENNReal.ofReal p) volume := by
  let ξ (x : Fin 2 → ℝ) := (μ.rnDeriv volume x).toReal
  have hm : Measurable ξ := ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv μ volume)
  have hξ (x : Fin 2 → ℝ) : 0 ≤ ξ x := ENNReal.toReal_nonneg
  have hμ' : volume.withDensity (fun x ↦ ENNReal.ofReal (ξ x)) = μ := by
    refine (withDensity_congr_ae ?_).trans (Measure.withDensity_rnDeriv_eq _ _ hμ)
    filter_upwards [Measure.rnDeriv_lt_top μ volume] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  refine ⟨ξ, hm, hξ, Measure.integrable_toReal_rnDeriv, hμ', fun i ↦ ?_⟩
  have hi : Integrable (r i) μ := (hr i).2.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  refine ⟨((integrable_toReal_rnDeriv_mul_iff hμ).mpr hi).neg, ?_,
    memLp_mul_rnDeriv_rpow_inv hμ (zero_lt_one.trans hp) (hr i).1 (hr i).2⟩
  intro φ hφ hφs
  calc
    _ = ∫ x, fderiv ℝ φ x (planarDirection i) ∂μ := integral_toReal_rnDeriv_mul hμ
    _ = ∫ x, r i x * φ x ∂μ := h i φ hφ hφs
    _ = ∫ x, ξ x * (r i x * φ x) ∂volume := (integral_toReal_rnDeriv_mul hμ).symm
    _ = _ := by simp_rw [neg_mul, integral_neg, neg_neg, mul_assoc]

end CarpetEnergy
