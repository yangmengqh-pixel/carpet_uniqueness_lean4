import PlanarDistributionRows
import WeightedDirectionalDerivative

/-!
# Weighted derivatives of a planar pushforward

The inverse first-variation matrix bounds each coordinate
derivative by the conjugate-exponent norm of the test. The
coordinate distributional derivatives have Lp densities with
respect to the pushforward measure.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

theorem exists_weighted_coordinate_densities_of_planar_rows
    (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    {p q a b c d C D : ℝ} (hpq : p.HolderConjugate q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hdet : a * d - b * c ≠ 0)
    (h : ∀ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      let X := ∫ x, fderiv ℝ φ x (planarDirection 0) ∂μ
      let Y := ∫ x, fderiv ℝ φ x (planarDirection 1) ∂μ
      let N := (∫ x, |φ x| ^ q ∂μ) ^ q⁻¹
      |a * X + b * Y| ≤ C * N ∧ |c * X + d * Y| ≤ D * N) :
    ∃ r : Fin 2 → (Fin 2 → ℝ) → ℝ,
      (∀ i, Measurable (r i) ∧ MemLp (r i) (ENNReal.ofReal p) μ) ∧
      ∀ i (φ : (Fin 2 → ℝ) → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ x, fderiv ℝ φ x (planarDirection i) ∂μ) = ∫ x, r i x * φ x ∂μ := by
  let K₀ := (|d| * C + |b| * D) / |a * d - b * c|
  let K₁ := (|a| * D + |c| * C) / |a * d - b * c|
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hK₁ : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  have hcoord (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) :
      let N := (∫ x, |φ x| ^ q ∂μ) ^ q⁻¹
      |∫ x, fderiv ℝ φ x (planarDirection 0) ∂μ| ≤ K₀ * N ∧
      |∫ x, fderiv ℝ φ x (planarDirection 1) ∂μ| ≤ K₁ * N := by
    obtain ⟨h₀, h₁⟩ := abs_bounds_of_two_rows hdet (h φ hφ hφs)
    constructor
    · refine h₀.trans_eq ?_
      dsimp only [K₀]
      ring
    · refine h₁.trans_eq ?_
      dsimp only [K₁]
      ring
  obtain ⟨u, hu, huLp, huD⟩ := exists_weighted_directional_derivative_density μ hpq hK₀
    (planarDirection 0) (fun φ hφ hs ↦ (hcoord φ hφ hs).1)
  obtain ⟨v, hv, hvLp, hvD⟩ := exists_weighted_directional_derivative_density μ hpq hK₁
    (planarDirection 1) (fun φ hφ hs ↦ (hcoord φ hφ hs).2)
  refine ⟨![u, v], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hu, huLp⟩
    · exact ⟨hv, hvLp⟩
  · intro i
    fin_cases i
    · exact huD
    · exact hvD

theorem absoluteContinuous_of_weighted_planar_rows
    (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    {q a b c d C D : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hdet : a * d - b * c ≠ 0)
    (h : ∀ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      let X := ∫ x, fderiv ℝ φ x (planarDirection 0) ∂μ
      let Y := ∫ x, fderiv ℝ φ x (planarDirection 1) ∂μ
      let N := (∫ x, |φ x| ^ q ∂μ) ^ q⁻¹
      |a * X + b * Y| ≤ C * N ∧ |c * X + d * Y| ≤ D * N) : μ ≪ volume := by
  let W := (μ.real univ) ^ q⁻¹
  have hW : 0 ≤ W := Real.rpow_nonneg measureReal_nonneg _
  apply absoluteContinuous_of_planar_rows μ a b c d (C * W) (D * W)
    (mul_nonneg hC hW) (mul_nonneg hD hW) hdet
  intro φ hφ hs h01
  have hpoint (x : Fin 2 → ℝ) : |φ x| ^ q ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (h01 x).1]
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (h01 x).1 (h01 x).2 hq
  have hi := integral_mono_of_nonneg
    (μ := μ) (f := fun x ↦ |φ x| ^ q) (g := fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (integrable_const (1 : ℝ)) (Eventually.of_forall hpoint)
  rw [integral_const, smul_eq_mul, mul_one] at hi
  have htest := Real.rpow_le_rpow (integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _))
    hi (inv_nonneg.mpr hq)
  exact ⟨(h φ hφ hs).1.trans (mul_le_mul_of_nonneg_left htest hC),
    (h φ hφ hs).2.trans (mul_le_mul_of_nonneg_left htest hD)⟩

end CarpetEnergy
