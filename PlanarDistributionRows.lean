import MeasureGradientAbsoluteContinuity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Extracting the planar distributional gradient

Two uniformly bounded linear combinations of the planar derivatives
bound both partial derivatives when their coefficient matrix is
invertible. The finite-measure absolute-continuity theorem then applies.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

/-- Standard coordinate directions in the plane as a product of real lines. -/
def planarDirection (i : Fin 2) : Fin 2 → ℝ := Pi.single i 1

private theorem planarDirection_decomposition (v : Fin 2 → ℝ) :
    v = v 0 • planarDirection 0 + v 1 • planarDirection 1 := by
  ext i
  fin_cases i <;> simp [planarDirection, Pi.add_apply, Pi.smul_apply]

private noncomputable def derivativeIntegral (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∫ x, fderiv ℝ φ x v ∂μ
  map_add' v w := by
    have hcont := hφ.continuous_fderiv (by norm_num)
    have hi (u : Fin 2 → ℝ) : Integrable (fun x ↦ fderiv ℝ φ x u) μ :=
      (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply ℝ hs u)
    simp only [map_add, integral_add (hi v) (hi w)]
  map_smul' t v := by
    simp only [map_smul, smul_eq_mul, integral_const_mul, RingHom.id_apply]

theorem abs_bounds_of_two_rows {a b c d C D X Y : ℝ} (hdet : a * d - b * c ≠ 0)
    (hXY : |a * X + b * Y| ≤ C ∧ |c * X + d * Y| ≤ D) :
    |X| ≤ (|d| * C + |b| * D) / |a * d - b * c| ∧
      |Y| ≤ (|a| * D + |c| * C) / |a * d - b * c| := by
  let Δ := a * d - b * c
  have hΔ : 0 < |Δ| := abs_pos.mpr hdet
  constructor
  · apply (le_div_iff₀ hΔ).mpr
    calc
      _ = |Δ * X| := by rw [abs_mul, mul_comm]
      _ = |d * (a * X + b * Y) - b * (c * X + d * Y)| := congrArg (fun t : ℝ ↦ |t|) (by dsimp only [Δ]; ring)
      _ ≤ |d * (a * X + b * Y)| + |b * (c * X + d * Y)| := by simpa only [sub_zero, abs_neg, zero_sub] using abs_sub_le _ (0 : ℝ) _
      _ ≤ _ := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hXY.1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hXY.2 (abs_nonneg _))
  · apply (le_div_iff₀ hΔ).mpr
    calc
      _ = |Δ * Y| := by rw [abs_mul, mul_comm]
      _ = |a * (c * X + d * Y) - c * (a * X + b * Y)| := congrArg (fun t : ℝ ↦ |t|) (by dsimp only [Δ]; ring)
      _ ≤ |a * (c * X + d * Y)| + |c * (a * X + b * Y)| := by simpa only [sub_zero, abs_neg, zero_sub] using abs_sub_le _ (0 : ℝ) _
      _ ≤ _ := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hXY.2 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hXY.1 (abs_nonneg _))

theorem hasBoundedDistributionalGradient_of_planar_rows
    (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (a b c d C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hdet : a * d - b * c ≠ 0)
    (h : ∀ (φ : (Fin 2 → ℝ) → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) →
      let X := ∫ x, fderiv ℝ φ x (planarDirection 0) ∂μ
      let Y := ∫ x, fderiv ℝ φ x (planarDirection 1) ∂μ
      |a * X + b * Y| ≤ C ∧ |c * X + d * Y| ≤ D) :
    ∃ K ≥ (0 : ℝ), HasBoundedDistributionalGradient μ K := by
  let Δ := a * d - b * c
  let K₀ := (|d| * C + |b| * D) / |Δ|
  let K₁ := (|a| * D + |c| * C) / |Δ|
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hK₁ : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  refine ⟨K₀ + K₁, add_nonneg hK₀ hK₁, fun φ hc hs h01 v ↦ ?_⟩
  let L := derivativeIntegral μ φ hc hs
  let X := L (planarDirection 0)
  let Y := L (planarDirection 1)
  have hXY : |a * X + b * Y| ≤ C ∧ |c * X + d * Y| ≤ D := h φ hc hs h01
  obtain ⟨hX, hY⟩ := abs_bounds_of_two_rows hdet hXY
  have hv (i : Fin 2) : |v i| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm v i
  change |L v| ≤ _
  have he : L v = v 0 * X + v 1 * Y := by
    conv_lhs => rw [planarDirection_decomposition v]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [he]
  calc
    _ ≤ |v 0 * X| + |v 1 * Y| := abs_add_le _ _
    _ ≤ ‖v‖ * K₀ + ‖v‖ * K₁ := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul (hv 0) hX (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul (hv 1) hY (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- The planar absolute-continuity implication of (5.31)–(5.32). -/
theorem absoluteContinuous_of_planar_rows
    (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (a b c d C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hdet : a * d - b * c ≠ 0)
    (h : ∀ (φ : (Fin 2 → ℝ) → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) →
      let X := ∫ x, fderiv ℝ φ x (planarDirection 0) ∂μ
      let Y := ∫ x, fderiv ℝ φ x (planarDirection 1) ∂μ
      |a * X + b * Y| ≤ C ∧ |c * X + d * Y| ≤ D) :
    μ ≪ volume := by
  obtain ⟨K, hK, hgrad⟩ := hasBoundedDistributionalGradient_of_planar_rows μ a b c d C D hC hD hdet h
  exact absoluteContinuous_of_boundedDistributionalGradient μ volume hK hgrad

end CarpetEnergy
