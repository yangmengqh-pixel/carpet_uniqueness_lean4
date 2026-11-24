import PlanarSobolevRoot

/-!
# Multiplication of a weakly differentiable function by a smooth cutoff
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsLocallyFiniteMeasure μ]

set_option maxHeartbeats 3100000 in
/-- The weak product rule against a compactly supported smooth factor. -/
theorem HasWeakDirectionalDerivative.mul_smooth_cutoff
    {p : ℝ} (hp : 1 < p) {u v χ : X → ℝ} {e : X}
    (h : HasWeakDirectionalDerivative μ u v e)
    (hu : MemLp u (ENNReal.ofReal p) μ) (hv : MemLp v (ENNReal.ofReal p) μ)
    (hχ : ContDiff ℝ 1 χ) (hχs : HasCompactSupport χ) :
    HasWeakDirectionalDerivative μ (χ * u) (fun x ↦ χ x * v x + fderiv ℝ χ x e * u x) e := by
  intro φ hφ _hφs
  let q := p.conjExponent
  let : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 :=
    (Real.HolderConjugate.conjExponent hp).ennrealOfReal
  let Dχ (x : X) := fderiv ℝ χ x e
  let Dφ (x : X) := fderiv ℝ φ x e
  have hDχ : Continuous Dχ := (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDφ : Continuous Dφ := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDχs : HasCompactSupport Dχ := hχs.fderiv_apply ℝ e
  have hI₀ : Integrable (fun x ↦ u x * (χ x * Dφ x)) μ :=
    hu.integrable_mul ((hχ.continuous.mul hDφ).memLp_of_hasCompactSupport (p := ENNReal.ofReal q) (hχs.mul_right (f' := Dφ)))
  have hI₁ : Integrable (fun x ↦ u x * (Dχ x * φ x)) μ :=
    hu.integrable_mul ((hDχ.mul hφ.continuous).memLp_of_hasCompactSupport (p := ENNReal.ofReal q) (hDχs.mul_right (f' := φ)))
  have hI₂ : Integrable (fun x ↦ v x * (χ x * φ x)) μ :=
    hv.integrable_mul ((hχ.continuous.mul hφ.continuous).memLp_of_hasCompactSupport (p := ENNReal.ofReal q) (hχs.mul_right (f' := φ)))
  have hh := h (χ * φ) (hχ.mul hφ) (hχs.mul_right (f' := φ))
  have hdiff (x : X) : fderiv ℝ (χ * φ) x e = χ x * Dφ x + Dχ x * φ x := by
    rw [fderiv_mul (hχ.differentiable (by norm_num) x) (hφ.differentiable (by norm_num) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, Dχ, Dφ]
    ring
  simp_rw [hdiff, mul_add, Pi.mul_apply] at hh
  rw [integral_add hI₀ hI₁] at hh
  have hleft :
      (∫ x, (χ * u) x * fderiv ℝ φ x e ∂μ) = ∫ x, u x * (χ x * Dφ x) ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by dsimp only [Pi.mul_apply, Dφ]; ring
  have hright : (∫ x, (χ x * v x + fderiv ℝ χ x e * u x) * φ x ∂μ) =
      (∫ x, v x * (χ x * φ x) ∂μ) + ∫ x, u x * (Dχ x * φ x) ∂μ := by
    rw [← integral_add hI₂ hI₁]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by dsimp only [Dχ]; ring
  rw [hleft, hright]
  linarith only [hh]

end CarpetEnergy
