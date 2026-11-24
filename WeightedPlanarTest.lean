import PlanarDistributionRows
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The weight and planar derivatives of a weighted test
-/

open scoped BigOperators

namespace CarpetEnergy

/-- Drop the first coordinate of a weighted planar argument. -/
noncomputable def planarTail : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin 2 ↦ ContinuousLinearMap.proj i.succ)

/-- The scalar test formed by multiplying a planar test by its weight. -/
noncomputable def weightedPlanarTest (ω : ℝ → ℝ) (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ω (x 0) * φ (planarTail x)

theorem contDiff_weightedPlanarTest (ω : ℝ → ℝ) (hω : ContDiff ℝ 1 ω)
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) :
    ContDiff ℝ 1 (weightedPlanarTest ω φ) :=
  (hω.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) 0).contDiff).mul
    (hφ.comp planarTail.contDiff)

private theorem fderiv_weightedPlanarTest (ω : ℝ → ℝ) (hω : ContDiff ℝ 1 ω)
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (x v : Fin 3 → ℝ) :
    fderiv ℝ (weightedPlanarTest ω φ) x v =
      deriv ω (x 0) * v 0 * φ (planarTail x) +
        ω (x 0) * fderiv ℝ φ (planarTail x) (planarTail v) := by
  let P : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hD := ((contDiff_one_iff_fderiv.mp hφ).1 (planarTail x)).hasFDerivAt.comp x planarTail.hasFDerivAt
  have hW := ((contDiff_one_iff_deriv.mp hω).1 (x 0)).hasDerivAt.hasFDerivAt.comp x P.hasFDerivAt
  have h := hW.mul hD
  have he : HasFDerivAt (weightedPlanarTest ω φ)
      (ω (x 0) • (fderiv ℝ φ (planarTail x)).comp planarTail +
        φ (planarTail x) • ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv ω (x 0))).comp P) x := h
  rw [he.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, P, ContinuousLinearMap.proj_apply]
  ring

theorem fderiv_weightedPlanarTest_zero (ω : ℝ → ℝ) (hω : ContDiff ℝ 1 ω)
    (φ : (Fin 2 → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (x : Fin 3 → ℝ) :
    fderiv ℝ (weightedPlanarTest ω φ) x (Pi.single 0 1) = deriv ω (x 0) * φ (planarTail x) := by
  have hTail : planarTail (Pi.single 0 1) = 0 := by
    ext i
    change (Pi.single (0 : Fin 3) 1 : Fin 3 → ℝ) i.succ = 0
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i)]
  rw [fderiv_weightedPlanarTest ω hω φ hφ, hTail, map_zero, mul_zero, add_zero, Pi.single_eq_same, mul_one]

theorem fderiv_weightedPlanarTest_succ (ω : ℝ → ℝ) (hω : ContDiff ℝ 1 ω)
    (φ : (Fin 2 → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (x : Fin 3 → ℝ) (i : Fin 2) :
    fderiv ℝ (weightedPlanarTest ω φ) x (Pi.single i.succ 1) =
      ω (x 0) * fderiv ℝ φ (planarTail x) (planarDirection i) := by
  have hTail : planarTail (Pi.single i.succ 1) = planarDirection i := by
    ext j
    change (Pi.single i.succ 1 : Fin 3 → ℝ) j.succ = (Pi.single i 1 : Fin 2 → ℝ) j
    by_cases h : j = i
    · subst j
      simp
    · rw [Pi.single_eq_of_ne (fun h' ↦ h (Fin.succ_injective _ h')), Pi.single_eq_of_ne h]
  rw [fderiv_weightedPlanarTest ω hω φ hφ, hTail,
    Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm, mul_zero, zero_mul, zero_add]

end CarpetEnergy
