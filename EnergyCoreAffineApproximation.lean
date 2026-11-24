import EnergyGeneralizedCoreComposition
import SmoothAffineLipschitzExtension

/-!
# Smooth compositions and affine remainders on the finite-energy core
-/

open Metric Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The tuple of continuous coordinate functions. -/
def continuousCoreTuple {m : ℕ} (u : Fin m → E.continuousCore) :
    C(CarpetPoints, Fin m → ℝ) where
  toFun x i := (u i).val x
  continuous_toFun := continuous_pi (fun i ↦ (u i).val.continuous)

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem continuousCoreTuple_apply {m : ℕ} (u : Fin m → E.continuousCore) (x : CarpetPoints) (i : Fin m) :
    E.continuousCoreTuple u x i = (u i).val x := rfl

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- A continuous finite-energy tuple has bounded image. -/
theorem exists_closedBall_coreTuple {m : ℕ} (u : Fin m → E.continuousCore) :
    ∃ R : ℝ, ∀ x : CarpetPoints, E.continuousCoreTuple u x ∈ closedBall 0 R := by
  have h := (isCompact_univ.image (E.continuousCoreTuple u).continuous.norm).bddAbove
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun x ↦ ?_⟩
  rw [mem_closedBall, dist_zero_right]
  exact hR (mem_image_of_mem _ (mem_univ x))

/-- A C¹ scalar composition of finitely many continuous profiles
belongs to the continuous energy core. -/
theorem exists_core_comp_contDiff
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {m : ℕ} (u : Fin m → E.continuousCore) (φ : (Fin m → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    ∃ v : E.continuousCore, ∀ x, v.val x = φ (E.continuousCoreTuple u x) := by
  obtain ⟨R, hR⟩ := E.exists_closedBall_coreTuple u
  obtain ⟨b, hb, ψ, hψ, he⟩ := exists_lipschitz_extension_of_contDiff_closedBall φ hφ R
  obtain ⟨v, hv, _⟩ := E.exists_core_comp_lipschitzWith hc u ψ hb hψ
  exact ⟨v, fun x ↦ (hv x).trans (he (hR x)).symm⟩

/-- Apply an ambient linear functional to the tuple within the core. -/
noncomputable def linearCoreTuple {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (u : Fin m → E.continuousCore) : E.continuousCore := by
  classical
  exact ∑ i, (L (Pi.single i 1)) • u i

private theorem sum_smul_pi_single {m : ℕ} (x : Fin m → ℝ) :
    (∑ i, x i • (Pi.single i 1 : Fin m → ℝ)) = x := by
  classical
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi.symm, mul_zero]
  · simp

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem linearCoreTuple_apply {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (u : Fin m → E.continuousCore) (x : CarpetPoints) :
    (E.linearCoreTuple L u).val x = L (E.continuousCoreTuple u x) := by
  classical
  let N : E.continuousCore →ₗ[ℝ] ℝ := (ContinuousMap.evalCLM ℝ x).toLinearMap.comp E.continuousCore.subtype
  have h (v : E.continuousCore) : N v = v.val x := rfl
  rw [← h, linearCoreTuple, map_sum]
  simp only [h]
  conv_rhs => rw [← sum_smul_pi_single (E.continuousCoreTuple u x)]
  simp only [map_sum, map_smul, smul_eq_mul, continuousCoreTuple_apply, mul_comm]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- On a tuple whose values stay near the expansion center, the root of
the affine remainder is bounded by its Lipschitz constant times the
mixed energy root of the tuple. -/
theorem rootSeminorm_affine_remainder_le
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {m : ℕ} (u : Fin m → E.continuousCore) (v : E.continuousCore) (φ : (Fin m → ℝ) → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] ℝ) (hv : ∀ x, v.val x = φ (E.continuousCoreTuple u x))
    {s : Set (Fin m → ℝ)} (hs : ∀ x, E.continuousCoreTuple u x ∈ s)
    (ψ : (Fin m → ℝ) → ℝ) {b : ℝ≥0} (hb : 0 < b) (hψ : LipschitzWith b ψ)
    (he : EqOn (fun y ↦ φ y - L y) ψ s) :
    E.rootSeminorm (E.continuousCoreToDomain (v - E.linearCoreTuple L u)) ≤
      (b : ℝ) * finitePowerSum p (fun i ↦ E.rootSeminorm (E.continuousCoreToDomain (u i))) := by
  obtain ⟨w, hw, hb⟩ := E.exists_core_comp_lipschitzWith hc u ψ hb hψ
  have hh : v - E.linearCoreTuple L u = w := by
    apply Subtype.ext
    ext x
    change v.val x - (E.linearCoreTuple L u).val x = w.val x
    rw [hv, E.linearCoreTuple_apply, hw]
    exact he (hs x)
  rw [hh]
  exact hb

end CarpetEnergy.SelfSimilarPEnergy
