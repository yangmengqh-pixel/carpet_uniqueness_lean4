import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Extending a functional dominated by a pullback norm

A bound in terms of the image of a linear map makes the functional
descend to its range. Hahn–Banach then extends it to the ambient
normed space.
-/

namespace CarpetEnergy

theorem exists_continuousLinearMap_factor_of_bound
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →ₗ[ℝ] W) (F : V →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖F x‖ ≤ C * ‖T x‖) :
    ∃ L : W →L[ℝ] ℝ, ‖L‖ ≤ C ∧ ∀ x, L (T x) = F x := by
  have hk : LinearMap.ker T ≤ LinearMap.ker F := by
    intro x hx
    change T x = 0 at hx
    change F x = 0
    have hx' := h x
    rw [hx, norm_zero, mul_zero] at hx'
    exact norm_eq_zero.mp (le_antisymm hx' (norm_nonneg _))
  let R : LinearMap.range T →ₗ[ℝ] ℝ :=
    ((LinearMap.ker T).liftQ F hk).comp T.quotKerEquivRange.symm.toLinearMap
  have hR (x : V) : R ⟨T x, LinearMap.mem_range_self T x⟩ = F x := by
    unfold R
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, T.quotKerEquivRange_symm_apply_image]
    rfl
  have hbound (z : LinearMap.range T) : ‖R z‖ ≤ C * ‖z‖ := by
    obtain ⟨x, hx⟩ := z.property
    have he : (⟨T x, LinearMap.mem_range_self T x⟩ : LinearMap.range T) = z := Subtype.ext hx
    rw [← he, hR]
    exact h x
  let S : LinearMap.range T →L[ℝ] ℝ := R.mkContinuous C hbound
  obtain ⟨L, hLS, hnorm⟩ := exists_extension_norm_eq (LinearMap.range T) S
  refine ⟨L, hnorm.le.trans (S.opNorm_le_bound hC hbound), fun x ↦ ?_⟩
  exact (hLS ⟨T x, LinearMap.mem_range_self T x⟩).trans (hR x)

end CarpetEnergy
