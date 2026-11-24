import EnergyVariationCells
import EnergySelfSimilarSmoothness
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.Module

/-!
# Uniform control of a first variation by its secants
-/

open Filter Function Set
open scoped ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem convexOn_energy : ConvexOn ℝ univ (fun f : E.domain ↦ (E.energy f : ℝ)) := by
  refine ⟨convex_univ, fun f _ g _ a b ha hb hab ↦ ?_⟩
  let S := E.rootSeminorm
  have hp := zero_lt_one.trans E.one_lt_p
  have hF (f : E.domain) : (E.energy f : ℝ) = S f ^ p := by
    rw [E.rootSeminorm_apply, Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne']
  simp only [hF, smul_eq_mul]
  have hS := map_add_le_add S (a • f) (b • g)
  rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb] at hS
  exact (Real.rpow_le_rpow (apply_nonneg S _) hS hp.le).trans
    ((convexOn_rpow E.one_lt_p.le).2 (mem_Ici.mpr (apply_nonneg S f))
      (mem_Ici.mpr (apply_nonneg S g)) ha hb hab)

theorem mul_variation_le_energy_forward_difference (h : E.HasLinearFirstVariations)
    (f g : E.domain) {t : ℝ} (ht : 0 < t) :
    t * (p * E.variation h f g) ≤ (E.energy (f + t • g) : ℝ) - (E.energy f : ℝ) := by
  let F (s : ℝ) := (E.energy (f + s • g) : ℝ)
  have hconv : ConvexOn ℝ univ F := by
    refine ⟨convex_univ, fun r _ s _ a b ha hb hab ↦ ?_⟩
    have he : f + (a • r + b • s) • g = a • (f + r • g) + b • (f + s • g) := by
      calc
        _ = (a + b) • f + (a • r + b • s) • g := by rw [hab, one_smul]
        _ = _ := by module
    dsimp only [F]
    rw [he]
    exact E.convexOn_energy.2 (mem_univ _) (mem_univ _) ha hb hab
  have hb := hconv.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) ht
    (E.hasDerivAt_energy_variation h f g)
  have he : slope F 0 t = (F t - F 0) / t := by
    rw [slope_def_field, sub_zero]
  rw [he] at hb
  have hh := (le_div_iff₀ ht).mp hb
  simpa only [F, zero_smul, add_zero, mul_comm t] using hh

set_option maxHeartbeats 1800000 in
/-- The shared symmetric increment bound controls the first-order
remainder uniformly over bases and directions of bounded energy. -/
theorem exists_uniform_energy_variation_error_bound (h : E.HasLinearFirstVariations)
    (hs : HasUniformSymmetricIncrement (fun f ↦ (E.energy f : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (f g : E.domain) (t : ℝ), 0 < t → t < δ →
      0 ≤ (E.energy (f + t • g) : ℝ) - (E.energy f : ℝ) - t * (p * E.variation h f g) ∧
      (E.energy (f + t • g) : ℝ) - (E.energy f : ℝ) - t * (p * E.variation h f g) ≤
        ε * t * ((E.energy f : ℝ) + (E.energy g : ℝ)) := by
  obtain ⟨δ, hδ, hbound⟩ := hs ε hε
  refine ⟨δ, hδ, fun f g t ht htt ↦ ?_⟩
  have h₁ := E.mul_variation_le_energy_forward_difference h f g ht
  have h₂ := E.mul_variation_le_energy_forward_difference h f (-g) ht
  rw [map_neg, smul_neg, ← sub_eq_add_neg] at h₂
  have hS := hbound f g t (by rwa [abs_of_pos ht])
  rw [abs_of_pos ht] at hS
  exact ⟨sub_nonneg.mpr h₁, by linarith only [h₂, hS, show
    (2 + ε * t) * (E.energy f : ℝ) + ε * t * (E.energy g : ℝ) =
      2 * (E.energy f : ℝ) + ε * t * ((E.energy f : ℝ) + (E.energy g : ℝ)) by ring]⟩

end CarpetEnergy.SelfSimilarPEnergy
