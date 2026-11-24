import EnergyRelativeRootSeminorm
import SeminormPowerFirstVariation

/-!
# A smooth, self-similar graph-limit energy on the given domain
-/

open Filter
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- Renormalization of the common graph limit produces a comparable
energy with the same cell scale, the generalized contraction, and
linear first variations on the full energy domain. -/
theorem exists_relative_graphLimit_with_first_variations :
    ∃ (G : E.domain → ℝ) (S : Seminorm ℝ E.domain),
      (∀ f, G f = (S f) ^ p) ∧
      (∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ f, A * (E.energy f : ℝ) ≤ G f ∧ G f ≤ B * (E.energy f : ℝ)) ∧
      (∀ f, G f = E.scalingFactor * ∑ i, G (E.pullback i f)) ∧
      (∀ a : ℝ, ∀ f, G (f + ⟨constantLp p a, E.constant_mem a⟩) = G f) ∧
      (∀ σ f, G (E.pullbackSymmetry σ f) = G f) ∧
      E.HasFiniteGeneralizedPContraction G ∧ E.HasInfinityGeneralizedPContraction G ∧
      (∀ f, ∃ L : E.domain →ₗ[ℝ] ℝ, ∀ g : E.domain,
        HasDerivAt (fun t : ℝ ↦ G (f + t • g)) (p * L g) 0) := by
  let hp := zero_lt_one.trans E.one_lt_p
  obtain ⟨j, F, l, G, A, hA, B, hB, hj, hF, hl₀, _, hcomp, hlim, he⟩ :=
    E.exists_selfSimilarized_discreteLimit
  let : l.NeBot := hl₀
  have hG (f : E.domain) : 0 ≤ G f :=
    (mul_nonneg hA.le (NNReal.coe_nonneg _)).trans (hcomp f).1
  obtain ⟨hhom, hconst, hsym⟩ := E.renormalizedGammaLimit_invariance hF hlim
  have hgcp := E.renormalizedGammaLimit_hasFiniteGeneralizedPContraction hj hF hlim
  let S := E.relativeRootSeminorm G hG hhom hgcp
  have hS (f : E.domain) : G f = S f ^ p := by
    change G f = (G f ^ p⁻¹) ^ p
    exact (Real.rpow_inv_rpow (hG f) hp.ne').symm
  let pull (i : Fin 8) : E.domain →ₗ[ℝ] E.domain :=
    { toFun := E.pullback i
      map_add' := fun f g ↦ E.pullbackWord_add [i] f g
      map_smul' := fun a f ↦ E.pullbackWord_smul [i] a f }
  have hd := HasUniformSymmetricIncrement.of_renormalizationMean_limit
    E.isScalingFactor_scalingFactor.1.le pull (E.gammaLimit_toReal_hasUniformSymmetricIncrement hj hF) hlim
  have hpow : HasUniformSymmetricIncrement (fun f : E.domain ↦ S f ^ p) := by
    rw [show (fun f : E.domain ↦ S f ^ p) = G from (funext hS).symm]
    exact hd
  refine ⟨G, S, hS, ⟨A, hA, B, hB, hcomp⟩, he, hconst, hsym, hgcp, hgcp.infinity E hG, fun f ↦ ?_⟩
  simpa only [hS] using exists_linear_first_variation_of_uniformSymmetricIncrement S E.one_lt_p hpow f

end CarpetEnergy.SelfSimilarPEnergy
