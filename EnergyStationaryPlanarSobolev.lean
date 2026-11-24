import EnergyStationaryPlanarDensity
import PlanarSobolevRoot

/-!
# Sobolev density of the weighted stationary pushforward

This combines the planar row representation with the weak chain
rule for the p-th root.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- Proposition 5.6 for continuous stationary harmonic profiles and a
continuous interior cutoff. -/
theorem exists_stationary_pair_planar_sobolev_density
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (F G : E.continuousCore)
    (hF : E.IsInteriorHarmonic (E.continuousCoreToDomain F))
    (hG : E.IsInteriorHarmonic (E.continuousCoreToDomain G))
    (hind : ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      0 < E.rootSeminorm (E.continuousCoreToDomain (a • F + b • G)))
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (hμ : ∀ n, μ (carpetCellBoundary n) = 0)
    (hstat : ∀ a b : ℝ,
      E.energyMeasure (E.continuousCoreToDomain (a • F + b • G)) =
        ((E.energy (E.continuousCoreToDomain (a • F + b • G)) : NNReal) : ℝ≥0∞) • μ)
    (χ : E.continuousCore) (hχ : ∀ x ∈ carpetOuterBoundary, χ.val x = 0)
    (hχ01 : ∀ x, χ.val x ∈ Icc (0 : ℝ) 1) :
    let κ := (powerWeightedMeasure p μ χ.val).map
      (E.continuousCoreTuple (![F, G] : Fin 2 → E.continuousCore))
    ∃ ξ : (Fin 2 → ℝ) → ℝ, Measurable ξ ∧ (∀ x, 0 ≤ ξ x) ∧
      Integrable ξ volume ∧ volume.withDensity (fun x ↦ ENNReal.ofReal (ξ x)) = κ ∧
      MemPlanarSobolev p (fun x ↦ ξ x ^ p⁻¹) := by
  obtain ⟨ξ, r, hξ, hξ₀, hξI, hrep, hr⟩ := E.exists_stationary_pair_planar_density h hc F G hF hG
    hind μ hμ hstat χ hχ hχ01
  exact ⟨ξ, hξ, hξ₀, hξI, hrep, memPlanarSobolev_rpow_inv_of_weighted_derivatives E.one_lt_p
    ξ hξ hξ₀ hξI r (fun i ↦ (hr i).1) (fun i ↦ (hr i).2.2)⟩

end CarpetEnergy.SelfSimilarPEnergy
