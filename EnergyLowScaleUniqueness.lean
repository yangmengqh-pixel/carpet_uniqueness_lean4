import EnergyLowScaleRankOne
import EnergyMorreyUniqueness
import EnergyHarnackHarmonicBlowup
import EnergyCellNeighborhoodHarnack

/-!
# Proportionality from the remaining small-scale estimates
-/

open MeasureTheory
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1700000 in
/-- The three conclusions of Theorem 2.3 follow in the low-scale case
if a comparison energy satisfies neighborhood Harnack and the
planar exceptional sets have small weighted cutoffs. -/
theorem proportional_of_low_scale_harnack_and_cutoffs [Fact (1 ≤ ENNReal.ofReal p)]
    (D : SelfSimilarPEnergy p)
    (hρ : E.scalingFactor ≤ 1)
    (hHar : ∃ Q : SelfSimilarPEnergy p, Q.domain = E.domain ∧
      Q.HasLinearFirstVariations ∧
      Q.HasFiniteGeneralizedPContraction (fun f ↦ (Q.energy f : ℝ)) ∧
      ∃ H : ℝ, 1 ≤ H ∧ Q.HasNeighborhoodHarnack H)
    (hcut : HasPlanarWeightedExceptionalCutoffs p) :
    E.scalingFactor = D.scalingFactor ∧ E.domain = D.domain ∧
      ∃ (h : E.domain ≤ D.domain) (c : ℝ), 0 < c ∧
        ∀ f : E.domain, (D.energy (Submodule.inclusion h f) : ℝ) = c * (E.energy f : ℝ) := by
  obtain ⟨Q, hQE, hQderiv, hQcontr, H, hH, hQHar⟩ := hHar
  have hρQ : Q.scalingFactor = E.scalingFactor := Q.scalingFactor_eq E
  have hcompact := Q.hasInteriorHarmonicCompactness_of_neighborhoodHarnack hH hQHar hQcontr
  refine E.proportional_of_reference D Q hQE ?_ (Q.zeroOne_of_neighborhoodHarnack hH hQHar hQcontr)
  intro ν hν hdom
  let : IsFiniteMeasure ν := hν
  exact Q.hasPairwiseEnergyDependence_of_low_scale_cutoffs (hρQ.symm ▸ hρ) hcompact
    hQderiv hQcontr hcut ν hdom

/-- In the low-scale regime the harmonic compactness input follows from
the Harnack inequality for the constructed comparison energy. -/
theorem proportional_of_low_scale_cutoffs
    (D : SelfSimilarPEnergy p) (hρ : E.scalingFactor ≤ 1)
    (hcut : HasPlanarWeightedExceptionalCutoffs p) :
    E.scalingFactor = D.scalingFactor ∧ E.domain = D.domain ∧
      ∃ (h : E.domain ≤ D.domain) (c : ℝ), 0 < c ∧
        ∀ f : E.domain, (D.energy (Submodule.inclusion h f) : ℝ) = c * (E.energy f : ℝ) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨Q, hQE, hρQ, hQcontr, _, hQderiv, hQsymm⟩ :=
    E.exists_selfSimilarPEnergy_with_uniform_first_variations
  exact E.proportional_of_low_scale_harnack_and_cutoffs D hρ
    ⟨Q, hQE, hQderiv, hQcontr,
      Q.exists_neighborhood_harnack_of_scalingFactor_le_one (hρQ.symm ▸ hρ) hQderiv hQcontr hQsymm⟩ hcut

end CarpetEnergy.SelfSimilarPEnergy
