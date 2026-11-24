import EnergyLowScaleRankOneProof
import EnergyCellNeighborhoodHarnack
import EnergyMorreyUniqueness
import EnergyHarnackHarmonicBlowup

/-!
# Uniqueness of a Definition 2.1 self-similar energy
-/

open MeasureTheory
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ}

/-- Two Definition 2.1 energies have the same scale and domain and
differ by a single positive multiplier. -/
theorem proportional (E D : SelfSimilarPEnergy p) :
    E.scalingFactor = D.scalingFactor ∧ E.domain = D.domain ∧
      ∃ (h : E.domain ≤ D.domain) (c : ℝ), 0 < c ∧
        ∀ f : E.domain, (D.energy (Submodule.inclusion h f) : ℝ) = c * (E.energy f : ℝ) := by
  by_cases hρ : 1 < E.scalingFactor
  · exact E.proportional_of_scalingFactor_gt_one D hρ
  have hρ₀ : E.scalingFactor ≤ 1 := le_of_not_gt hρ
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨Q, hQE, hρQ, hQcontr, _, hQderiv, hQsymm⟩ :=
    E.exists_selfSimilarPEnergy_with_uniform_first_variations
  have hQρ : Q.scalingFactor ≤ 1 := hρQ.symm ▸ hρ₀
  obtain ⟨H, hH, hHar⟩ := Q.exists_neighborhood_harnack_of_scalingFactor_le_one hQρ hQderiv hQcontr hQsymm
  have hcompact := Q.hasInteriorHarmonicCompactness_of_neighborhoodHarnack hH hHar hQcontr
  refine E.proportional_of_reference D Q hQE ?_ (Q.zeroOne_of_neighborhoodHarnack hH hHar hQcontr)
  intro ν hν hdom
  let : IsFiniteMeasure ν := hν
  exact Q.hasPairwiseEnergyDependence_of_scalingFactor_le_one hQρ hcompact hQderiv hQcontr ν hdom

/-- Theorem 2.3, with the reference energy supplied as a Definition 2.1
energy. The multiplier is oriented as in the manuscript. -/
theorem theorem_2_3 (E canonical : SelfSimilarPEnergy p) :
    E.scalingFactor = canonical.scalingFactor ∧ E.domain = canonical.domain ∧
      ∃ (h : canonical.domain ≤ E.domain) (c : ℝ), 0 < c ∧
        ∀ f : canonical.domain,
          (E.energy (Submodule.inclusion h f) : ℝ) = c * (canonical.energy f : ℝ) := by
  obtain ⟨hρ, hF, h⟩ := canonical.proportional E
  exact ⟨hρ.symm, hF.symm, h⟩

end CarpetEnergy.SelfSimilarPEnergy
