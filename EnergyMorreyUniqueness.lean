import EnergyMorreyRankOne
import EnergyProportionality

/-!
# Theorem 2.3 in the Morrey regime

A smooth energy from the graph construction gives a common comparison
for any two Definition 2.1 energies. The rank-one and zero-one arguments
make both comparisons exact up to a positive factor.
-/

open MeasureTheory
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1800000 in
/-- A common reference energy with pairwise dependence and the zero-one
property makes any two Definition 2.1 energies proportional. -/
theorem proportional_of_reference (D Q : SelfSimilarPEnergy p)
    (hQE : Q.domain = E.domain)
    (hQDep : ∀ μ : Measure CarpetPoints, IsFiniteMeasure μ →
      (∀ f, Q.energyMeasure f ≪ μ) → Q.HasPairwiseEnergyDependence μ)
    (hQZero : ∀ μ : Measure CarpetPoints, (∀ f, Q.energyMeasure f ≪ μ) →
      (∀ ν : Measure CarpetPoints, (∀ f, Q.energyMeasure f ≪ ν) → μ ≪ ν) →
      HasZeroOneLaw μ (Sum.elim cellMap carpetSymmetry)) :
    E.scalingFactor = D.scalingFactor ∧ E.domain = D.domain ∧
      ∃ (h : E.domain ≤ D.domain) (c : ℝ), 0 < c ∧
        ∀ f : E.domain, (D.energy (Submodule.inclusion h f) : ℝ) = c * (E.energy f : ℝ) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨hE, cE, hcE, he⟩ := Q.proportional_of_pairwise_dependence_of_zeroOne E hQDep hQZero
  obtain ⟨hD, cD, hcD, hd⟩ := Q.proportional_of_pairwise_dependence_of_zeroOne D hQDep hQZero
  have hED := E.domain_eq D
  refine ⟨E.scalingFactor_eq D, hED, hED.le, cD / cE, div_pos hcD hcE, fun f ↦ ?_⟩
  let g : Q.domain := ⟨f.val, hQE.symm ▸ f.property⟩
  have hEf : Submodule.inclusion hE g = f := Subtype.ext rfl
  have hDf : Submodule.inclusion hD g = Submodule.inclusion hED.le f := Subtype.ext rfl
  have he' := he g
  have hd' := hd g
  rw [hEf] at he'
  rw [hDf] at hd'
  rw [hd', he', div_mul_eq_mul_div, mul_left_comm cD cE]
  exact (mul_div_cancel_left₀ _ hcE.ne').symm

/-- Any two Definition 2.1 energies with renormalization factor greater
than one have the same scale and domain and differ by a positive
constant multiplier. -/
theorem proportional_of_scalingFactor_gt_one (D : SelfSimilarPEnergy p)
    (hρ : 1 < E.scalingFactor) :
    E.scalingFactor = D.scalingFactor ∧ E.domain = D.domain ∧
      ∃ (h : E.domain ≤ D.domain) (c : ℝ), 0 < c ∧
        ∀ f : E.domain, (D.energy (Submodule.inclusion h f) : ℝ) = c * (E.energy f : ℝ) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨Q, hQE, hρQ, hQcontr, _, hQderiv⟩ := E.exists_selfSimilarPEnergy_with_first_variations
  have hρQ' : 1 < Q.scalingFactor := hρQ.symm ▸ hρ
  refine E.proportional_of_reference D Q hQE ?_ (Q.zeroOne_of_scalingFactor_gt_one hρQ')
  intro μ hμ hdom
  let : IsFiniteMeasure μ := hμ
  exact Q.hasPairwiseEnergyDependence_morrey hρQ' hQderiv hQcontr μ hdom

end CarpetEnergy.SelfSimilarPEnergy
