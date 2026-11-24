import EnergyStationaryCellDensity
import EnergyPlanarDensityObstruction
import UpperDensityBallCover
import PlanarLowerDensity
import EnergyWeightedCapacityNonconcentration

/-!
# Rank one at low walk dimension from the planar cutoff step
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

/-- The remaining smooth weighted cutoff conclusion for the exceptional
sets in the low-dimensional planar argument. -/
def HasPlanarWeightedExceptionalCutoffs (p : ℝ) : Prop :=
  ∀ (ν κ : Measure PlanarCoordinates) [IsFiniteMeasure ν] [IsFiniteMeasure κ]
    (s : ℝ≥0∞), 0 < s → s ≠ ∞ →
    ∀ ξ : PlanarCoordinates → ℝ, Measurable ξ → (∀ x, 0 ≤ ξ x) → Integrable ξ volume →
      MemPlanarSobolev p (fun x ↦ ξ x ^ p⁻¹) →
      s • κ ≤ volume.withDensity (fun x ↦ ENNReal.ofReal (ξ x)) →
      HasSmallWeightedCutoffsOnCompacts p κ
        (UnboundedUpperBallDensity ν (2 - p) ∪ UnboundedUpperBallDensity κ 2)

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3100000 in
/-- The low walk-dimension case follows from harmonic compactness and the
smooth weighted cutoff conclusion for the two exceptional sets. -/
theorem hasPairwiseEnergyDependence_of_low_scale_cutoffs
    (hρ : E.scalingFactor ≤ 1)
    (hcompact : E.HasInteriorHarmonicCompactness)
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (hcut : HasPlanarWeightedExceptionalCutoffs p)
    (σ : Measure CarpetPoints) [IsFiniteMeasure σ] (hdom : ∀ f, E.energyMeasure f ≪ σ) :
    E.HasPairwiseEnergyDependence σ := by
  by_contra hn
  obtain ⟨u, s, ξ, hs, hsfin, ⟨j, hj⟩, hξ, hξ₀, hξI, hSob, hdomκ⟩ :=
    E.exists_cell_pair_sobolev_dominator_of_not_hasPairwiseEnergyDependence hcompact h hc σ hdom hn
  let H := E.continuousCoreTuple u
  let ν := carpetMeasure.map H
  let κ := (E.pairEnergyMeasure u).map H
  have hp := E.lt_two_of_scalingFactor_le_one hρ
  let B := UnboundedUpperBallDensity ν (2 - p) ∪ UnboundedUpperBallDensity κ 2
  have hB : MeasurableSet B := (measurableSet_unboundedUpperBallDensity ν (sub_nonneg.mpr hp.le)).union
    (measurableSet_unboundedUpperBallDensity κ (by norm_num))
  have hcutB := hcut ν κ s hs hsfin ξ hξ hξ₀ hξI hSob hdomκ
  have hνB : 0 < ν Bᶜ := E.map_carpetMeasure_compl_pos_of_small_weighted_cutoffs
    h hc u j hj hB hcutB
  let A := {z : PlanarCoordinates | ∃ a R : ℝ, 0 < a ∧ 0 < R ∧
    ∀ r ∈ Ioo 0 R, a * r ^ (2 : ℕ) ≤ ν.real (ball z r)}
  have hA : ∀ᵐ z ∂ν, z ∈ A := ae_planar_ball_lower_density ν
  have hpt : (A \ B).Nonempty := by
    by_contra hnone
    have hν : ∀ᵐ z ∂ν, z ∈ B := hA.mono fun z hz ↦ by
      by_contra hzb
      exact hnone ⟨z, hz, hzb⟩
    have hnull : ν Bᶜ = 0 := ae_iff.mp hν
    exact hνB.ne' hnull
  obtain ⟨z, ha, hzB⟩ := hpt
  obtain ⟨a, Ra, ha₀, haR, hlow⟩ := ha
  obtain ⟨c, Rc, hc₀, hcR, hvol⟩ := exists_upper_density_bound_of_notMem
    (show z ∉ UnboundedUpperBallDensity ν (2 - p) from fun hz ↦ hzB (Or.inl hz))
  obtain ⟨b, Rb, hb₀, hbR, hene⟩ := exists_upper_density_bound_of_notMem
    (show z ∉ UnboundedUpperBallDensity κ 2 from fun hz ↦ hzB (Or.inr hz))
  apply E.not_exists_planar_density_point_of_scalingFactor_le_one hρ h hc u
  let R := min Ra (min Rb Rc)
  have hR : 0 < R := lt_min haR (lt_min hbR hcR)
  refine ⟨z, a, b, c, R, ha₀, hb₀.le, hc₀.le, hR, fun r hr ↦ ?_⟩
  have hra : r ∈ Ioo 0 Ra := ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
  have hrb : r ∈ Ioo 0 Rb := ⟨hr.1, hr.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hrc : r ∈ Ioo 0 Rc := ⟨hr.1, hr.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  exact ⟨hlow r hra, hvol r hrc, Real.rpow_two r ▸ hene r hrb⟩

end SelfSimilarPEnergy
end CarpetEnergy
