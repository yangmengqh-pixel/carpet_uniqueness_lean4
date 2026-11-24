import EnergyLowScaleRankOne
import PlanarExceptionalCutoffs

/-!
# Pairwise energy dependence in the low walk-dimension case
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 4500000 in
/-- Case 2 of Theorem 5.2 for the smooth comparison energy. -/
theorem hasPairwiseEnergyDependence_of_scalingFactor_le_one
    (hρ : E.scalingFactor ≤ 1)
    (hcompact : E.HasInteriorHarmonicCompactness)
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (σ : Measure CarpetPoints) [IsFiniteMeasure σ] (hdom : ∀ f, E.energyMeasure f ≪ σ) :
    E.HasPairwiseEnergyDependence σ := by
  by_contra hn
  obtain ⟨u, s, ξ, hs, hsfin, ⟨j, hj⟩, hξ, hξ₀, _, hSob, hdomκ⟩ :=
    E.exists_cell_pair_sobolev_dominator_of_not_hasPairwiseEnergyDependence hcompact h hc σ hdom hn
  let H := E.continuousCoreTuple u
  let ν := carpetMeasure.map H
  let κ := (E.pairEnergyMeasure u).map H
  let S := range H
  have hS : IsCompact S := isCompact_range H.continuous
  have hκS : ∀ᵐ z ∂κ, z ∈ S := by
    exact (ae_map_iff (μ := E.pairEnergyMeasure u) H.continuous.measurable.aemeasurable
      (p := fun z ↦ z ∈ S) hS.isClosed.measurableSet).mpr
        (Eventually.of_forall (fun x ↦ mem_range_self x))
  have hp := E.lt_two_of_scalingFactor_le_one hρ
  have hp₀ := zero_lt_one.trans E.one_lt_p
  let a₀ (z : PlanarCoordinates) := ξ z ^ p⁻¹
  have ha₀ : ∀ z, 0 ≤ a₀ z := fun z ↦ Real.rpow_nonneg (hξ₀ z) _
  have haM : Measurable a₀ := (Real.continuous_rpow_const (inv_nonneg.mpr hp₀.le)).measurable.comp hξ
  have hdom' : s • κ ≤ volume.withDensity (fun z ↦ ENNReal.ofReal (a₀ z ^ p)) := by
    simpa only [a₀, Real.rpow_inv_rpow (hξ₀ _) hp₀.ne'] using hdomκ
  obtain ⟨B, hB, hsub, hcutB⟩ := exists_small_weighted_cutoff_set_covering_planar_exceptions E.one_lt_p hp
    ν κ hS hκS hs hsfin haM ha₀ hSob hdom'
  have hνB : 0 < ν Bᶜ := E.map_carpetMeasure_compl_pos_of_small_weighted_cutoffs_in_measure
    h hc u j hj hcutB
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
    (show z ∉ UnboundedUpperBallDensity ν (2 - p) from fun hz ↦ hzB (hsub (Or.inl hz)))
  obtain ⟨b, Rb, hb₀, hbR, hene⟩ := exists_upper_density_bound_of_notMem
    (show z ∉ UnboundedUpperBallDensity κ 2 from fun hz ↦ hzB (hsub (Or.inr hz)))
  apply E.not_exists_planar_density_point_of_scalingFactor_le_one hρ h hc u
  let R := min Ra (min Rb Rc)
  have hR : 0 < R := lt_min haR (lt_min hbR hcR)
  refine ⟨z, a, b, c, R, ha₀, hb₀.le, hc₀.le, hR, fun r hr ↦ ?_⟩
  have hra : r ∈ Ioo 0 Ra := ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
  have hrb : r ∈ Ioo 0 Rb := ⟨hr.1, hr.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hrc : r ∈ Ioo 0 Rc := ⟨hr.1, hr.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  exact ⟨hlow r hra, hvol r hrc, Real.rpow_two r ▸ hene r hrb⟩

end CarpetEnergy.SelfSimilarPEnergy
