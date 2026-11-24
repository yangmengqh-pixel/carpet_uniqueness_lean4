import EnergyStationaryPlanarSobolev
import EnergyPairCellPushforward
import EnergyFixedRealDirections
import EnergyCompactCutoff
import CarpetGoodCells

/-!
# A Sobolev density dominating a positive-energy cell pushforward
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3800000 in
/-- Without pairwise energy dependence, harmonic compactness and the
stationary blowup give an interior cell whose pair pushforward is
dominated, after rescaling, by a density with Sobolev (p)-th root. -/
theorem exists_cell_pair_sobolev_dominator_of_not_hasPairwiseEnergyDependence
    (hcompact : E.HasInteriorHarmonicCompactness)
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (ν : Measure CarpetPoints) [IsFiniteMeasure ν] (hdom : ∀ f, E.energyMeasure f ≪ ν)
    (hn : ¬ E.HasPairwiseEnergyDependence ν) :
    ∃ (u : Fin 2 → E.continuousCore) (s : ℝ≥0∞) (ξ : (Fin 2 → ℝ) → ℝ),
      0 < s ∧ s ≠ ∞ ∧ (∃ j, 0 < E.rootSeminorm (E.continuousCoreToDomain (u j))) ∧
      Measurable ξ ∧ (∀ x, 0 ≤ ξ x) ∧ Integrable ξ volume ∧
      MemPlanarSobolev p (fun x ↦ ξ x ^ p⁻¹) ∧
      s • (E.pairEnergyMeasure u).map (E.continuousCoreTuple u) ≤
        volume.withDensity (fun x ↦ ENNReal.ofReal (ξ x)) := by
  obtain ⟨f, g, U, V, d, hf, hg, hU, hV, hsum, hd, hdirs⟩ :=
    E.exists_fixed_real_directions_of_not_hasPairwiseEnergyDependence hcompact ν hdom hn
  have hUmem : continuousLp p U ∈ E.domain := hU.symm ▸ f.property
  have hVmem : continuousLp p V ∈ E.domain := hV.symm ▸ g.property
  let F : E.continuousCore := ⟨U, hUmem⟩
  let G : E.continuousCore := ⟨V, hVmem⟩
  have hF : E.continuousCoreToDomain F = f := Subtype.ext hU
  have hG : E.continuousCoreToDomain G = g := Subtype.ext hV
  let W : Fin 2 → E.continuousCore := ![F, G]
  let μ := E.pairEnergyMeasure W
  have hμeq : μ = E.energyMeasure f + E.energyMeasure g := by
    change E.energyMeasure (E.continuousCoreToDomain F) +
      E.energyMeasure (E.continuousCoreToDomain G) = _
    rw [hF, hG]
  have hμprob : μ univ = 1 := by
    rw [hμeq, add_apply, E.energyMeasure_univ, E.energyMeasure_univ, ← ENNReal.coe_add]
    exact ENNReal.coe_eq_one.mpr (NNReal.eq hsum)
  have hμOuter : μ carpetOuterBoundary = 0 := by
    simp only [hμeq, add_apply, E.energyMeasure_carpetOuterBoundary_eq_zero, add_zero]
  have hμCell (n : ℕ) : μ (carpetCellBoundary n) = 0 := by
    simp only [hμeq, add_apply,
      E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero, add_zero]
  obtain ⟨_, _, hcells⟩ := exists_good_interior_cells μ hμprob hμOuter hμCell univ
    MeasurableSet.univ (hμprob ▸ one_pos) 0
  obtain ⟨n, w, hw, _, hwin, _⟩ := (hcells 1 one_pos).exists
  let v := List.ofFn w
  have hvin : range (wordMap v) ⊆ carpetOuterBoundaryᶜ :=
    fun x hx ↦ hwin (mem_iUnion₂.mpr ⟨w, self_mem_cellNeighborhood w 0, hx⟩)
  obtain ⟨χ, hχTrace, hχCell, hχ01⟩ := E.exists_core_cutoff
    isClosed_carpetOuterBoundary.isOpen_compl (isCompact_range (continuous_wordMap v)).isClosed hvin
  have hind (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
      0 < E.rootSeminorm (E.continuousCoreToDomain (a • F + b • G)) := by
    have hcoef : 0 < |a| + |b| := hab.elim
      (fun ha ↦ add_pos_of_pos_of_nonneg (abs_pos.mpr ha) (abs_nonneg _))
      (fun hb ↦ add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr hb))
    have he := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (mul_pos hd hcoef) p)).trans_le (hdirs a b).1
    rw [map_add, map_smul, map_smul, hF, hG, E.rootSeminorm_apply]
    have hpos : 0 < (E.energy (a • f + b • g) : ℝ) := by exact_mod_cast ENNReal.coe_pos.mp he
    exact Real.rpow_pos_of_pos hpos _
  have hstat (a b : ℝ) : E.energyMeasure (E.continuousCoreToDomain (a • F + b • G)) =
      ((E.energy (E.continuousCoreToDomain (a • F + b • G)) : NNReal) : ℝ≥0∞) • μ := by
    rw [map_add, map_smul, map_smul, hF, hG, hμeq]
    exact (hdirs a b).2.2
  obtain ⟨ξ, hξ, hξ₀, hξI, hrep, hSob⟩ := E.exists_stationary_pair_planar_sobolev_density
    h hc F G (hF.symm ▸ hf) (hG.symm ▸ hg) hind μ hμCell hstat χ
    (fun x hx ↦ hχTrace x (fun hn ↦ hn hx)) hχ01
  let u (i : Fin 2) := E.wordPullbackCore v (W i)
  let s := ENNReal.ofReal E.scalingFactor ^ v.length
  have hs : 0 < ENNReal.ofReal E.scalingFactor :=
    ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1
  have hmass := E.pairEnergyMeasure_univ_wordPullback_pos W v hw
  have hpos : ∃ j, 0 < E.rootSeminorm (E.continuousCoreToDomain (u j)) := by
    by_contra! hnon
    have hzero (j : Fin 2) : E.rootSeminorm (E.continuousCoreToDomain (u j)) = 0 :=
      (hnon j).antisymm (apply_nonneg E.rootSeminorm _)
    have he (j : Fin 2) : E.energy (E.continuousCoreToDomain (u j)) = 0 := by
      have hh := hzero j
      rw [E.rootSeminorm_apply, Real.rpow_eq_zero_iff_of_nonneg (NNReal.coe_nonneg _)] at hh
      exact_mod_cast hh.1
    change 0 < E.pairEnergyMeasure u univ at hmass
    simp only [pairEnergyMeasure, add_apply, E.energyMeasure_univ, he, ENNReal.coe_zero, add_zero,
      lt_irrefl] at hmass
  refine ⟨u, s, ξ, pos_iff_ne_zero.mpr (pow_ne_zero _ hs.ne'), ENNReal.pow_ne_top ENNReal.ofReal_ne_top,
    hpos, hξ, hξ₀, hξI, hSob, ?_⟩
  rw [hrep]
  exact E.smul_map_pairEnergyMeasure_wordPullback_le W χ v hχCell

end CarpetEnergy.SelfSimilarPEnergy
