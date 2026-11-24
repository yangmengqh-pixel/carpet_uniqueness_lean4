import EnergyPlanarPowerWeight
import EnergyMorreyHarmonicBlowup
import EnergyFixedRealDirections
import EnergyFirstVariation
import HarmonicMorreyObstruction

/-!
# Rank one for the smooth graph-limit energy in the Morrey regime
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
private theorem stationary_line {f g : E.domain} (μ : Measure CarpetPoints)
    (hs : ∀ a b : ℝ, E.energyMeasure (a • f + b • g) =
      ((E.energy (a • f + b • g) : NNReal) : ℝ≥0∞) • μ)
    (i j : Fin 2) (t : ℝ) :
    E.energyMeasure ((![f, g] : Fin 2 → E.domain) i + t • (![f, g] : Fin 2 → E.domain) j) =
      ((E.energy ((![f, g] : Fin 2 → E.domain) i + t • (![f, g] : Fin 2 → E.domain) j) : NNReal) : ℝ≥0∞) • μ := by
  fin_cases i <;> fin_cases j
  · have he : (1 + t) • f + (0 : ℝ) • g = f + t • f := by rw [add_smul, one_smul, zero_smul, add_zero]
    have h := hs (1 + t) 0
    rw [he] at h
    exact h
  · have h := hs 1 t
    rw [one_smul] at h
    exact h
  · have he : t • f + (1 : ℝ) • g = g + t • f := by rw [one_smul, add_comm]
    have h := hs t 1
    rw [he] at h
    exact h
  · have he : (0 : ℝ) • f + (1 + t) • g = g + t • g := by rw [zero_smul, zero_add, add_smul, one_smul]
    have h := hs 0 (1 + t)
    rw [he] at h
    exact h

set_option maxHeartbeats 3500000 in
/-- Harmonic compactness and the planar row estimates yield pairwise
dependence for the smooth reference energy when its scaling factor
exceeds one. -/
theorem hasPairwiseEnergyDependence_morrey (hρ : 1 < E.scalingFactor)
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (ν : Measure CarpetPoints) [IsFiniteMeasure ν] (hdom : ∀ f, E.energyMeasure f ≪ ν) :
    E.HasPairwiseEnergyDependence ν := by
  by_contra hn
  have hp := zero_lt_one.trans E.one_lt_p
  obtain ⟨f, g, U, V, d, hf, hg, hU, hV, hsum, hd, hdirs⟩ :=
    E.exists_fixed_real_directions_of_not_hasPairwiseEnergyDependence
      (E.hasInteriorHarmonicCompactness_of_scalingFactor_gt_one hρ) ν hdom hn
  have hUmem : continuousLp p U ∈ E.domain := hU.symm ▸ f.property
  have hVmem : continuousLp p V ∈ E.domain := hV.symm ▸ g.property
  let F : E.continuousCore := ⟨U, hUmem⟩
  let G : E.continuousCore := ⟨V, hVmem⟩
  have hF : E.continuousCoreToDomain F = f := Subtype.ext hU
  have hG : E.continuousCoreToDomain G = g := Subtype.ext hV
  let μ := E.energyMeasure f + E.energyMeasure g
  let : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (E.energyMeasure f + E.energyMeasure g))
  have hμ₀ : 0 < μ univ := by
    have he : μ univ = 1 := by
      dsimp only [μ]
      rw [add_apply, E.energyMeasure_univ, E.energyMeasure_univ, ← ENNReal.coe_add]
      exact ENNReal.coe_eq_one.mpr (NNReal.eq hsum)
    rw [he]
    exact one_pos
  have hμOuter : μ carpetOuterBoundary = 0 := by
    simp only [μ, add_apply, E.energyMeasure_carpetOuterBoundary_eq_zero, add_zero]
  have hμCell (n : ℕ) : μ (carpetCellBoundary n) = 0 := by
    simp only [μ, add_apply,
      E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero, add_zero]
  obtain ⟨χ, hχmem, hχsupport, hχ01, hχMass⟩ := E.exists_positive_interior_weight μ hμ₀ hμOuter
  let χ₀ : E.continuousCore := ⟨χ, hχmem⟩
  have hχTrace (x : CarpetPoints) (hx : x ∈ carpetOuterBoundary) : χ₀.val x = 0 := by
    by_contra hne
    exact hχsupport (subset_closure (mem_support.mpr hne)) hx
  let H : Fin 2 → E.continuousCore := ![F, G]
  let K := E.continuousCoreTuple H
  let ω := powerWeightedMeasure p μ χ
  let : IsFiniteMeasure ω := isFiniteMeasure_of_le _ (powerWeightedMeasure_le p hp μ χ hχ01)
  let κ := ω.map K
  let : IsFiniteMeasure κ := inferInstanceAs (IsFiniteMeasure (ω.map K))
  let l₀ := (E.variation h f).comp E.continuousCoreToDomain
  let l₁ := (E.variation h g).comp E.continuousCoreToDomain
  have hind (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
      0 < E.rootSeminorm (E.continuousCoreToDomain (a • F + b • G)) := by
    have hcoef : 0 < |a| + |b| := hab.elim
      (fun ha ↦ add_pos_of_pos_of_nonneg (abs_pos.mpr ha) (abs_nonneg _))
      (fun hb ↦ add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr hb))
    have he := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (mul_pos hd hcoef) p)).trans_le (hdirs a b).1
    rw [map_add, map_smul, map_smul, hF, hG, E.rootSeminorm_apply]
    have hpos : 0 < (E.energy (a • f + b • g) : ℝ) := by exact_mod_cast (ENNReal.coe_pos.mp he)
    exact Real.rpow_pos_of_pos hpos _
  have hdF (v : E.continuousCore) : HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (F + t • v)) : ℝ)) (p * l₀ v) 0 := by
    simp only [map_add, map_smul, hF, l₀, LinearMap.comp_apply]
    exact E.hasDerivAt_energy_variation h f _
  have hdG (v : E.continuousCore) : HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (G + t • v)) : ℝ)) (p * l₁ v) 0 := by
    simp only [map_add, map_smul, hG, l₁, LinearMap.comp_apply]
    exact E.hasDerivAt_energy_variation h g _
  have hdet := E.first_variation_matrix_det_ne_zero_of_independent F G l₀ l₁ hind hdF hdG
  have hstat (a b : ℝ) : E.energyMeasure (a • f + b • g) =
      ((E.energy (a • f + b • g) : NNReal) : ℝ≥0∞) • μ := (hdirs a b).2.2
  have hstat₀ (i : Fin 2) (t : ℝ) :
      E.energyMeasure (f + t • E.continuousCoreToDomain (H i)) =
        ((E.energy (f + t • E.continuousCoreToDomain (H i)) : NNReal) : ℝ≥0∞) • μ := by
    have he : E.continuousCoreToDomain (H i) = (![f, g] : Fin 2 → E.domain) i := by
      fin_cases i
      · exact hF
      · exact hG
    rw [he]
    exact E.stationary_line μ hstat 0 i t
  have hstat₁ (i : Fin 2) (t : ℝ) :
      E.energyMeasure (g + t • E.continuousCoreToDomain (H i)) =
        ((E.energy (g + t • E.continuousCoreToDomain (H i)) : NNReal) : ℝ≥0∞) • μ := by
    have he : E.continuousCoreToDomain (H i) = (![f, g] : Fin 2 → E.domain) i := by
      fin_cases i
      · exact hF
      · exact hG
    rw [he]
    exact E.stationary_line μ hstat 1 i t
  let q := p.conjExponent
  let B (u : E.domain) :=
    p * (E.energy u : ℝ) ^ q⁻¹ * (E.energy (E.continuousCoreToDomain χ₀) : ℝ) ^ p⁻¹
  have hB (u : E.domain) : 0 ≤ B u := by dsimp only [B]; positivity
  let W := (κ.real univ) ^ q⁻¹
  have hW : 0 ≤ W := Real.rpow_nonneg measureReal_nonneg _
  have hψ (φ : (Fin 2 → ℝ) → ℝ) (_hφ : ContDiff ℝ 1 φ) (h01 : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
      (∫ x, |φ x| ^ q ∂κ) ^ q⁻¹ ≤ W := by
    have hq := (Real.HolderConjugate.conjExponent E.one_lt_p).symm.nonneg
    have hpoint (x : Fin 2 → ℝ) : |φ x| ^ q ≤ (1 : ℝ) := by
      rw [abs_of_nonneg (h01 x).1]
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (h01 x).1 (h01 x).2 hq
    have hi := integral_mono_of_nonneg
      (μ := κ) (f := fun x ↦ |φ x| ^ q) (g := fun _ ↦ (1 : ℝ))
      (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
      (integrable_const (1 : ℝ)) (Eventually.of_forall hpoint)
    rw [integral_const, smul_eq_mul, mul_one] at hi
    exact Real.rpow_le_rpow (integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)) hi (inv_nonneg.mpr hq)
  obtain ⟨C, hC, hgrad⟩ := hasBoundedDistributionalGradient_of_planar_rows κ
    (l₀ F) (l₀ G) (l₁ F) (l₁ G) (B f * W) (B g * W)
    (mul_nonneg (hB f) hW) (mul_nonneg (hB g) hW) hdet (by
      intro φ hφ _ h01
      have h₀ := E.abs_planar_power_row_le h hc f hf H μ hμCell hstat₀ χ₀ hχTrace (fun x ↦ (hχ01 x).1) φ hφ
      have h₁ := E.abs_planar_power_row_le h hc g hg H μ hμCell hstat₁ χ₀ hχTrace (fun x ↦ (hχ01 x).1) φ hφ
      have hbound₀ := h₀.trans (mul_le_mul_of_nonneg_left (hψ φ hφ h01) (hB f))
      have hbound₁ := h₁.trans (mul_le_mul_of_nonneg_left (hψ φ hφ h01) (hB g))
      constructor
      · rw [Fin.sum_univ_two] at hbound₀
        exact hbound₀
      · rw [Fin.sum_univ_two] at hbound₁
        exact hbound₁)
  have hK : (K : CarpetPoints → (Fin 2 → ℝ)) = fun x ↦ ![U x, V x] := by
    funext x j
    fin_cases j <;> rfl
  have h0 : 0 < ω univ := hχMass
  have hgrad' : HasBoundedDistributionalGradient (ω.map fun x ↦ (![U x, V x] : Fin 2 → ℝ)) C := by
    change HasBoundedDistributionalGradient (ω.map K) C at hgrad
    rwa [hK] at hgrad
  exact E.not_hasBoundedDistributionalGradient_map_pair hρ U V hUmem hVmem ω h0 C hC hgrad'

end CarpetEnergy.SelfSimilarPEnergy
