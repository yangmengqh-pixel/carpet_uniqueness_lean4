import EnergyPlanarPowerWeight
import EnergyFirstVariation
import PlanarDensityWeakDerivative

/-!
# Planar density of a stationary harmonic pair

The independent stationary harmonic pair gives two independent
first-variation rows. The exact weighted test estimates identify
the weak derivatives of the planar Lebesgue density.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3000000 in
/-- The weighted derivative conclusion of Proposition 5.6 for a
continuous stationary independent harmonic pair. -/
theorem exists_stationary_pair_planar_density
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
    ∃ (ξ : (Fin 2 → ℝ) → ℝ) (r : Fin 2 → (Fin 2 → ℝ) → ℝ),
      Measurable ξ ∧ (∀ x, 0 ≤ ξ x) ∧ Integrable ξ volume ∧
      volume.withDensity (fun x ↦ ENNReal.ofReal (ξ x)) = κ ∧
      ∀ i, Measurable (r i) ∧ MemLp (r i) (ENNReal.ofReal p) κ ∧
        Integrable (fun x ↦ -(ξ x * r i x)) volume ∧
        HasWeakDirectionalDerivative volume ξ (fun x ↦ -(ξ x * r i x)) (planarDirection i) ∧
        MemLp (fun x ↦ ξ x ^ p⁻¹ * r i x) (ENNReal.ofReal p) volume := by
  let f := E.continuousCoreToDomain F
  let g := E.continuousCoreToDomain G
  let H : Fin 2 → E.continuousCore := ![F, G]
  let κ := (powerWeightedMeasure p μ χ.val).map (E.continuousCoreTuple H)
  let : IsFiniteMeasure (powerWeightedMeasure p μ χ.val) := isFiniteMeasure_of_le _
    (powerWeightedMeasure_le p (zero_lt_one.trans E.one_lt_p) μ χ.val hχ01)
  let : IsFiniteMeasure κ := inferInstanceAs (IsFiniteMeasure
    ((powerWeightedMeasure p μ χ.val).map (E.continuousCoreTuple H)))
  let l₀ := (E.variation h f).comp E.continuousCoreToDomain
  let l₁ := (E.variation h g).comp E.continuousCoreToDomain
  have hdF (v : E.continuousCore) : HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (F + t • v)) : ℝ)) (p * l₀ v) 0 := by
    simp only [map_add, map_smul, l₀, LinearMap.comp_apply]
    exact E.hasDerivAt_energy_variation h f _
  have hdG (v : E.continuousCore) : HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (G + t • v)) : ℝ)) (p * l₁ v) 0 := by
    simp only [map_add, map_smul, l₁, LinearMap.comp_apply]
    exact E.hasDerivAt_energy_variation h g _
  have hdet := E.first_variation_matrix_det_ne_zero_of_independent F G l₀ l₁ hind hdF hdG
  have hLine (u : E.continuousCore) (i : Fin 2) (t : ℝ) (hs : u = F ∨ u = G) :
      E.energyMeasure (E.continuousCoreToDomain u + t • E.continuousCoreToDomain (H i)) =
        ((E.energy (E.continuousCoreToDomain u + t • E.continuousCoreToDomain (H i)) : NNReal) : ℝ≥0∞) • μ := by
    rw [← map_smul, ← map_add]
    rcases hs with hu | hu <;> subst u <;> fin_cases i
    · have e := hstat (1 + t) 0
      simp only [add_smul, one_smul, zero_smul, add_zero] at e
      exact e
    · have e := hstat 1 t
      simp only [one_smul] at e
      exact e
    · have e := hstat t 1
      rw [one_smul, add_comm] at e
      exact e
    · have e := hstat 0 (1 + t)
      simp only [add_smul, one_smul, zero_smul, zero_add] at e
      exact e
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent E.one_lt_p
  let B (u : E.domain) := p * (E.energy u : ℝ) ^ q⁻¹ * (E.energy (E.continuousCoreToDomain χ) : ℝ) ^ p⁻¹
  have hB (u : E.domain) : 0 ≤ B u := by
    have hp := hpq.nonneg
    dsimp only [B]
    positivity
  have hRows (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ)
      (_hφs : HasCompactSupport φ) :
      let X := ∫ x, fderiv ℝ φ x (planarDirection 0) ∂κ
      let Y := ∫ x, fderiv ℝ φ x (planarDirection 1) ∂κ
      let N := (∫ x, |φ x| ^ q ∂κ) ^ q⁻¹
      |l₀ F * X + l₀ G * Y| ≤ B f * N ∧ |l₁ F * X + l₁ G * Y| ≤ B g * N := by
    have h₀ := E.abs_planar_power_row_le h hc f hF H μ hμ (fun i t ↦ hLine F i t (Or.inl rfl))
      χ hχ (fun x ↦ (hχ01 x).1) φ hφ
    have h₁ := E.abs_planar_power_row_le h hc g hG H μ hμ (fun i t ↦ hLine G i t (Or.inr rfl))
      χ hχ (fun x ↦ (hχ01 x).1) φ hφ
    dsimp only at h₀ h₁
    rw [Fin.sum_univ_two] at h₀ h₁
    exact ⟨h₀, h₁⟩
  have hAC := absoluteContinuous_of_weighted_planar_rows κ hpq.symm.nonneg
    (hB f) (hB g) hdet hRows
  obtain ⟨r, hr, hder⟩ := exists_weighted_coordinate_densities_of_planar_rows κ hpq
    (hB f) (hB g) hdet hRows
  obtain ⟨ξ, hξm, hξ, hξI, hξrep, hξD⟩ :=
    exists_planar_density_with_weak_derivative κ hAC E.one_lt_p r hr hder
  exact ⟨ξ, r, hξm, hξ, hξI, hξrep, fun i ↦ ⟨(hr i).1, (hr i).2, hξD i⟩⟩

end CarpetEnergy.SelfSimilarPEnergy
