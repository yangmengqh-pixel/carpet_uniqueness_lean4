import EnergyDominance
import EnergyLipschitz
import EnergySymmetry

/-!
# Self-similar components

The energy measure of an invariant Borel set satisfies (Q1)–(Q5).
This is the component construction in Lemma 6.7.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A functional satisfying (Q1)–(Q5) of Section 6. -/
structure SelfSimilarComponent where
  mass : E.domain → ℝ≥0
  rootSeminorm : Seminorm ℝ E.domain
  rootSeminorm_apply : ∀ f, rootSeminorm f = (mass f : ℝ) ^ p⁻¹
  mass_le_energy : ∀ f, mass f ≤ E.energy f
  selfSimilar : ∀ f, (mass f : ℝ≥0∞) =
    ENNReal.ofReal E.scalingFactor * ∑ i : Fin 8, (mass (E.pullback i f) : ℝ≥0∞)
  symmetry : ∀ σ f, mass (E.pullbackSymmetry σ f) = mass f
  contraction : ∀ {L : ℝ≥0} {φ : ℝ → ℝ}, LipschitzWith L φ → ∀ f g : E.domain,
    (g : CarpetLp p) =ᵐ[carpetMeasure] φ ∘ (f : CarpetLp p) → mass g ≤ L ^ p * mass f

private theorem energyMeasure_preimage_eq_of_invariant
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    {A : Set CarpetPoints} {τ : CarpetPoints → CarpetPoints}
    (h : ∀ᵐ x ∂μ, τ x ∈ A ↔ x ∈ A) (f : E.domain) :
    E.energyMeasure f (τ ⁻¹' A) = E.energyMeasure f A := by
  have hEq : (τ ⁻¹' A : Set CarpetPoints) =ᵐ[E.energyMeasure f] A :=
    h.filter_mono (Measure.AbsolutelyContinuous.ae_le (hdom f))
  exact measure_congr hEq

private theorem energyMeasure_pullbackSymmetry_apply_of_invariant
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    {A : Set CarpetPoints} (hA : MeasurableSet A)
    (hsym : ∀ σ, ∀ᵐ x ∂μ, carpetSymmetry σ x ∈ A ↔ x ∈ A)
    (σ : SquareSymmetry) (f : E.domain) :
    E.energyMeasure (E.pullbackSymmetry σ f) A = E.energyMeasure f A := by
  rw [E.energyMeasure_pullbackSymmetry, Measure.map_apply
    (continuous_carpetSymmetry (inverseSymmetry σ)).measurable hA]
  exact E.energyMeasure_preimage_eq_of_invariant hdom (hsym (inverseSymmetry σ)) f

private theorem energyMeasure_apply_toNNReal_comp_le
    {L : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith L φ) (f g : E.domain)
    (hg : (g : CarpetLp p) =ᵐ[carpetMeasure] φ ∘ (f : CarpetLp p))
    (A : Set CarpetPoints) :
    (E.energyMeasure g A).toNNReal ≤ L ^ p * (E.energyMeasure f A).toNNReal := by
  obtain ⟨v, hv, hmass⟩ := E.exists_energyMeasure_comp_le hφ f
  have heq : v = g := Subtype.ext (Lp.ext (hv.trans hg.symm))
  rw [heq] at hmass
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (measure_ne_top (E.energyMeasure f) A),
    ENNReal.coe_toNNReal (measure_ne_top (E.energyMeasure g) A)]
  exact hmass A

/-- The mass of an invariant Borel set defines a component of the original energy. -/
noncomputable def componentOfInvariantSet
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (A : Set CarpetPoints) (hA : MeasurableSet A)
    (hcell : ∀ i : Fin 8, ∀ᵐ x ∂μ, cellMap i x ∈ A ↔ x ∈ A)
    (hsym : ∀ σ, ∀ᵐ x ∂μ, carpetSymmetry σ x ∈ A ↔ x ∈ A) :
    E.SelfSimilarComponent where
  mass f := (E.energyMeasure f A).toNNReal
  rootSeminorm := E.energyMeasureSeminorm A hA
  rootSeminorm_apply f := E.energyMeasureSeminorm_apply A hA f
  mass_le_energy f := by
    have h := measure_mono (μ := E.energyMeasure f) (subset_univ A)
    rw [E.energyMeasure_univ] at h
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (measure_ne_top (E.energyMeasure f) A)]
    exact h
  selfSimilar f := by
    simp only [ENNReal.coe_toNNReal (measure_ne_top (E.energyMeasure _) A)]
    conv_lhs => rw [E.energyMeasure_eq_sum_cells f]
    rw [Measure.sum_apply _ hA, tsum_fintype, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_apply, smul_eq_mul, Measure.map_apply (continuous_cellMap i).measurable hA,
      E.energyMeasure_preimage_eq_of_invariant hdom (hcell i)]
  symmetry σ f := congrArg ENNReal.toNNReal
    (E.energyMeasure_pullbackSymmetry_apply_of_invariant hdom hA hsym σ f)
  contraction hφ f g hg := E.energyMeasure_apply_toNNReal_comp_le hφ f g hg A

theorem componentOfInvariantSet_mass
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (A : Set CarpetPoints) (hA : MeasurableSet A)
    (hcell : ∀ i : Fin 8, ∀ᵐ x ∂μ, cellMap i x ∈ A ↔ x ∈ A)
    (hsym : ∀ σ, ∀ᵐ x ∂μ, carpetSymmetry σ x ∈ A ↔ x ∈ A)
    (f : E.domain) :
    (((E.componentOfInvariantSet hdom A hA hcell hsym).mass f : ℝ≥0) : ℝ≥0∞) =
      E.energyMeasure f A :=
  ENNReal.coe_toNNReal (measure_ne_top _ _)

end CarpetEnergy.SelfSimilarPEnergy
