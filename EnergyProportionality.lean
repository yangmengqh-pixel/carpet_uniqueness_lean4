import EnergyBoundaryCovariance
import EnergyWeightedSeminorm
import RankOneApproximation

/-!
# Proportionality from pairwise dependence and a zero-one law

This is the final implication of Section 7. The two remaining analytic
inputs are made explicit in its hypotheses.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The pairwise density-root formulation of p-dependence relative to a
finite common dominating measure. -/
def HasPairwiseEnergyDependence (μ : Measure CarpetPoints) : Prop :=
  ∀ f g : E.domain, ∀ᵐ x ∂μ, ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
    E.energyDensityRoot μ (a • f + b • g) x ≤ ε * (‖a‖ + ‖b‖)

variable (D : SelfSimilarPEnergy p)

private theorem ae_proportional_densities_of_pairwise_dependence
    (h : E.domain ≤ D.domain) (C : ℝ≥0) (hC : 1 ≤ C)
    (hcomp : ∀ f : E.domain, E.energyMeasure f ≤
      (C : ℝ≥0∞) • D.energyMeasure (Submodule.inclusion h f) ∧
      D.energyMeasure (Submodule.inclusion h f) ≤ (C : ℝ≥0∞) • E.energyMeasure f)
    (V : Submodule ℚ E.domain) [Countable V] (d : ℕ → V)
    (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - (d (j n) : E.domain))) atTop (𝓝 0))
    (hdep : E.HasPairwiseEnergyDependence (E.energyReferenceMeasure (fun n ↦ (d n : E.domain)))) :
    let μ := E.energyReferenceMeasure (fun n ↦ (d n : E.domain))
    ∀ᵐ x ∂μ, ∃ c ∈ Icc ((C : ℝ)⁻¹) (C : ℝ),
      ∀ n, (D.energyMeasure (Submodule.inclusion h (d n : E.domain))).rnDeriv μ x =
        ENNReal.ofReal c * (E.energyMeasure (d n : E.domain)).rnDeriv μ x := by
  let u := fun n ↦ (d n : E.domain)
  let μ := E.energyReferenceMeasure u
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hC₁ : 1 ≤ (C : ℝ) := by exact_mod_cast hC
  have hC₀ : 0 < (C : ℝ) := zero_lt_one.trans_le hC₁
  obtain ⟨N, hN, hnull, _, hgood⟩ := E.exists_pointwise_density_comparison D h C hcomp V d hdense
    carpetAllCellBoundaries (E.energyReferenceMeasure_allCellBoundaries_eq_zero u)
  have hrel : ∀ᵐ x ∂μ, ∀ f g : V, ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
      E.energyDensityRoot μ (a • (f : E.domain) + b • (g : E.domain)) x ≤ ε * (‖a‖ + ‖b‖) :=
    ae_all_iff.mpr fun f ↦ ae_all_iff.mpr fun g ↦ hdep f g
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull, hrel] with x hx hr
  obtain ⟨R, T, hRT, hsum⟩ := hgood x hx
  have hsmall : HasSmallRationalRelations R := by
    intro f g ε hε
    obtain ⟨a, b, hab, he⟩ := hr f g ε hε
    exact ⟨a, b, hab, ((hRT (a • f + b • g)).1).le.trans he⟩
  have hpos : ∃ g : V, 0 < R g := by
    by_contra! he
    have hzero (n : ℕ) : R (d n) = 0 := (he (d n)).antisymm (apply_nonneg _ _)
    simp only [hzero, Real.zero_rpow hp.ne', ENNReal.ofReal_zero, mul_zero, tsum_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨g, hg⟩ := hpos
  have hu : 0 < (C : ℝ) ^ p⁻¹ := Real.rpow_pos_of_pos hC₀ _
  have hbound (f : V) : ((C : ℝ)⁻¹) ^ p⁻¹ * R f ≤ T f ∧ T f ≤ (C : ℝ) ^ p⁻¹ * R f := by
    refine ⟨?_, (hRT f).2.2.2.2.2⟩
    rw [Real.inv_rpow hC₀.le, ← div_eq_inv_mul]
    exact (div_le_iff₀ hu).mpr ((hRT f).2.2.2.2.1.trans_eq (mul_comm _ _))
  obtain ⟨c, hc, hmul⟩ := exists_rpow_eq_mul_of_small_relations R T hsmall hp
    (inv_nonneg.mpr hC₀.le) hC₀.le hbound hg
  refine ⟨c, hc, fun n ↦ ?_⟩
  have hc₀ : 0 ≤ c := (inv_nonneg.mpr hC₀.le).trans hc.1
  rw [← (hRT (d n)).2.2.2.1, ← (hRT (d n)).2.2.1, hmul (d n),
    ENNReal.ofReal_mul hc₀]

/-- Once pairwise p-dependence and the zero-one law are available for the
reference energy, every competing energy is a positive multiple of it. -/
theorem proportional_of_pairwise_dependence_of_zeroOne
    (hdep : ∀ (μ : Measure CarpetPoints), IsFiniteMeasure μ →
      (∀ f, E.energyMeasure f ≪ μ) → E.HasPairwiseEnergyDependence μ)
    (hzeroOne : ∀ (μ : Measure CarpetPoints),
      (∀ f, E.energyMeasure f ≪ μ) →
      (∀ ν : Measure CarpetPoints, (∀ f, E.energyMeasure f ≪ ν) → μ ≪ ν) →
      HasZeroOneLaw μ (Sum.elim cellMap carpetSymmetry)) :
    ∃ (h : E.domain ≤ D.domain) (c : ℝ), 0 < c ∧
      ∀ f : E.domain, (D.energy (Submodule.inclusion h f) : ℝ) = c * (E.energy f : ℝ) := by
  obtain ⟨h, C, hC, hcomp⟩ := E.exists_energyMeasure_comparison D
  obtain ⟨V, d, hd, hcontinuous, hdense⟩ := E.exists_energyDense_continuous_ratSubmodule
  have : Countable V := hd.countable
  let u := fun n ↦ (d n : E.domain)
  let μ := E.energyReferenceMeasure u
  have hm (f : E.domain) : E.energyMeasure f ≪ μ :=
    E.energyMeasure_absolutelyContinuous_reference u hdense f
  have hmin (ν : Measure CarpetPoints) (hν : ∀ f, E.energyMeasure f ≪ ν) : μ ≪ ν :=
    E.energyReferenceMeasure_absolutelyContinuous u ν hν
  have hpair := E.ae_proportional_densities_of_pairwise_dependence D h C hC hcomp V d hdense
    (hdep μ (inferInstanceAs (IsFiniteMeasure (E.energyReferenceMeasure u))) hm)
  obtain ⟨a, ha, habounds, hdensity⟩ := E.exists_bounded_common_density_of_ae_proportional D h C hC
    (fun f ↦ (hcomp f).2) u hdense hpair
  have hC₁ : 1 ≤ (C : ℝ) := by exact_mod_cast hC
  have hCpos : 0 < (C : ℝ) := zero_lt_one.trans_le hC₁
  have hlo : 0 < ((C : ℝ)⁻¹) := inv_pos.mpr hCpos
  have hb : ((C : ℝ)⁻¹) ≤ C := ((inv_le_one₀ hCpos).mpr hC₁).trans hC₁
  obtain ⟨c, _, hc, hcprop⟩ := E.proportional_of_common_density D h (E.scalingFactor_eq D)
    E.energyMeasure_inter_cellMap_eq_zero D.energyMeasure_inter_cellMap_eq_zero u
    (fun n ↦ hcontinuous (d n)) hdense (hzeroOne μ hm hmin) ha
    (fun x ↦ hlo.le.trans (habounds x).1) hlo hb
    (Eventually.of_forall habounds) hdensity
  exact ⟨h, c, hc, fun f ↦ (hcprop f).2⟩

end CarpetEnergy.SelfSimilarPEnergy
