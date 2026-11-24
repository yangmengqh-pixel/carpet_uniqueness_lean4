import EnergyProportionality
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Changing the reference measure for pairwise dependence

The pair measure used in Section 5 is the sum of the two energy
measures. The Radon–Nikodym chain rule transfers the conclusion to the
common reference measure used in Section 7.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem energyMeasure_add_rat_smul_absolutelyContinuous
    (f g : E.domain) (a b : ℚ) :
    E.energyMeasure (a • f + b • g) ≪ E.energyMeasure f + E.energyMeasure g := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  apply Measure.AbsolutelyContinuous.mk
  intro A hA h
  rw [add_apply] at h
  have hf : E.energyMeasure f A = 0 :=
    nonpos_iff_eq_zero.mp ((le_add_of_nonneg_right bot_le).trans_eq h)
  have hg : E.energyMeasure g A = 0 :=
    nonpos_iff_eq_zero.mp ((le_add_of_nonneg_left bot_le).trans_eq h)
  let S := E.energyMeasureSeminorm A hA
  have hSf : S f = 0 := by
    rw [E.energyMeasureSeminorm_apply A hA f, Measure.real, hf, ENNReal.toReal_zero,
      Real.zero_rpow (inv_ne_zero hp.ne')]
  have hSg : S g = 0 := by
    rw [E.energyMeasureSeminorm_apply A hA g, Measure.real, hg, ENNReal.toReal_zero,
      Real.zero_rpow (inv_ne_zero hp.ne')]
  have hh := map_add_le_add S (a • f) (b • g)
  change S (a • f + b • g) ≤ S (a • f) + S (b • g) at hh
  rw [← Rat.cast_smul_eq_qsmul ℝ a f, ← Rat.cast_smul_eq_qsmul ℝ b g,
    map_smul_eq_mul, map_smul_eq_mul, hSf, hSg, mul_zero, mul_zero, add_zero] at hh
  have hz : S (a • f + b • g) = 0 := hh.antisymm (apply_nonneg _ _)
  rw [E.energyMeasureSeminorm_apply A hA, Measure.real] at hz
  have h' := (Real.rpow_eq_zero ENNReal.toReal_nonneg (inv_ne_zero hp.ne')).mp hz
  rw [← ENNReal.ofReal_toReal (measure_ne_top (E.energyMeasure (a • f + b • g)) A),
    h', ENNReal.ofReal_zero]

/-- Pairwise p-dependence relative to the sum of each pair's energy measures. -/
def HasPairwiseDependenceOnPairMeasures : Prop :=
  ∀ f g : E.domain, ∀ᵐ x ∂(E.energyMeasure f + E.energyMeasure g),
    ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
      E.energyDensityRoot (E.energyMeasure f + E.energyMeasure g) (a • f + b • g) x ≤
        ε * (‖a‖ + ‖b‖)

theorem ae_pairDependence_of_pairMeasure (f g : E.domain)
    (h : ∀ᵐ x ∂(E.energyMeasure f + E.energyMeasure g),
      ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
        E.energyDensityRoot (E.energyMeasure f + E.energyMeasure g) (a • f + b • g) x ≤
          ε * (‖a‖ + ‖b‖))
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (hdom : ∀ f, E.energyMeasure f ≪ μ) :
    ∀ᵐ x ∂μ, ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
      E.energyDensityRoot μ (a • f + b • g) x ≤ ε * (‖a‖ + ‖b‖) := by
  let pair := E.energyMeasure f + E.energyMeasure g
  have : IsFiniteMeasure pair := inferInstanceAs (IsFiniteMeasure (E.energyMeasure f + E.energyMeasure g))
  have : pair.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hpair : pair ≪ μ := (hdom f).add_left (hdom g)
  let t (x : CarpetPoints) := (pair.rnDeriv μ x).toReal ^ p⁻¹
  have ht (x : CarpetPoints) : 0 ≤ t x := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hmul : ∀ᵐ x ∂μ, ∀ a b : ℚ, E.energyDensityRoot μ (a • f + b • g) x =
      E.energyDensityRoot pair (a • f + b • g) x * t x := by
    refine ae_all_iff.mpr fun a ↦ ae_all_iff.mpr fun b ↦ ?_
    have hr := Measure.rnDeriv_mul_rnDeriv (κ := μ)
      (E.energyMeasure_add_rat_smul_absolutelyContinuous f g a b)
    filter_upwards [hr] with x hx
    change (E.energyMeasure (a • f + b • g)).rnDeriv pair x * pair.rnDeriv μ x =
      (E.energyMeasure (a • f + b • g)).rnDeriv μ x at hx
    change ((E.energyMeasure (a • f + b • g)).rnDeriv μ x).toReal ^ p⁻¹ =
      ((E.energyMeasure (a • f + b • g)).rnDeriv pair x).toReal ^ p⁻¹ * t x
    rw [← hx, ENNReal.toReal_mul, Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  have hr := h
  change ∀ᵐ x ∂pair, _ at hr
  rw [← Measure.withDensity_rnDeriv_eq pair μ hpair,
    ae_withDensity_iff (Measure.measurable_rnDeriv _ _)] at hr
  filter_upwards [hmul, hr] with x hm hx
  intro ε hε
  by_cases hz : pair.rnDeriv μ x = 0
  · refine ⟨1, 0, by simp, ?_⟩
    rw [hm 1 0]
    have ht' : t x = 0 := by
      dsimp [t]
      rw [hz, ENNReal.toReal_zero,
        Real.zero_rpow (inv_ne_zero (zero_lt_one.trans E.one_lt_p).ne')]
    rw [ht', mul_zero]
    positivity
  · obtain ⟨a, b, hab, hs⟩ := hx hz (ε / (t x + 1)) (div_pos hε (by linarith [ht x]))
    refine ⟨a, b, hab, ?_⟩
    rw [hm a b]
    calc
      _ ≤ (ε / (t x + 1) * (‖a‖ + ‖b‖)) * t x := mul_le_mul_of_nonneg_right hs (ht x)
      _ = (ε / (t x + 1) * t x) * (‖a‖ + ‖b‖) := by ring
      _ ≤ _ := by
        have he : ε / (t x + 1) * t x ≤ ε := by
          calc
            _ ≤ ε / (t x + 1) * (t x + 1) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
                (div_nonneg hε.le (by linarith [ht x]))
            _ = _ := div_mul_cancel₀ _ (by linarith [ht x])
        exact mul_le_mul_of_nonneg_right he hab.le

/-- Pairwise dependence for pair measures implies pairwise dependence for
any finite common dominating measure. -/
theorem hasPairwiseEnergyDependence_of_pairMeasures
    (h : E.HasPairwiseDependenceOnPairMeasures)
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (hdom : ∀ f, E.energyMeasure f ≪ μ) :
    E.HasPairwiseEnergyDependence μ :=
  fun f g ↦ E.ae_pairDependence_of_pairMeasure f g (h f g) μ hdom

end CarpetEnergy.SelfSimilarPEnergy
