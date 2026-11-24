import EnergyCellDependence
import EnergyNormalizedHarmonic

/-!
# Bounds and continuity for pair energy measures

The restricted energy-root seminorm bounds the energy of a rational
combination by the reference pair measure on every Borel set. Restricted
energy masses vary continuously in the graph norm.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The energy of a rational combination is bounded by its coefficient
one-norm to the power p times the reference pair measure. -/
theorem energyMeasure_pair_rat_le (f g : E.domain) (a b : ℚ) :
    E.energyMeasure (a • f + b • g) ≤
      ENNReal.ofReal ((‖a‖ + ‖b‖) ^ p) • (E.energyMeasure f + E.energyMeasure g) := by
  apply Measure.le_iff.mpr
  intro A hA
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let S := E.energyMeasureSeminorm A hA
  let μ := E.energyMeasure f + E.energyMeasure g
  let R := (μ A).toReal ^ p⁻¹
  have hR (v : E.domain) (hv : E.energyMeasure v ≤ μ) : S v ≤ R := by
    rw [E.energyMeasureSeminorm_apply, Measure.real]
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (measure_ne_top _ _) (hv A)) (inv_nonneg.mpr hp.le)
  have hf := hR f (le_add_of_nonneg_right bot_le)
  have hg := hR g (le_add_of_nonneg_left bot_le)
  have hs : S (a • f + b • g) ≤ (‖a‖ + ‖b‖) * R := by
    calc
      _ ≤ S (a • f) + S (b • g) := map_add_le_add _ _ _
      _ = ‖a‖ * S f + ‖b‖ * S g := by
        rw [← Rat.cast_smul_eq_qsmul ℝ a f, ← Rat.cast_smul_eq_qsmul ℝ b g,
          map_smul_eq_mul, map_smul_eq_mul, Rat.norm_cast_real, Rat.norm_cast_real]
      _ ≤ ‖a‖ * R + ‖b‖ * R := add_le_add
        (mul_le_mul_of_nonneg_left hf (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
      _ = _ := (add_mul _ _ _).symm
  have h := Real.rpow_le_rpow (apply_nonneg S _) hs hp.le
  change (E.energyMeasureSeminorm A hA (a • f + b • g)) ^ p ≤ _ at h
  rw [E.energyMeasureSeminorm_apply, Measure.real, Real.rpow_inv_rpow ENNReal.toReal_nonneg hp.ne',
    Real.mul_rpow (add_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.rpow_nonneg ENNReal.toReal_nonneg _)] at h
  rw [Real.rpow_inv_rpow ENNReal.toReal_nonneg hp.ne'] at h
  have he := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_mul
    (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  exact he

theorem ae_rnDeriv_pair_le (f g : E.domain) (a b : ℚ) :
    ∀ᵐ x ∂(E.energyMeasure f + E.energyMeasure g),
      (E.energyMeasure (a • f + b • g)).rnDeriv (E.energyMeasure f + E.energyMeasure g) x ≤
        ENNReal.ofReal ((‖a‖ + ‖b‖) ^ p) := by
  let μ := E.energyMeasure f + E.energyMeasure g
  let ν := E.energyMeasure (a • f + b • g)
  let C := ENNReal.ofReal ((‖a‖ + ‖b‖) ^ p)
  let : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (E.energyMeasure f + E.energyMeasure g))
  let : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (E.energyMeasure (a • f + b • g)))
  let : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
    (fun A hA _ ↦ ?_)
  rw [Measure.setLIntegral_rnDeriv (E.energyMeasure_add_rat_smul_absolutelyContinuous f g a b),
    setLIntegral_const]
  exact E.energyMeasure_pair_rat_le f g a b A

theorem continuous_graphEnergyMeasure (A : Set CarpetPoints) (hA : MeasurableSet A) :
    Continuous (fun z : E.GraphDomain ↦ E.energyMeasure (E.graphToDomain z) A) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let L : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := (E.energyMeasureSeminorm A hA).comp L
  have hS : Continuous S := Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain)
    continuous_norm (fun z ↦
      (E.energyMeasureSeminorm_le_rootSeminorm A hA _).trans (E.rootSeminorm_le_graphSeminorm _))
  have he (z : E.GraphDomain) : E.energyMeasure (E.graphToDomain z) A =
      ENNReal.ofReal (S z ^ p) := by
    change _ = ENNReal.ofReal (E.energyMeasureSeminorm A hA (E.graphToDomain z) ^ p)
    rw [E.energyMeasureSeminorm_apply, Measure.real, Real.rpow_inv_rpow ENNReal.toReal_nonneg hp.ne',
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp only [he]
  exact ENNReal.continuous_ofReal.comp (hS.rpow_const (fun _ ↦ Or.inr hp.le))

end CarpetEnergy.SelfSimilarPEnergy
