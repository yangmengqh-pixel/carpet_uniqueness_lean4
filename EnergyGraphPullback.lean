import CarpetWordIntegral
import EnergyBoundaryCovariance

/-!
# Continuous pullbacks on the graph domain

Cell integration controls the ambient norm, and the word mass formula
controls the energy. Pullbacks are therefore continuous linear maps
for the graph norm.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The ambient p-moment of a word pullback is bounded by the inverse cell mass. -/
theorem norm_pullbackWord_rpow_le (w : List (Fin 8)) (f : E.domain) :
    ‖(E.pullbackWord w f : CarpetLp p)‖ ^ p ≤ (8 : ℝ) ^ w.length * ‖(f : CarpetLp p)‖ ^ p := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let φ (t : ℝ) := |t| ^ p
  have hφ : Continuous φ := continuous_abs.rpow_const (fun _ ↦ Or.inr hp.le)
  have he := setIntegral_wordMap_of_isLpPullback w (E.pullbackWord_isLpPullback w f) hφ
  have hint : Integrable (fun x ↦ φ ((f : CarpetLp p) x)) carpetMeasure := by
    simpa only [φ, Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using
      (Lp.memLp (f : CarpetLp p)).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp)
        ENNReal.ofReal_ne_top
  have h := setIntegral_le_integral (s := range (wordMap w)) hint
    (Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg _) _)
  rw [he] at h
  have hh : ((8 : ℝ)⁻¹) ^ w.length * ‖(E.pullbackWord w f : CarpetLp p)‖ ^ p ≤ ‖(f : CarpetLp p)‖ ^ p := by
    simpa only [φ, integral_abs_rpow_eq_norm_rpow hp] using h
  rw [inv_pow, inv_mul_le_iff₀ (by positivity : 0 < (8 : ℝ) ^ w.length)] at hh
  exact hh

theorem pullbackWord_energy_le (w : List (Fin 8)) (f : E.domain) :
    (E.energy (E.pullbackWord w f) : ℝ) ≤ (E.scalingFactor ^ w.length)⁻¹ * (E.energy f : ℝ) := by
  have hρ := E.isScalingFactor_scalingFactor.1
  have h := measure_mono (μ := E.energyMeasure f) (subset_univ (range (wordMap w)))
  rw [E.energyMeasure_range_word, E.energyMeasure_univ] at h
  have h' := ENNReal.toReal_mono ENNReal.coe_ne_top h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le,
    ENNReal.coe_toReal, ENNReal.coe_toReal] at h'
  exact (le_inv_mul_iff₀ (pow_pos hρ _)).mpr h'

/-- Pullback by a word is a continuous linear map on the graph space. -/
noncomputable def graphPullbackWord (w : List (Fin 8)) : E.GraphDomain →L[ℝ] E.GraphDomain := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let L : E.GraphDomain →ₗ[ℝ] E.GraphDomain :=
    { toFun := fun f ↦ E.toGraph (E.pullbackWord w (E.graphToDomain f))
      map_add' := fun f g ↦ E.pullbackWord_add w (E.graphToDomain f) (E.graphToDomain g)
      map_smul' := fun a f ↦ E.pullbackWord_smul w a (E.graphToDomain f) }
  let c := max ((8 : ℝ) ^ w.length) (E.scalingFactor ^ w.length)⁻¹
  have hc : 0 ≤ c := (pow_nonneg (by norm_num) _).trans (le_max_left _ _)
  refine L.mkContinuous (c ^ p⁻¹) fun z ↦ ?_
  let f := E.graphToDomain z
  let g := E.pullbackWord w f
  change E.graphSeminorm g ≤ c ^ p⁻¹ * E.graphSeminorm f
  rw [E.graphSeminorm_apply, E.graphSeminorm_apply, energyGraphNorm, energyGraphNorm]
  have he : (E.energy g : ℝ) ≤ c * (E.energy f : ℝ) :=
    (E.pullbackWord_energy_le w f).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (NNReal.coe_nonneg _))
  have hL : ‖(g : CarpetLp p)‖ ^ p ≤ c * ‖(f : CarpetLp p)‖ ^ p :=
    (E.norm_pullbackWord_rpow_le w f).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  rw [← Real.mul_rpow hc (add_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)), mul_add]
  exact Real.rpow_le_rpow (add_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
    (add_le_add he hL) (inv_nonneg.mpr hp.le)

theorem graphPullbackWord_apply (w : List (Fin 8)) (f : E.GraphDomain) :
    E.graphPullbackWord w f = E.toGraph (E.pullbackWord w (E.graphToDomain f)) := rfl

end CarpetEnergy.SelfSimilarPEnergy
