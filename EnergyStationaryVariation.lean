import EnergyVariationCells

/-!
# Local first variations of a stationary pair
-/

open MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A fixed directional energy density gives the same fixed density
for derivatives along that direction, on every cell. -/
theorem variation_word_of_stationary_density (h : E.HasLinearFirstVariations)
    (f g : E.domain) (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (hμ : ∀ t : ℝ, E.energyMeasure (f + t • g) =
      ((E.energy (f + t • g) : NNReal) : ℝ≥0∞) • μ)
    (w : List (Fin 8)) :
    E.scalingFactor ^ w.length * E.variation h (E.pullbackWord w f) (E.pullbackWord w g) =
      (μ.real (range (wordMap w))) * E.variation h f g := by
  let c := E.scalingFactor ^ w.length
  let A := range (wordMap w)
  let a := μ.real A
  have he (t : ℝ) : c * (E.energy (E.pullbackWord w f + t • E.pullbackWord w g) : ℝ) =
      a * (E.energy (f + t • g) : ℝ) := by
    have hm := congrArg (fun ν : Measure CarpetPoints ↦ (ν A).toReal) (hμ t)
    change ((E.energyMeasure (f + t • g)) (range (wordMap w))).toReal = _ at hm
    rw [E.energyMeasure_range_word, E.pullbackWord_add, E.pullbackWord_smul,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal E.isScalingFactor_scalingFactor.1.le,
      ENNReal.coe_toReal, smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at hm
    rw [mul_comm a (E.energy (f + t • g) : ℝ)]
    exact hm
  have hleft := (E.hasDerivAt_energy_variation h (E.pullbackWord w f) (E.pullbackWord w g)).const_mul c
  have hright := (E.hasDerivAt_energy_variation h f g).const_mul a
  have hfun :
      (fun t : ℝ ↦ c * (E.energy (E.pullbackWord w f + t • E.pullbackWord w g) : ℝ)) =
      (fun t : ℝ ↦ a * (E.energy (f + t • g) : ℝ)) := funext he
  rw [hfun] at hleft
  have h' := hleft.unique hright
  rw [mul_left_comm c p, mul_left_comm a p] at h'
  exact mul_left_cancel₀ (zero_lt_one.trans E.one_lt_p).ne' h'

end CarpetEnergy.SelfSimilarPEnergy
