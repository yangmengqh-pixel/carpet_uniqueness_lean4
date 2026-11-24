import EnergyMeasure

/-!
# Scaling factors and energy comparison

Comparing energies on a domain inclusion orders their scaling factors. The
argument iterates self-similarity and takes a geometric limit.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Iterating the energy scaling equation over all words of length `n`. -/
theorem energy_eq_sum_words (n : ℕ) (f : E.domain) :
    (E.energy f : ℝ) = E.scalingFactor ^ n *
      ∑ w : Fin n → Fin 8, (E.energy (E.pullbackWord (List.ofFn w) f) : ℝ) := by
  have h := congrArg (fun μ : Measure CarpetPoints ↦ μ univ) (E.energyMeasure_eq_sum_words n f)
  rw [E.energyMeasure_univ, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype] at h
  simp only [smul_apply, smul_eq_mul,
    Measure.map_apply (measurableEmbedding_wordMap _).measurable MeasurableSet.univ,
    preimage_univ, E.energyMeasure_univ] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun _ _ ↦
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top)] at hr
  simpa only [ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal E.isScalingFactor_scalingFactor.1.le, ← Finset.mul_sum] using hr

/-- If one energy is bounded by a multiple of another, its scaling factor is
at least the scaling factor of the dominating energy. -/
theorem scalingFactor_ge_of_energy_le (D : SelfSimilarPEnergy p)
    (hdom : E.domain ≤ D.domain) (c : ℝ≥0)
    (henergy : ∀ f : E.domain, E.energy f ≤ c * D.energy (Submodule.inclusion hdom f)) :
    D.scalingFactor ≤ E.scalingFactor := by
  by_contra! hlt
  obtain ⟨f, hf⟩ := E.exists_energy_ne_zero
  let g := Submodule.inclusion hdom f
  have hE : 0 < E.scalingFactor := E.isScalingFactor_scalingFactor.1
  have hD : 0 < D.scalingFactor := D.isScalingFactor_scalingFactor.1
  have hlim : Tendsto (fun n : ℕ ↦
      (E.scalingFactor / D.scalingFactor) ^ n * ((c : ℝ) * (D.energy g : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hE.le hD.le)
        ((div_lt_one hD).mpr hlt)).mul_const ((c : ℝ) * (D.energy g : ℝ))
  have hbound (n : ℕ) : (E.energy f : ℝ) ≤
      (E.scalingFactor / D.scalingFactor) ^ n * ((c : ℝ) * (D.energy g : ℝ)) := by
    rw [E.energy_eq_sum_words n f, D.energy_eq_sum_words n g]
    have hs : (∑ w : Fin n → Fin 8, (E.energy (E.pullbackWord (List.ofFn w) f) : ℝ)) ≤
        ∑ w : Fin n → Fin 8, (c : ℝ) * (D.energy (D.pullbackWord (List.ofFn w) g) : ℝ) := by
      apply Finset.sum_le_sum
      intro w _
      have hw := henergy (E.pullbackWord (List.ofFn w) f)
      rw [E.pullbackWord_inclusion hdom] at hw
      exact_mod_cast hw
    calc
      _ ≤ E.scalingFactor ^ n * (∑ w : Fin n → Fin 8,
          (c : ℝ) * (D.energy (D.pullbackWord (List.ofFn w) g) : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (pow_nonneg hE.le _)
      _ = _ := by
        rw [← Finset.mul_sum, div_pow]
        field_simp
  have hz : (E.energy f : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)
  exact hf (by exact_mod_cast le_antisymm hz (E.energy f).property)

/-- Two-sided energy comparison gives equality of the scaling factors. -/
theorem scalingFactor_eq_of_two_sided_energy_comparison (D : SelfSimilarPEnergy p)
    (hED : E.domain ≤ D.domain) (hDE : D.domain ≤ E.domain)
    (c d : ℝ≥0)
    (henergyED : ∀ f : E.domain, E.energy f ≤ c * D.energy (Submodule.inclusion hED f))
    (henergyDE : ∀ f : D.domain, D.energy f ≤ d * E.energy (Submodule.inclusion hDE f)) :
    E.scalingFactor = D.scalingFactor :=
  le_antisymm (D.scalingFactor_ge_of_energy_le E hDE d henergyDE)
    (E.scalingFactor_ge_of_energy_le D hED c henergyED)

end CarpetEnergy.SelfSimilarPEnergy
