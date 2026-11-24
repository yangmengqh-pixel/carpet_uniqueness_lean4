import EnergyStationaryPlanarSobolev
import EnergyWeightedCutoffComposition
import EnergyBoundaryCovariance

/-!
# The planar pushforward on a selected interior cell

When the cutoff equals one on a cell, the unweighted planar
pushforward of the pulled-back pair is dominated by the weighted
pushforward of the original pair, after the cell's energy scaling.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

theorem restrict_le_powerWeightedMeasure (p : ℝ) (μ : Measure CarpetPoints)
    (χ : C(CarpetPoints, ℝ)) {A : Set CarpetPoints} (hA : MeasurableSet A)
    (hχ : ∀ x ∈ A, χ x = 1) :
    μ.restrict A ≤ powerWeightedMeasure p μ χ := by
  rw [← withDensity_indicator_one hA]
  apply withDensity_mono
  refine Eventually.of_forall fun x ↦ ?_
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx]
    change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (χ x ^ p)
    rw [hχ x hx, Real.one_rpow, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hx]
    exact zero_le

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem pairEnergyMeasure_restrict_word (u : Fin 2 → E.continuousCore) (w : List (Fin 8)) :
    (E.pairEnergyMeasure u).restrict (range (wordMap w)) =
      (ENNReal.ofReal E.scalingFactor ^ w.length) •
        (E.pairEnergyMeasure (fun i ↦ E.wordPullbackCore w (u i))).map (wordMap w) := by
  unfold pairEnergyMeasure
  rw [Measure.restrict_add, E.energyMeasure_restrict_word, E.energyMeasure_restrict_word,
    ← smul_add, Measure.map_add _ _ (continuous_wordMap w).measurable,
    E.continuousCoreToDomain_wordPullbackCore, E.continuousCoreToDomain_wordPullbackCore]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
set_option maxHeartbeats 1500000 in
theorem smul_map_pairEnergyMeasure_wordPullback_le (u : Fin 2 → E.continuousCore)
    (χ : E.continuousCore) (w : List (Fin 8)) (hχ : ∀ x ∈ range (wordMap w), χ.val x = 1) :
    let v := fun i ↦ E.wordPullbackCore w (u i)
    (ENNReal.ofReal E.scalingFactor ^ w.length) •
        (E.pairEnergyMeasure v).map (E.continuousCoreTuple v) ≤
      (powerWeightedMeasure p (E.pairEnergyMeasure u) χ.val).map (E.continuousCoreTuple u) := by
  let v : Fin 2 → E.continuousCore := fun i ↦ E.wordPullbackCore w (u i)
  let H := E.continuousCoreTuple u
  let V := E.continuousCoreTuple v
  have hV : (V : CarpetPoints → (Fin 2 → ℝ)) = H ∘ wordMap w := by
    funext x i
    rfl
  have hdom := Measure.map_mono (restrict_le_powerWeightedMeasure p (E.pairEnergyMeasure u) χ.val
    (measurableEmbedding_wordMap w).measurableSet_range hχ) H.continuous.measurable
  rw [E.pairEnergyMeasure_restrict_word u w, Measure.map_smul _ H.continuous.measurable.aemeasurable,
    Measure.map_map H.continuous.measurable (continuous_wordMap w).measurable, ← hV] at hdom
  exact hdom

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem pairEnergyMeasure_univ_wordPullback_pos (u : Fin 2 → E.continuousCore)
    (w : List (Fin 8)) (h : 0 < E.pairEnergyMeasure u (range (wordMap w))) :
    0 < E.pairEnergyMeasure (fun i ↦ E.wordPullbackCore w (u i)) univ := by
  have he := congrArg (fun μ : Measure CarpetPoints ↦ μ univ) (E.pairEnergyMeasure_restrict_word u w)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_wordMap w).measurable MeasurableSet.univ, preimage_univ] at he
  rw [he] at h
  exact pos_iff_ne_zero.mpr fun hz ↦ by rw [hz, mul_zero] at h; exact (lt_irrefl _) h

end SelfSimilarPEnergy

end CarpetEnergy
