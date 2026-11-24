import EnergyGlobalNormalization
import EnergyMorrey
import EnergyNeighborhoodMeans
import CarpetNeighborhoodMass

/-!
# Uniform Morrey bounds for normalized neighborhood profiles
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem sum_neighborhood_energy_le_of_mass_ratio {n k : ℕ} (w : Fin n → Fin 8)
    (f : E.domain) (a : ℝ≥0) (ha : 0 < a)
    (h : (a : ℝ≥0∞) * E.energyMeasure f (wordCellUnion (cellNeighborhood w k)) ≤
      E.energyMeasure f (range (wordMap (List.ofFn w)))) :
    (∑ v ∈ cellNeighborhood w k, (E.energy (E.pullbackWord (List.ofFn v) f) : ℝ)) ≤
      (a : ℝ)⁻¹ * (E.energy (E.pullbackWord (List.ofFn w) f) : ℝ) := by
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, E.energyMeasure_range_word,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal E.isScalingFactor_scalingFactor.1.le,
    ENNReal.coe_toReal, List.length_ofFn,
    measure_wordCellUnion _ (E.energyMeasure_carpetCellBoundary_eq_zero
      E.energyMeasure_carpetOuterBoundary_eq_zero f n)] at hreal
  rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)] at hreal
  simp only [E.energyMeasure_range_word, List.length_ofFn, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal E.isScalingFactor_scalingFactor.1.le,
    ENNReal.coe_toReal, ← Finset.mul_sum] at hreal
  rw [mul_left_comm (a : ℝ)] at hreal
  have hc : (0 : ℝ) < E.scalingFactor ^ n := pow_pos E.isScalingFactor_scalingFactor.1 _
  have h' := le_of_mul_le_mul_left hreal hc
  have ha' : 0 < (a : ℝ) := ha
  rw [inv_mul_eq_div, le_div_iff₀ ha']
  simpa only [mul_comm] using h'

set_option maxHeartbeats 1100000 in
/-- The positive lower bound on the central share of the neighborhood
energy yields uniform energy-root and supremum bounds for all its
normalized cell pullbacks. -/
theorem exists_morrey_normalized_neighborhood_bounds (hρ : 1 < E.scalingFactor)
    (k : ℕ) (a : ℝ≥0) (ha : 0 < a) :
    ∃ B > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8) (f : E.continuousCore),
      ∀ (_hpos : 0 < E.energyMeasure (E.continuousCoreToDomain f) (range (wordMap (List.ofFn w)))),
      ∀ (_hratio : (a : ℝ≥0∞) * E.energyMeasure (E.continuousCoreToDomain f)
        (wordCellUnion (cellNeighborhood w k)) ≤
        E.energyMeasure (E.continuousCoreToDomain f) (range (wordMap (List.ofFn w)))),
      ∀ (v : Fin n → Fin 8), (_hv : v ∈ cellNeighborhood w k) →
        let g := E.wordPullbackCore (List.ofFn v) (E.globallyNormalizedCore (List.ofFn w) f)
        E.rootSeminorm (E.continuousCoreToDomain g) ≤ B ∧ ‖g.val‖ ≤ B := by
  classical
  have hp := zero_lt_one.trans E.one_lt_p
  have ha' : 0 < (a : ℝ) := ha
  let A := (a : ℝ)⁻¹
  have hA : 0 < A := inv_pos.mpr ha'
  obtain ⟨D, hD, hDnorm⟩ := E.exists_sup_sub_mean_le_rootSeminorm hρ
  obtain ⟨C, hC, hmean⟩ := E.exists_neighborhood_wordMean_gap k
  let B := 1 + A ^ p⁻¹ + D * A ^ p⁻¹ + (C * A) ^ p⁻¹
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, fun n w f hpos hratio v hv ↦ ?_⟩
  let W := List.ofFn w
  let V := List.ofFn v
  let F := E.continuousCoreToDomain f
  let G := E.globallyNormalizedCore W f
  let g := E.wordPullbackCore V G
  let F' := E.continuousCoreToDomain G
  let c := ENNReal.ofReal (|E.unitEnergyScale (E.pullbackWord W F)| ^ p)
  have hpos' := E.pullback_energy_pos_of_mass W hpos
  have hc : E.energy (E.pullbackWord W F') = 1 := by
    change E.energy (E.pullbackWord W (E.continuousCoreToDomain (E.globallyNormalizedCore W f))) = _
    rw [E.globallyNormalizedCore_pullback, E.energy_normalizedWordPullback W F hpos']
  have hratio' : (a : ℝ≥0∞) * E.energyMeasure F' (wordCellUnion (cellNeighborhood w k)) ≤
      E.energyMeasure F' (range (wordMap W)) := by
    change (a : ℝ≥0∞) * E.energyMeasure (E.continuousCoreToDomain (E.globallyNormalizedCore W f)) _ ≤
      E.energyMeasure (E.continuousCoreToDomain (E.globallyNormalizedCore W f)) _
    rw [E.globallyNormalizedCore_energyMeasure, smul_apply, smul_apply]
    simp only [smul_eq_mul]
    exact (by
      change (a : ℝ≥0∞) * (c * E.energyMeasure F _) ≤ c * E.energyMeasure F _
      rw [mul_left_comm (a : ℝ≥0∞) c]
      exact mul_le_mul' le_rfl hratio)
  have hs := E.sum_neighborhood_energy_le_of_mass_ratio w F' a ha hratio'
  rw [hc, NNReal.coe_one, mul_one] at hs
  have hcell : (E.energy (E.pullbackWord V F') : ℝ) ≤ A :=
    (Finset.single_le_sum (f := fun v ↦ (E.energy (E.pullbackWord (List.ofFn v) F') : ℝ))
      (fun _ _ ↦ NNReal.coe_nonneg _) hv).trans hs
  have hroot : E.rootSeminorm (E.continuousCoreToDomain g) ≤ A ^ p⁻¹ := by
    dsimp only [g]
    rw [E.continuousCoreToDomain_wordPullbackCore, E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) hcell (inv_nonneg.mpr hp.le)
  have hmw : E.wordMean W F' = 0 := E.globallyNormalizedCore_wordMean W f
  have hmv : |E.wordMean V F'| ≤ (C * A) ^ p⁻¹ := by
    have h := hmean n F' w v hv
    rw [hmw, zero_sub, abs_neg] at h
    have h' := h.trans (mul_le_mul_of_nonneg_left hs hC.le)
    exact (Real.rpow_rpow_inv (abs_nonneg _) hp.ne') ▸
      Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h' (inv_nonneg.mpr hp.le)
  have hDn (x : CarpetPoints) : |g.val x - E.wordMean V F'| ≤ D * A ^ p⁻¹ := by
    have h := hDnorm g.val g.property x
    change |g.val x - E.wordMean [] (E.continuousCoreToDomain g)| ≤
      D * E.rootSeminorm (E.continuousCoreToDomain g) at h
    have hm : E.wordMean [] (E.continuousCoreToDomain g) = E.wordMean V F' := by
      dsimp only [g]
      rw [E.continuousCoreToDomain_wordPullbackCore]
      rfl
    rw [hm] at h
    exact h.trans (mul_le_mul_of_nonneg_left hroot hD.le)
  have hAsp : 0 ≤ A ^ p⁻¹ := Real.rpow_nonneg hA.le _
  have hCAsp : 0 ≤ (C * A) ^ p⁻¹ := Real.rpow_nonneg (mul_nonneg hC.le hA.le) _
  refine ⟨hroot.trans (by dsimp only [B]; linarith [mul_nonneg hD.le hAsp]), ?_⟩
  apply (ContinuousMap.norm_le _ hB.le).mpr
  intro x
  rw [Real.norm_eq_abs]
  calc
    |g.val x| = |(g.val x - E.wordMean V F') + E.wordMean V F'| := by rw [sub_add_cancel]
    _ ≤ |g.val x - E.wordMean V F'| + |E.wordMean V F'| := abs_add_le _ _
    _ ≤ D * A ^ p⁻¹ + (C * A) ^ p⁻¹ := add_le_add (hDn x) hmv
    _ ≤ B := by dsimp only [B]; linarith

end CarpetEnergy.SelfSimilarPEnergy
