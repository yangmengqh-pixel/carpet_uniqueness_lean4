import EnergyNeighborhoodHarnackEstimate
import EnergyInteriorHarmonicExterior
import EnergyWordMeanJensen
import CarpetNeighborhoodBuffers

/-!
# Uniform initial bound on buffered fine neighborhoods

At a fixed finer scale, the Harnack estimate and the mean
comparison control the profile on a full neighborhood around
every point of the coarser inner region.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 2900000 in
theorem exists_centered_bound_on_buffered_fine_neighborhood {H : ℝ} (hH : 1 ≤ H)
    (hHar : E.HasNeighborhoodHarnack H)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ))) (L : ℕ) :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8) (v : Fin (n + L) → Fin 8),
      Disjoint (wordCellUnion (cellNeighborhood w 3)) carpetOuterBoundary →
      wordCellUnion (cellNeighborhood v 3) ⊆ wordCellUnion (cellNeighborhood w 3) →
      ∀ f : E.domain, E.IsInteriorHarmonic f →
        ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood v 2)),
          |(f : CarpetLp p) x - E.wordMean (List.ofFn w) f| ≤
            C * ((E.scalingFactor ^ n)⁻¹ * E.cellUnionEnergy (cellNeighborhood w 3) f) ^ p⁻¹ := by
  obtain ⟨A, hA, hpi⟩ := E.exists_neighborhood_poincare 3
  obtain ⟨B, hB, hbound⟩ := E.exists_harmonic_neighborhood_centered_bound hH hHar hG
  have hp := zero_lt_one.trans E.one_lt_p
  have hρ := E.isScalingFactor_scalingFactor.1
  let K := (E.scalingFactor ^ L)⁻¹
  let D := (8 : ℝ) ^ L * A
  let C := B * K ^ p⁻¹ + D ^ p⁻¹
  have hK : 0 < K := inv_pos.mpr (pow_pos hρ _)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨C, add_pos (mul_pos hB (Real.rpow_pos_of_pos hK _)) (Real.rpow_pos_of_pos hD _),
    fun n w v hw hv f hf ↦ ?_⟩
  let W := wordCellUnion (cellNeighborhood w 3)
  let V := wordCellUnion (cellNeighborhood v 3)
  let U := range (wordMap (List.ofFn v))
  let m := E.wordMean (List.ofFn w) f
  let mv := E.wordMean (List.ofFn v) f
  let e := E.cellUnionEnergy (cellNeighborhood w 3) f
  let t := (E.scalingFactor ^ n)⁻¹ * e
  have ht : 0 ≤ t := mul_nonneg (inv_nonneg.mpr (pow_nonneg hρ.le _)) (E.cellUnionEnergy_nonneg _ _)
  have hV : Disjoint V carpetOuterBoundary := hw.mono_left hv
  have hU₀ : U ⊆ V := fun _ hx ↦ mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨self_mem_cellNeighborhood v 3, hx⟩⟩
  have hU : U ⊆ W := hU₀.trans hv
  have hsum : t = ∑ z ∈ cellNeighborhood w 3, (E.energy (E.pullbackWord (List.ofFn z) f) : ℝ) := by
    dsimp only [t, e, cellUnionEnergy]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hρ.ne'), one_mul]
  have hmean : |mv - m| ≤ D ^ p⁻¹ * t ^ p⁻¹ := by
    have hInt := integrable_abs_sub_const_rpow hp (f : CarpetLp p) m
    have hI := integral_mono_measure (Measure.restrict_mono hU le_rfl)
      (Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg ((f : CarpetLp p) x - m)) p) hInt.restrict
    have hj := (E.abs_wordMean_sub_rpow_mul_le (List.ofFn v) f m).trans (hI.trans (hpi n w f))
    rw [List.length_ofFn, ← hsum, pow_add] at hj
    have hr : 0 < ((8 : ℝ)⁻¹) ^ n := by positivity
    have hj' : ((8 : ℝ)⁻¹) ^ L * |mv - m| ^ p ≤ A * t := by
      apply le_of_mul_le_mul_left _ hr
      convert hj using 1 <;> ring
    have hmul := mul_le_mul_of_nonneg_left hj' (show 0 ≤ (8 : ℝ) ^ L by positivity)
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num : (8 : ℝ) ≠ 0), one_pow, one_mul] at hmul
    have hm := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) hmul (inv_nonneg.mpr hp.le)
    rw [Real.rpow_rpow_inv (abs_nonneg _) hp.ne', ← mul_assoc,
      Real.mul_rpow hD.le ht] at hm
    exact hm
  have hE : E.cellUnionEnergy (cellNeighborhood v 3) f ≤ e := by
    simp only [e, E.cellUnionEnergy_eq_energyMeasure_real]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hv)
  have he :
      (E.scalingFactor ^ (n + L))⁻¹ * E.cellUnionEnergy (cellNeighborhood v 3) f ≤ K * t := by
    refine (mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr (pow_nonneg hρ.le _))).trans_eq ?_
    dsimp only [K, t]
    rw [pow_add, mul_inv]
    ring
  have hmin := IsInteriorHarmonic.minimizesWithExterior_wordCells E (cellNeighborhood v 3) hV hf
  have hcenter := hbound (n + L) v hV f hmin
  filter_upwards [hcenter] with x hx
  have hpow := Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr (pow_nonneg hρ.le _))
    (E.cellUnionEnergy_nonneg _ _)) he (inv_nonneg.mpr hp.le)
  rw [Real.mul_rpow hK.le ht] at hpow
  calc
    _ ≤ |(f : CarpetLp p) x - mv| + |mv - m| := abs_sub_le _ _ _
    _ ≤ B * (K ^ p⁻¹ * t ^ p⁻¹) + D ^ p⁻¹ * t ^ p⁻¹ :=
      add_le_add (hx.trans (mul_le_mul_of_nonneg_left hpow hB.le)) hmean
    _ = _ := by dsimp only [C]; ring

end CarpetEnergy.SelfSimilarPEnergy
