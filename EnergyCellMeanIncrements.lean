import EnergyWordMeanJensen
import EnergyNeighborhoodPoincare

/-!
# Differences of means on a parent cell and its children
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

theorem range_wordMap_child_subset {n : ℕ} (w : Fin (n + 1) → Fin 8) :
    range (wordMap (List.ofFn w)) ⊆ range (wordMap (List.ofFn (w ∘ Fin.castSucc))) := by
  rw [List.ofFn_succ', List.concat_eq_append]
  have hc (v : List (Fin 8)) (i : Fin 8) (x : CarpetPoints) :
      wordMap (v ++ [i]) x = wordMap v (cellMap i x) := by
    induction v with
    | nil => rfl
    | cons j v ih => exact congrArg (cellMap j) ih
  rintro _ ⟨x, rfl⟩
  rw [hc]
  exact mem_range_self _

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A single parent-cell Poincaré bound controls the difference to every child mean. -/
theorem exists_wordMean_increment_bound :
    ∃ C > (0 : ℝ), ∀ (f : E.domain) (n : ℕ) (w : Fin (n + 1) → Fin 8),
      |E.wordMean (List.ofFn w) f - E.wordMean (List.ofFn (w ∘ Fin.castSucc)) f| ≤
        (C * (E.energy (E.pullbackWord (List.ofFn (w ∘ Fin.castSucc)) f) : ℝ)) ^ p⁻¹ := by
  obtain ⟨A, hA, hPI⟩ := E.exists_cell_poincare
  refine ⟨8 * A, by positivity, fun f n w ↦ ?_⟩
  let c := E.wordMean (List.ofFn (w ∘ Fin.castSucc)) f
  let t := |E.wordMean (List.ofFn w) f - c|
  let V := range (wordMap (List.ofFn (w ∘ Fin.castSucc)))
  let e := (E.energy (E.pullbackWord (List.ofFn (w ∘ Fin.castSucc)) f) : ℝ)
  have h := E.abs_wordMean_sub_rpow_mul_le (List.ofFn w) f c
  have hi := setIntegral_mono_set (integrable_abs_sub_const_rpow
    (zero_lt_one.trans E.one_lt_p) (f : CarpetLp p) c).restrict
    (Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg _) p)
    (Filter.Eventually.of_forall (range_wordMap_child_subset w))
  have he := hPI (List.ofFn (w ∘ Fin.castSucc)) f
  rw [List.length_ofFn] at h he
  have hpow : ((8 : ℝ)⁻¹) ^ n * ((8 : ℝ)⁻¹ * t ^ p) ≤ A * ((8 : ℝ)⁻¹) ^ n * e := by
    simpa only [pow_succ, mul_assoc] using h.trans (hi.trans he)
  have ht : t ^ p ≤ 8 * A * e := by
    have hh := (mul_le_mul_iff_right₀ (show (0 : ℝ) < ((8 : ℝ)⁻¹) ^ n by positivity)).mp
      (show ((8 : ℝ)⁻¹) ^ n * ((8 : ℝ)⁻¹ * t ^ p) ≤ ((8 : ℝ)⁻¹) ^ n * (A * e) from by
        convert hpow using 1; ring)
    linarith
  have hp := inv_pos.mpr (zero_lt_one.trans E.one_lt_p)
  exact (Real.rpow_rpow_inv (abs_nonneg _) (ne_of_gt (zero_lt_one.trans E.one_lt_p))) ▸
    Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) ht hp.le

end SelfSimilarPEnergy
end CarpetEnergy
