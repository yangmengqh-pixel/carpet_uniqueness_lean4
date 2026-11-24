import EnergyHarmonicMinimization

/-!
# A norm bound with a positive-measure zero exterior
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem exists_norm_le_root_of_ae_zero_on {A : Set CarpetPoints} (hA : carpetMeasure A ≠ 0) :
    ∃ C > (0 : ℝ), ∀ f : E.domain,
      (∀ᵐ x ∂carpetMeasure.restrict A, (f : CarpetLp p) x = 0) →
      ‖(f : CarpetLp p)‖ ≤ C * E.rootSeminorm f := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨C, hC, hnorm⟩ := E.exists_norm_le_of_setIntegral A hA
  refine ⟨C + 1, add_pos_of_nonneg_of_pos hC one_pos, fun f hf ↦ ?_⟩
  have h := hnorm f
  rw [integral_congr_ae hf, integral_zero, abs_zero, zero_div, zero_add] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (apply_nonneg E.rootSeminorm f))

end CarpetEnergy.SelfSimilarPEnergy
