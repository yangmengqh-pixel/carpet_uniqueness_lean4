import PlanarSobolevTranslation

/-!
# The planar derivative norm is bounded by its coordinate derivatives
-/

open scoped NNReal

namespace CarpetEnergy

theorem planar_opNorm_rpow_le {p : ℝ} (hp : 1 ≤ p) (A : (Fin 2 → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ^ p ≤ (2 : ℝ) ^ (p - 1) *
      (|A (planarDirection 0)| ^ p + |A (planarDirection 1)| ^ p) := by
  have hnorm : ‖A‖ ≤ |A (planarDirection 0)| + |A (planarDirection 1)| := by
    apply A.opNorm_le_bound (add_nonneg (abs_nonneg _) (abs_nonneg _))
    intro z
    have he : A z = z 0 * A (planarDirection 0) + z 1 * A (planarDirection 1) := by
      conv_lhs => rw [planarDirection_decomposition_eq z]
      simp only [map_add, map_smul, smul_eq_mul]
    rw [he, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, add_mul]
    have h (i : Fin 2) : |z i| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
    exact add_le_add
      ((mul_le_mul_of_nonneg_right (h 0) (abs_nonneg _)).trans_eq (mul_comm _ _))
      ((mul_le_mul_of_nonneg_right (h 1) (abs_nonneg _)).trans_eq (mul_comm _ _))
  refine (Real.rpow_le_rpow (norm_nonneg _) hnorm (zero_le_one.trans hp)).trans ?_
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨|A (planarDirection 0)|, abs_nonneg _⟩ : ℝ≥0)
    (⟨|A (planarDirection 1)|, abs_nonneg _⟩ : ℝ≥0) hp

end CarpetEnergy
