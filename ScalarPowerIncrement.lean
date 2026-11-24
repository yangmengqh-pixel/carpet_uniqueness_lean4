import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A uniform bound on increments of a positive power

The derivative on a nonnegative interval is bounded by its value at
the right endpoint. This gives the estimate used in the clipped
harmonic comparison.
-/

open Set

namespace CarpetEnergy

theorem rpow_increment_le {p a b M : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M) : (a + b) ^ p ≤ a ^ p + p * b * (M + b) ^ (p - 1) := by
  have hp₀ : 0 ≤ p := zero_le_one.trans hp.le
  have hb' : a ≤ a + b := le_add_of_nonneg_right hb
  have hd (t : ℝ) (_ : t ∈ Icc a (a + b)) :
      HasDerivWithinAt (fun s : ℝ ↦ s ^ p) (p * t ^ (p - 1)) (Icc a (a + b)) t :=
    (Real.hasDerivAt_rpow_const (Or.inr hp.le)).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Ico a (a + b)) :
      ‖p * t ^ (p - 1)‖ ≤ p * (M + b) ^ (p - 1) := by
    have ht₀ := ha.trans ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp₀ (Real.rpow_nonneg ht₀ _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ht₀ (ht.2.le.trans (add_le_add_left haM b)) (sub_nonneg.mpr hp.le)) hp₀
  have he := norm_image_sub_le_of_norm_deriv_le_segment' hd hbound (a + b)
    (right_mem_Icc.mpr hb')
  rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg
    (sub_nonneg.mpr (Real.rpow_le_rpow ha hb' hp₀))] at he
  have he' : p * (M + b) ^ (p - 1) * b = p * b * (M + b) ^ (p - 1) := by ring
  linarith only [he, he']

end CarpetEnergy
