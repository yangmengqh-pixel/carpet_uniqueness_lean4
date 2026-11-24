import EnergyWalkScale
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Scalar estimates for energy-image area

For a finite partition, powers of the pieces are bounded by their total
using superadditivity or concavity. The scale bound turns the concave
case into a geometric area estimate with ratio at most eight ninths.
-/

open Finset Set
open scoped BigOperators

namespace CarpetEnergy

theorem sum_rpow_le_rpow_sum_of_one_le {ι : Type*} (S : Finset ι) (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) {q : ℝ} (hq : 1 ≤ q) :
    (∑ i ∈ S, u i ^ q) ≤ (∑ i ∈ S, u i) ^ q := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [Real.zero_rpow (zero_lt_one.trans_le hq).ne']
  | @insert a S ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (add_le_add (le_refl _) ih).trans
      (Real.add_rpow_le_rpow_add (hu a) (Finset.sum_nonneg fun i _ ↦ hu i) hq)

theorem sum_rpow_le_card_mul_rpow_sum_of_le_one {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (∑ i ∈ S, u i ^ q) ≤ (S.card : ℝ) ^ (1 - q) * (∑ i ∈ S, u i) ^ q := by
  classical
  let n := (S.card : ℝ)
  have hn : 0 < n := by
    change 0 < (S.card : ℝ)
    exact_mod_cast S.card_pos.mpr hS
  have hN : ∑ _i ∈ S, n⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn.ne'
  have hf := Real.concaveOn_rpow hq₀ hq₁
  have h := hf.le_map_sum (t := S) (w := fun _ ↦ n⁻¹) (p := u)
    (fun _ _ ↦ inv_nonneg.mpr hn.le) hN (fun i _ ↦ hu i)
  simp only [smul_eq_mul, ← mul_sum] at h
  have hsum : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg fun i _ ↦ hu i
  rw [Real.mul_rpow (inv_nonneg.mpr hn.le) hsum, Real.inv_rpow hn.le] at h
  have h' := mul_le_mul_of_nonneg_left h hn.le
  have hnq : n * (n ^ q)⁻¹ = n ^ (1 - q) := by
    rw [Real.rpow_sub hn, Real.rpow_one, div_eq_mul_inv]
  rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, ← mul_assoc, hnq] at h'
  exact h'

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The geometric factor when the covering power is two and `p ≥ 2`.
The lower scale bound gives this estimate regardless of the carpet's
exact renormalization factor. -/
theorem image_area_ratio_le (hp₂ : 2 ≤ p) :
    (E.scalingFactor⁻¹) ^ (2 / p) * (8 : ℝ) ^ (1 - 2 / p) ≤ (8 / 9 : ℝ) := by
  have hp : 0 < p := zero_lt_two.trans_le hp₂
  have hρ := E.isScalingFactor_scalingFactor.1
  have h3 : 0 < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have hle : E.scalingFactor⁻¹ ≤ (8 : ℝ) * ((3 : ℝ) ^ p)⁻¹ := by
    have h := inv_le_inv₀ hρ (div_pos h3 (by norm_num)) |>.mpr E.three_rpow_div_eight_le_scalingFactor
    rw [← div_eq_mul_inv, ← inv_div]
    exact h
  have hq : 0 ≤ (2 / p : ℝ) := div_nonneg (by norm_num) hp.le
  calc
    _ ≤ (((8 : ℝ) * ((3 : ℝ) ^ p)⁻¹) ^ (2 / p)) * (8 : ℝ) ^ (1 - 2 / p) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (inv_nonneg.mpr hρ.le) hle hq)
        (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr h3.le), Real.inv_rpow h3.le,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        show p * (2 / p) = 2 by field_simp,
        mul_right_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 8),
        show 2 / p + (1 - 2 / p) = 1 by ring, Real.rpow_one]
      norm_num

end SelfSimilarPEnergy
end CarpetEnergy
