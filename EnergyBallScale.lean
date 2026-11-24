import EnergyWalkScale
import CarpetVolumeGrowth

/-!
# Comparing ball radii with the word-cell scale
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

theorem ternary_radius_lt_three_mul {r : ℝ} {n : ℕ}
    (h : (1 / 3 : ℝ) ^ (n + 1) < r) : (1 / 3 : ℝ) ^ n < 3 * r := by
  rw [pow_succ] at h
  linarith

theorem ball_subset_centerWord_neighborhood_of_le {n : ℕ} {r : ℝ}
    (x : CarpetPoints) (h : r ≤ (1 / 3 : ℝ) ^ n) :
    ball x r ⊆ wordCellUnion (cellNeighborhood (centerWord n x) 2) :=
  (ball_subset_ball h).trans (ball_subset_centerWord_neighborhood n x)

theorem centerWord_neighborhood_subset_ball {n k : ℕ} {r : ℝ}
    (x : CarpetPoints) (hr : 0 < r) (h : (1 / 3 : ℝ) ^ (n + 1) < r) :
    wordCellUnion (cellNeighborhood (centerWord n x) k) ⊆
      ball x ((3 * ((k : ℝ) + 1) * diam (univ : Set CarpetPoints) + 1) * r) := by
  intro y hy
  have hdist := dist_centerWord_neighborhood n k x hy
  apply mem_ball.mpr
  have hmul := mul_le_mul_of_nonneg_left (ternary_radius_lt_three_mul h).le
    (show 0 ≤ ((k : ℝ) + 1) * diam (univ : Set CarpetPoints) by positivity)
  exact hdist.trans_lt (by linarith [show
    ((k : ℝ) + 1) * (((1 / 3 : ℝ) ^ n) * diam (univ : Set CarpetPoints)) =
      (((k : ℝ) + 1) * diam (univ : Set CarpetPoints)) * (1 / 3 : ℝ) ^ n by ring,
    show ((k : ℝ) + 1) * diam (univ : Set CarpetPoints) * (3 * r) + r =
      (3 * ((k : ℝ) + 1) * diam (univ : Set CarpetPoints) + 1) * r by ring])

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem three_rpow_walkDimension : (3 : ℝ) ^ E.walkDimension = 8 * E.scalingFactor := by
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (3 : ℝ))]
  unfold walkDimension
  rw [mul_comm (Real.log 3), div_mul_cancel₀ _ (Real.log_pos (by norm_num : 1 < (3 : ℝ))).ne',
    Real.exp_log (mul_pos (by norm_num) E.isScalingFactor_scalingFactor.1)]

theorem walkDimension_le_carpetSimilarityDimension_iff :
    E.walkDimension ≤ carpetSimilarityDimension ↔ E.scalingFactor ≤ 1 := by
  rw [← Real.rpow_le_rpow_left_iff (by norm_num : 1 < (3 : ℝ)),
    E.three_rpow_walkDimension, real_three_rpow_carpetSimilarityDimension]
  constructor <;> intro h <;> linarith

theorem carpetSimilarityDimension_sub_walkDimension_lt_one :
    carpetSimilarityDimension - E.walkDimension < 1 := by
  have hd : carpetSimilarityDimension < 2 := by
    apply (Real.rpow_lt_rpow_left_iff (by norm_num : 1 < (3 : ℝ))).mp
    rw [real_three_rpow_carpetSimilarityDimension, Real.rpow_two]
    norm_num
  linarith [E.le_walkDimension, E.one_lt_p]

/-- The low-scale case has both exponent relations required for the
fast and relatively slow volume conditions in the Harnack reference. -/
theorem radius_ratio_power_bounds_of_scalingFactor_le_one (hρ : E.scalingFactor ≤ 1)
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    (R / r) ^ E.walkDimension ≤ (R / r) ^ carpetSimilarityDimension ∧
      (r / R) ^ (carpetSimilarityDimension - E.walkDimension) *
        (R / r) ^ carpetSimilarityDimension = (R / r) ^ E.walkDimension := by
  have hR₀ := hr.trans_le hR
  have hdiv := div_pos hR₀ hr
  refine ⟨Real.rpow_le_rpow_of_exponent_le ((one_le_div hr).mpr hR)
    (E.walkDimension_le_carpetSimilarityDimension_iff.mpr hρ), ?_⟩
  rw [show r / R = (R / r)⁻¹ from (inv_div _ _).symm, ← Real.rpow_neg_eq_inv_rpow,
    ← Real.rpow_add hdiv]
  congr 1
  ring

private theorem ternary_radius_rpow (n : ℕ) (s : ℝ) :
    ((1 / 3 : ℝ) ^ n) ^ s = (((3 : ℝ) ^ s)⁻¹) ^ n := by
  rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (1 / 3 : ℝ)),
    mul_comm (n : ℝ), Real.rpow_mul_natCast (by norm_num : 0 ≤ (1 / 3 : ℝ)),
    one_div, Real.inv_rpow (by norm_num)]

theorem ternary_radius_rpow_walkDimension (n : ℕ) :
    ((1 / 3 : ℝ) ^ n) ^ E.walkDimension = (8 * E.scalingFactor)⁻¹ ^ n := by
  rw [ternary_radius_rpow, E.three_rpow_walkDimension]

theorem ternary_radius_rpow_dimension_sub_walkDimension (n : ℕ) :
    ((1 / 3 : ℝ) ^ n) ^ (carpetSimilarityDimension - E.walkDimension) = E.scalingFactor ^ n := by
  rw [ternary_radius_rpow, Real.rpow_sub (by norm_num), E.three_rpow_walkDimension,
    real_three_rpow_carpetSimilarityDimension, inv_div, mul_div_cancel_left₀ _ (by norm_num)]

theorem scalingFactor_pow_le_rpow_of_radius_bracket {n : ℕ} {r : ℝ}
    (hr : 0 < r) (hl : (1 / 3 : ℝ) ^ (n + 1) < r) (hu : r ≤ (1 / 3 : ℝ) ^ n) :
    E.scalingFactor ^ n ≤
      (3 : ℝ) ^ |carpetSimilarityDimension - E.walkDimension| *
        r ^ (carpetSimilarityDimension - E.walkDimension) := by
  let s := carpetSimilarityDimension - E.walkDimension
  let b := (1 / 3 : ℝ) ^ n / r
  have hb₁ : 1 ≤ b := (one_le_div hr).mpr hu
  have hb₃ : b ≤ 3 := (div_le_iff₀ hr).mpr (ternary_radius_lt_three_mul hl).le
  have hbn : 0 ≤ b := zero_le_one.trans hb₁
  rw [← E.ternary_radius_rpow_dimension_sub_walkDimension]
  have hh : (1 / 3 : ℝ) ^ n = b * r := (div_mul_cancel₀ _ hr.ne').symm
  rw [hh, Real.mul_rpow hbn hr.le]
  exact mul_le_mul_of_nonneg_right
    ((Real.rpow_le_rpow_of_exponent_le hb₁ (le_abs_self s)).trans
      (Real.rpow_le_rpow hbn hb₃ (abs_nonneg s))) (Real.rpow_nonneg hr.le _)

end SelfSimilarPEnergy
end CarpetEnergy
