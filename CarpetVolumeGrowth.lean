import CarpetHausdorff
import CarpetNeighborhoodBuffers

/-!
# Polynomial volume bounds for the normalized carpet measure
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

theorem exists_ternary_radius_bracket {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    ∃ n : ℕ, (1 / 3 : ℝ) ^ (n + 1) < r ∧ r ≤ (1 / 3 : ℝ) ^ n := by
  obtain ⟨n, hl, hu⟩ := exists_consecutive_ternary_bounds (ENNReal.ofReal_ne_zero_iff.mpr hr)
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr₁)
  rw [← ofReal_ternary_radius, ENNReal.ofReal_lt_ofReal_iff hr] at hl
  rw [← ofReal_ternary_radius, ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (1 / 3 : ℝ) ^ n)] at hu
  exact ⟨n, hl, hu⟩

theorem real_ternary_radius_rpow_dimension (n : ℕ) :
    ((1 / 3 : ℝ) ^ n) ^ carpetSimilarityDimension = ((8 : ℝ)⁻¹) ^ n := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
    mul_comm (n : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 3),
    one_div, Real.inv_rpow (by norm_num), real_three_rpow_carpetSimilarityDimension]

set_option maxHeartbeats 2300000 in
/-- The normalized Hausdorff measure has matching upper and lower power
bounds, uniformly over centers and radii up to one. -/
theorem exists_carpet_ball_volume_bounds :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x : CarpetPoints, ∀ r, 0 < r → r ≤ 1 →
      a * r ^ carpetSimilarityDimension ≤ carpetMeasure.real (ball x r) ∧
        carpetMeasure.real (ball x r) ≤ b * r ^ carpetSimilarityDimension := by
  let d := carpetSimilarityDimension
  have hd := carpetSimilarityDimension_pos
  obtain ⟨L, hL⟩ := (tendsto_wordMap_radius.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1 / 3)).exists
  let a := ((8 : ℝ)⁻¹) ^ L
  let b := 200 * (2 : ℝ) ^ d
  refine ⟨a, b, by dsimp only [a]; positivity, by dsimp only [b]; positivity, fun x r hr hr₁ ↦ ?_⟩
  obtain ⟨n, hnl, hnu⟩ := exists_ternary_radius_bracket hr hr₁
  have hcell : range (wordMap (List.ofFn (centerWord (n + L) x))) ⊆ ball x r := by
    intro y hy
    apply mem_ball.mpr
    apply (wordMap_dist_le _ _ hy (mem_centerWord (n + L) x)).trans_lt
    rw [pow_add, mul_assoc]
    exact (mul_lt_mul_of_pos_left hL (by positivity)).trans_le (by rw [← pow_succ]; exact hnl.le)
  have hlow : a * r ^ d ≤ carpetMeasure.real (ball x r) := by
    have hmass := measureReal_mono (μ := carpetMeasure) hcell
    rw [Measure.real, carpetMeasure_range_wordMap, List.length_ofFn, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hmass
    have ha : 0 ≤ a := pow_nonneg (by norm_num : 0 ≤ ((8 : ℝ)⁻¹)) _
    calc
      a * r ^ d ≤ a * ((1 / 3 : ℝ) ^ n) ^ carpetSimilarityDimension :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hnu hd.le) ha
      _ = ((8 : ℝ)⁻¹) ^ (n + L) := by
        rw [real_ternary_radius_rpow_dimension n, pow_add]
        exact mul_comm _ _
      _ ≤ _ := hmass
  refine ⟨hlow, ?_⟩
  by_cases hhalf : r ≤ 1 / 2
  · have he : ediam (ball x r) ≤ ENNReal.ofReal (2 * r) := by
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      exact (dist_triangle_right y z x).trans (by linarith [mem_ball.mp hy, mem_ball.mp hz])
    have he₁ : ediam (ball x r) ≤ 1 := he.trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (by linarith : 2 * r ≤ 1))
    have hh := (carpetMeasure_le_ediam_rpow _ he₁).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow he hd.le))
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hd.le] at hh
    have h200 : (200 : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ d) =
        ENNReal.ofReal (200 * (2 * r) ^ d) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 200), ENNReal.ofReal_ofNat]
    have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hh.trans_eq h200)
    rw [ENNReal.toReal_ofReal (by positivity), Real.mul_rpow (by norm_num) hr.le, ← mul_assoc] at hh'
    exact hh'
  · have hh : carpetMeasure.real (ball x r) ≤ carpetMeasure.real univ :=
      measureReal_mono (subset_univ _)
    have hlu : carpetMeasure.real univ = 1 := by simp [Measure.real]
    rw [hlu] at hh
    refine hh.trans ?_
    dsimp only [b]
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hr.le]
    have hpow : 1 ≤ (2 * r) ^ d := Real.one_le_rpow (by linarith [not_le.mp hhalf]) hd.le
    exact (by norm_num : (1 : ℝ) ≤ 200).trans (le_mul_of_one_le_right (by norm_num) hpow)

end CarpetEnergy
