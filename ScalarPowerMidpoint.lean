import SeminormPowerMidpoints
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# A scalar midpoint deficit for p-powers
-/

namespace CarpetEnergy

/-- The real p-power has a midpoint deficit that controls a difference
uniformly on all scales. The nonnegative linear form survives sums
and integration. -/
theorem exists_abs_rpow_midpoint_deficit {p : ℝ} (hp : 1 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ x y : ℝ,
      |x - y| ^ p + C * |(x + y) / 2| ^ p ≤
        (ε + C / 2) * (|x| ^ p + |y| ^ p) := by
  let S := normSeminorm ℝ ℝ
  have hUC : ∀ d > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x y : ℝ, S x ≤ 1 → S y ≤ 1 →
      d ≤ S (x - y) → S ((1 / 2 : ℝ) • (x + y)) ≤ 1 - δ := by
    intro d hd
    obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub ℝ hd
    refine ⟨δ / 2, half_pos hδ, fun x y hx hy hxy ↦ ?_⟩
    have hsep : d ≤ dist x y := by
      rw [dist_eq_norm]
      exact hxy
    have hh : ‖x + y‖ ≤ 2 - δ := h hx hy hsep
    change ‖(1 / 2 : ℝ) • (x + y)‖ ≤ _
    rw [norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith only [hh]
  obtain ⟨C, hC, h⟩ := power_deficit_controls_difference S hp hUC ε hε
  refine ⟨C, hC, fun x y ↦ ?_⟩
  have hh := h x y
  change ‖x - y‖ ^ p ≤ ε * (‖x‖ ^ p + ‖y‖ ^ p) +
    C * ((‖x‖ ^ p + ‖y‖ ^ p) / 2 - ‖(1 / 2 : ℝ) • (x + y)‖ ^ p) at hh
  simp only [Real.norm_eq_abs, smul_eq_mul, one_div, inv_mul_eq_div] at hh
  nlinarith only [hh]

end CarpetEnergy
