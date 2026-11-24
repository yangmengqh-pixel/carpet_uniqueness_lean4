import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Midpoint tests for Cauchy sequences

If the norms of a sequence and of any cofinal sequence of its midpoints
have the same limit, uniform convexity rules out separated tails.
-/

open Filter Function Metric Set
open scoped Topology

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [UniformConvexSpace X]

/-- A uniform convexity criterion using cofinal sequences of midpoints. -/
theorem cauchySeq_of_norm_tendsto_of_midpoints (u : ℕ → X) (a : ℝ)
    (hu : Tendsto (fun n ↦ ‖u n‖) atTop (𝓝 a))
    (hm : ∀ i j : ℕ → ℕ, (∀ n, n ≤ i n) → (∀ n, n ≤ j n) →
      Tendsto (fun n ↦ ‖(1 / 2 : ℝ) • (u (i n) + u (j n))‖) atTop (𝓝 a)) :
    CauchySeq u := by
  have h₀ : 0 ≤ a := le_of_tendsto_of_tendsto tendsto_const_nhds hu
    (Eventually.of_forall (fun _ ↦ norm_nonneg _))
  by_contra hn
  rw [Metric.cauchySeq_iff] at hn
  push Not at hn
  obtain ⟨ε, hε, hi⟩ := hn
  choose i hi j hj hd using hi
  have hi' : Tendsto i atTop atTop := tendsto_atTop_mono' atTop
    (Eventually.of_forall hi) tendsto_id
  have hj' : Tendsto j atTop atTop := tendsto_atTop_mono' atTop
    (Eventually.of_forall hj) tendsto_id
  let r (n : ℕ) := max ‖u (i n)‖ ‖u (j n)‖
  have hr : Tendsto r atTop (𝓝 a) := by
    simpa only [max_self, Function.comp_apply, r] using (hu.comp hi').max (hu.comp hj')
  have hdist (n : ℕ) : ε ≤ ‖u (i n) - u (j n)‖ := by simpa only [dist_eq_norm] using hd n
  have ha : 0 < a := by
    apply lt_of_le_of_ne h₀
    intro hz
    have hlim : Tendsto (fun n ↦ ‖u (i n)‖ + ‖u (j n)‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [← hz, add_zero, Function.comp_apply] using (hu.comp hi').add (hu.comp hj')
    exact hε.not_ge (le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall fun n ↦ (hdist n).trans (norm_sub_le _ _)))
  obtain ⟨δ, hδ, hUC⟩ := exists_forall_closed_ball_dist_add_le_two_sub X
    (div_pos hε (by linarith : 0 < a + 1))
  have hupper : ∀ᶠ n in atTop, ‖(1 / 2 : ℝ) • (u (i n) + u (j n))‖ ≤ r n * (1 - δ / 2) := by
    filter_upwards [hr.eventually_const_lt ha, hr.eventually_lt_const (lt_add_of_pos_right a one_pos)]
      with n hr₀ hr₁
    have hleft : ‖(r n)⁻¹ • u (i n)‖ ≤ 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.mpr hr₀.le), inv_mul_le_iff₀ hr₀, mul_one]
      exact le_max_left _ _
    have hright : ‖(r n)⁻¹ • u (j n)‖ ≤ 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.mpr hr₀.le), inv_mul_le_iff₀ hr₀, mul_one]
      exact le_max_right _ _
    have hsep : ε / (a + 1) ≤ ‖(r n)⁻¹ • u (i n) - (r n)⁻¹ • u (j n)‖ := by
      rw [← smul_sub, norm_smul_of_nonneg (inv_nonneg.mpr hr₀.le), ← div_eq_inv_mul]
      exact (div_le_div_of_nonneg_left hε.le hr₀ hr₁.le).trans
        (div_le_div_of_nonneg_right (hdist n) hr₀.le)
    have hl := hUC hleft hright hsep
    rw [← smul_add, norm_smul_of_nonneg (inv_nonneg.mpr hr₀.le), ← div_eq_inv_mul] at hl
    have hbound := (div_le_iff₀ hr₀).mp hl
    rw [norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith only [hbound]
  have hlim := le_of_tendsto_of_tendsto (hm i j hi hj) (hr.mul_const (1 - δ / 2)) hupper
  have hp : 0 < a * δ := mul_pos ha hδ
  nlinarith

end CarpetEnergy
