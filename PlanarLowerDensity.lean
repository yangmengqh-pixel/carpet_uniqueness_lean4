import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A quadratic lower density at almost every point of a finite planar measure
-/

open Filter Metric MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

abbrev PlanarCoordinates := Fin 2 → ℝ

theorem planar_volume_closedBall (z : PlanarCoordinates) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall z r) = ENNReal.ofReal (4 * r ^ (2 : ℕ)) := by
  rw [Real.volume_pi_closedBall z hr, Fintype.card_fin]
  congr 1
  ring

theorem planar_volume_ball (z : PlanarCoordinates) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball z r) = ENNReal.ofReal (4 * r ^ (2 : ℕ)) := by
  rcases hr.eq_or_lt with hzero | hpos
  · subst r
    simp
  · rw [Real.volume_pi_ball z hpos, Fintype.card_fin]
    congr 1
    ring

/-- The lower quadratic growth in Lemma 5.9 holds almost everywhere,
by differentiating planar Lebesgue measure relative to the given measure. -/
theorem ae_planar_ball_lower_density (μ : Measure PlanarCoordinates) [IsFiniteMeasure μ] :
    ∀ᵐ z ∂μ, ∃ a R : ℝ, 0 < a ∧ 0 < R ∧
      ∀ r ∈ Ioo 0 R, a * r ^ (2 : ℕ) ≤ μ.real (ball z r) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (volume : Measure PlanarCoordinates) μ,
    Measure.rnDeriv_lt_top (volume : Measure PlanarCoordinates) μ] with z hz hf
  let T := ((volume : Measure PlanarCoordinates).rnDeriv μ z).toReal + 1
  have hT : 0 < T := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos
  have hlt : (volume : Measure PlanarCoordinates).rnDeriv μ z < ENNReal.ofReal T := by
    rw [← ENNReal.ofReal_toReal hf.ne]
    apply ENNReal.ofReal_lt_ofReal_iff hT |>.mpr
    exact lt_add_one _
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), volume (closedBall z r) / μ (closedBall z r) <
      ENNReal.ofReal T := hz.eventually_lt_const hlt
  obtain ⟨R, hR, hR'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨T⁻¹, R, inv_pos.mpr hT, hR, fun r hr ↦ ?_⟩
  have hhalf : r / 2 ∈ Ioo 0 R := ⟨half_pos hr.1, (half_lt_self hr.1).trans hr.2⟩
  have hord : volume (closedBall z (r / 2)) / μ (closedBall z (r / 2)) <
      ENNReal.ofReal T := hR' hhalf
  have hvol := planar_volume_closedBall z hhalf.1.le
  have hvol' : volume (closedBall z (r / 2)) = ENNReal.ofReal (r ^ (2 : ℕ)) := by
    rw [hvol]
    congr 1
    ring
  have hvolpos : 0 < volume (closedBall z (r / 2)) := by
    rw [hvol']
    exact ENNReal.ofReal_pos.mpr (pow_pos hr.1 _)
  have hm : μ (closedBall z (r / 2)) ≠ 0 := by
    intro hzero
    rw [hzero, ENNReal.div_zero hvolpos.ne'] at hord
    exact not_top_lt hord
  have hc := ENNReal.toReal_mono ENNReal.ofReal_ne_top hord.le
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hT.le, hvol',
    ENNReal.toReal_ofReal (pow_nonneg hr.1.le _)] at hc
  have hμ := ENNReal.toReal_pos hm (measure_ne_top _ _)
  have hsub := closedBall_subset_ball (half_lt_self hr.1) (x := z)
  have hmon := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (μ := μ) hsub)
  calc
    T⁻¹ * r ^ (2 : ℕ) ≤ μ.real (closedBall z (r / 2)) := by
      rw [mul_comm, ← div_eq_mul_inv]
      apply (div_le_iff₀ hT).mpr
      exact ((div_le_iff₀ hμ).mp hc).trans_eq (mul_comm _ _)
    _ ≤ μ.real (ball z r) := hmon

end CarpetEnergy
