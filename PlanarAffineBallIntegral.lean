import PlanarLowerDensity
import SmoothTranslationLp
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Integration under a contraction of a planar ball
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 2200000 in
/-- Averaging along segments ending at a fixed point of the ball
has Jacobian cost at most the inverse square of the variable coefficient. -/
theorem integral_lineMap_ball_le {F : PlanarCoordinates → ℝ}
    (hF : Continuous F) (hF₀ : ∀ x, 0 ≤ F x)
    {x z : PlanarCoordinates} {r t : ℝ} (hz : z ∈ ball x r) (ht : 0 < t) (ht₁ : t ≤ 1) :
    (∫ y in ball x r, F (AffineMap.lineMap z y t) ∂volume) ≤
      ((t ^ (2 : ℕ))⁻¹ * ∫ y in ball x r, F y ∂volume) := by
  let B := ball x r
  let H := B.indicator F
  let a := (1 - t) • z
  have hmap (y : PlanarCoordinates) : AffineMap.lineMap z y t = t • y + a := by
    rw [AffineMap.lineMap_apply_module, add_comm]
  have hFint : Integrable F (volume.restrict B) :=
    (hF.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hI : Integrable H volume := (integrable_indicator_iff isOpen_ball.measurableSet).2 hFint
  have hItr : Integrable (fun y : PlanarCoordinates ↦ H (t • y + a)) volume :=
    (hI.comp_add_right a).comp_smul ht.ne'
  calc
    _ = ∫ y in B, F (t • y + a) ∂volume := by simp only [hmap, B]
    _ = ∫ y in B, H (t • y + a) ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
      have hy' : t • y + a ∈ B := by
        rw [← hmap]
        exact (convex_ball x r).lineMap_mem hz hy ⟨ht.le, ht₁⟩
      exact (indicator_of_mem hy' F).symm
    _ ≤ ∫ y, H (t • y + a) ∂volume := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun y ↦ Set.indicator_nonneg (fun x _ ↦ hF₀ x) (t • y + a)) hItr
    _ = _ := by
      have hh := Measure.integral_comp_smul_of_nonneg (volume : Measure PlanarCoordinates)
        (fun y ↦ H (y + a)) t (hR := ht.le)
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul] at hh
      change _ = _ * ∫ y in B, F y ∂volume
      rw [hh, integral_add_right_eq_self]
      dsimp only [H]
      rw [integral_indicator isOpen_ball.measurableSet]

end CarpetEnergy
