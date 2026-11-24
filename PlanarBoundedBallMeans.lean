import MollifierRadiusBracket
import PlanarMollifierBallAverage
import PlanarMaximalSobolevCutoffs

/-!
# Bounded mollifications control the means on all small planar balls
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 3100000 in
theorem exists_bound_planar_ballMean_of_not_mem_unboundedMollification
    {u : PlanarCoordinates → ℝ} (hu : Integrable u volume)
    (hu₀ : ∀ x, 0 ≤ u x) {x : PlanarCoordinates}
    (hx : x ∉ UnboundedPlanarMollification u) :
    ∃ M > (0 : ℝ), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      (volume.real (ball x r))⁻¹ * ∫ y in ball x r, u y ∂volume ≤ M := by
  have h := hx
  change ¬ (∀ C : ℝ, ∃ n : ℕ, C < mollify volume n u x) at h
  push Not at h
  obtain ⟨C, hC⟩ := h
  obtain ⟨A, hA, hball⟩ := exists_planar_mollifier_ball_integral_bounds
  let P := max C 1
  have hP : 0 < P := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨4 * P / A, div_pos (mul_pos (by norm_num) hP) hA, fun r hr hr' ↦ ?_⟩
  obtain ⟨n, hn₁, hn₂⟩ := exists_mollifier_half_radius_bracket hr hr'
  let t := (mollifierBump (X := PlanarCoordinates) n).rOut
  have ht : 0 < t := (mollifierBump (X := PlanarCoordinates) n).rOut_pos
  have ht₁ : r ≤ t / 2 := hn₁
  have ht₂ : t ≤ 4 * r := hn₂
  have hI : (∫ y in ball x r, u y ∂volume) ≤ ∫ y in ball x (t / 2), u y ∂volume :=
    integral_mono_measure (Measure.restrict_mono (ball_subset_ball ht₁) le_rfl)
      (Eventually.of_forall hu₀) hu.restrict
  have hh : A / t ^ (2 : ℕ) * (∫ y in ball x r, u y ∂volume) ≤ P :=
    (mul_le_mul_of_nonneg_left hI (div_nonneg hA.le (sq_nonneg t))).trans
      ((hball n u hu hu₀ x).1.trans ((hC n).trans (le_max_left _ _)))
  have hcap : (∫ y in ball x r, u y ∂volume) ≤ (P / A) * (4 * r) ^ (2 : ℕ) := by
    have h := (le_div_iff₀ (div_pos hA (sq_pos_of_pos ht))).mpr
      (show (∫ y in ball x r, u y ∂volume) * (A / t ^ (2 : ℕ)) ≤ P by simpa only [mul_comm] using hh)
    refine h.trans ?_
    calc
      _ = P / A * t ^ (2 : ℕ) := by field_simp [hA.ne', ht.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ht.le ht₂ _) (div_nonneg hP.le hA.le)
  rw [measureReal_def, planar_volume_ball x hr.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * r ^ (2 : ℕ))]
  refine (mul_le_mul_of_nonneg_left hcap (by positivity)).trans_eq ?_
  field_simp [hA.ne', hr.ne']

end CarpetEnergy
