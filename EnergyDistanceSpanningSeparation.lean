import EnergyBallMeanStopping
import DistanceIntervalBallMass

/-!
# Energy required to separate two distance-spanning sets
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 3400000 in
/-- The distance-spanning version of the local lower bound in
[37, Lemma 5.10]. Each separating set covers a fixed interval of
distances from the center. -/
theorem exists_energy_lower_of_distance_spanning_separation
    (hρ : E.scalingFactor ≤ 1) :
    ∃ A c : ℝ, 1 ≤ A ∧ 0 < c ∧
      ∀ (x : CarpetPoints) (R : ℝ), 0 < R → R ≤ 1 / 2 →
        ∀ (S T : Set CarpetPoints), S ⊆ ball x R → T ⊆ ball x R →
          Icc (R / 2) (3 * R / 4) ⊆ (fun y ↦ dist y x) '' S →
          Icc (R / 2) (3 * R / 4) ⊆ (fun y ↦ dist y x) '' T →
          ∀ f : E.continuousCore, (∀ y ∈ S, 1 ≤ f.val y) → (∀ y ∈ T, f.val y ≤ 0) →
            c * R ^ (carpetSimilarityDimension - E.walkDimension) ≤
              (E.energyMeasure (E.continuousCoreToDomain f)).real (ball x (A * R)) := by
  obtain ⟨A₁, C₁, hA₁, hC₁, hMean⟩ := E.exists_ballMean_comparison
  obtain ⟨A₂, C₂, hA₂, hC₂, hStop⟩ := E.exists_ball_energy_stopping hρ
  let A := max (2 * A₁) (A₂ + 1)
  let β := E.walkDimension
  let s := carpetSimilarityDimension - β
  let a : ℝ := (1 / 4 : ℝ) ^ p
  let c₁ := a / (C₁ * (2 : ℝ) ^ β)
  let c₂ := C₂ * a / (40 * A₂)
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hA : 1 ≤ A := (show 1 ≤ A₂ + 1 by linarith).trans (le_max_right _ _)
  have hc₁ : 0 < c₁ := div_pos ha (mul_pos hC₁ (Real.rpow_pos_of_pos (by norm_num) _))
  have hc₂ : 0 < c₂ := div_pos (mul_pos hC₂ ha) (mul_pos (by norm_num) (zero_lt_one.trans_le hA₂))
  refine ⟨A, min c₁ c₂, hA, lt_min hc₁ hc₂, fun x R hR hR₁ S T hS hT hSp hTp f hfS hfT ↦ ?_⟩
  let g := E.continuousCoreToDomain f
  let μ := E.energyMeasure g
  let U := ball x (A * R)
  let m := E.ballMean g x (2 * R)
  have hsign : ∃ V : Set CarpetPoints, V ⊆ ball x R ∧
      Icc (R / 2) (3 * R / 4) ⊆ (fun y ↦ dist y x) '' V ∧
      ∀ y ∈ V, (1 / 2 : ℝ) ≤ |f.val y - m| := by
    by_cases hm : m ≤ 1 / 2
    · exact ⟨S, hS, hSp, fun y hy ↦ (by linarith [hfS y hy] : (1 / 2 : ℝ) ≤ f.val y - m).trans
        (le_abs_self _)⟩
    · exact ⟨T, hT, hTp, fun y hy ↦ (by linarith [hfT y hy, not_le.mp hm] :
        (1 / 2 : ℝ) ≤ -(f.val y - m)).trans (neg_le_abs _)⟩
  obtain ⟨V, hV, hVp, hdiff⟩ := hsign
  have hpos : 0 < R ^ s := Real.rpow_pos_of_pos hR _
  by_cases hfar : ∃ y ∈ V, (1 / 4 : ℝ) ≤ |E.ballMean g y R - m|
  · obtain ⟨y, hy, hyfar⟩ := hfar
    have hRy : ball y R ⊆ ball x (2 * R) := by
      intro z hz
      exact mem_ball.mpr ((dist_triangle z y x).trans_lt (by
        have hz' := mem_ball.mp hz
        have hy' := mem_ball.mp (hV hy)
        linarith))
    have hh := hMean g x y (2 * R) R (by positivity) (by linarith) hR (by linarith) hRy
    have hU' : ball x (A₁ * (2 * R)) ⊆ U := by
      apply ball_subset_ball
      have ha' := mul_le_mul_of_nonneg_right (le_max_left (2 * A₁) (A₂ + 1)) hR.le
      dsimp only [A]
      linarith
    have hM : μ.real (ball x (A₁ * (2 * R))) ≤ μ.real U := measureReal_mono hU'
    have hpow := (Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hyfar
      (zero_lt_one.trans E.one_lt_p).le).trans hh
    have hcoef : C₁ * ((2 * R) ^ β / R ^ carpetSimilarityDimension) =
        (C₁ * (2 : ℝ) ^ β) / R ^ s := by
      rw [Real.mul_rpow (by norm_num) hR.le, Real.rpow_sub hR]
      have hβ := (Real.rpow_pos_of_pos hR β).ne'
      have hd := (Real.rpow_pos_of_pos hR carpetSimilarityDimension).ne'
      field_simp [hβ, hd]
    rw [hcoef] at hpow
    have hnon : 0 ≤ C₁ * (2 : ℝ) ^ β / R ^ s := by positivity
    have hbd := hpow.trans (mul_le_mul_of_nonneg_left hM hnon)
    have hC : 0 < C₁ * (2 : ℝ) ^ β := by positivity
    have hfin : c₁ * R ^ s ≤ μ.real U := by
      dsimp only [c₁]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hC).mpr
      have hh' := mul_le_mul_of_nonneg_right hbd (Real.rpow_nonneg hR.le s)
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hpos.ne'] at hh'
      rwa [mul_comm (C₁ * (2 : ℝ) ^ β)] at hh'
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hpos.le).trans hfin
  · push Not at hfar
    let D := C₂ * a / A₂ * R ^ (s - 1)
    have hD : 0 < D := mul_pos (div_pos (mul_pos hC₂ ha) (zero_lt_one.trans_le hA₂))
      (Real.rpow_pos_of_pos hR _)
    have hball (y : CarpetPoints) (hy : y ∈ V) : ∃ r ∈ Ioc 0 (A₂ * R),
        ball y r ⊆ U ∧ D * r ≤ μ.real (ball y r) := by
      have hg' : (1 / 4 : ℝ) ≤ |f.val y - E.ballMean g y R| := by
        linarith only [hdiff y hy, hfar y hy, abs_sub_le (f.val y) (E.ballMean g y R) m]
      obtain ⟨n, hn⟩ := hStop f y R (1 / 4) hR (by linarith) (by norm_num) hg'
      let r := R * (1 / 2 : ℝ) ^ n
      have hr : 0 < r := mul_pos hR (pow_pos (by norm_num) _)
      have hrR : r ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))
      refine ⟨A₂ * r, ⟨mul_pos (zero_lt_one.trans_le hA₂) hr,
        mul_le_mul_of_nonneg_left hrR (zero_le_one.trans hA₂)⟩, ?_, ?_⟩
      · intro z hz
        have hz' := mem_ball.mp hz
        have hy' := mem_ball.mp (hV hy)
        have hA' := mul_le_mul_of_nonneg_right (le_max_right (2 * A₁) (A₂ + 1)) hR.le
        have hA'' := mul_le_mul_of_nonneg_left hrR (zero_le_one.trans hA₂)
        exact mem_ball.mpr ((dist_triangle z y x).trans_lt (by linarith))
      · refine (le_of_eq ?_).trans hn
        dsimp only [D]
        field_simp [ne_of_gt (zero_lt_one.trans_le hA₂)]
        ring
    have hh := measureReal_le_from_distance_interval μ x (by linarith : R / 2 ≤ 3 * R / 4) hD hVp hball
    have hRadd : R ^ (s - 1) * R = R ^ s := by
      calc
        _ = R ^ (s - 1) * R ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hR, sub_add_cancel]
    have hEq : D * (3 * R / 4 - R / 2) / 10 = c₂ * R ^ s := by
      dsimp only [D, c₂]
      rw [← hRadd]
      ring
    rw [hEq] at hh
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le).trans hh

end CarpetEnergy.SelfSimilarPEnergy
