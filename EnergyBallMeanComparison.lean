import EnergyBallPoincare

/-!
# Comparing nested ball means at the walk dimension
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

noncomputable def ballMean (f : E.domain) (x : CarpetPoints) (r : ℝ) : ℝ :=
  ⨍ y in ball x r, (f : CarpetLp p) y ∂carpetMeasure

set_option maxHeartbeats 2300000 in
theorem exists_ballMean_comparison :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ (f : E.domain) (x y : CarpetPoints) (R r : ℝ), 0 < R → R ≤ 1 →
        0 < r → r ≤ 1 → ball y r ⊆ ball x R →
        |E.ballMean f y r - E.ballMean f x R| ^ p ≤
          C * (R ^ E.walkDimension / r ^ carpetSimilarityDimension) *
            (E.energyMeasure f).real (ball x (A * R)) := by
  obtain ⟨A, B, hA, hB, hPI⟩ := E.exists_ball_poincare
  obtain ⟨a, _, ha, _, hvol⟩ := exists_carpet_ball_volume_bounds
  refine ⟨A, B / a, hA, div_pos hB ha, fun f x y R r hR hR₁ hr hr₁ hsub ↦ ?_⟩
  let c := E.ballMean f x R
  let μ := carpetMeasure
  let I := (E.energyMeasure f).real (ball x (A * R))
  have hp := zero_lt_one.trans E.one_lt_p
  have hv := (hvol y r hr hr₁).1
  have hpos : 0 < a * r ^ carpetSimilarityDimension := mul_pos ha (Real.rpow_pos_of_pos hr _)
  have hμ : μ (ball y r) ≠ 0 := by
    intro he
    have hh := hpos.trans_le hv
    rw [Measure.real, he, ENNReal.toReal_zero] at hh
    exact lt_irrefl _ hh
  have hm := measureReal_mul_abs_setAverage_sub_rpow_le E.one_lt_p.le (f : CarpetLp p) hμ c
  have hfI : Integrable (fun z ↦ |(f : CarpetLp p) z - c| ^ p) μ :=
    integrable_abs_sub_const_rpow hp (f : CarpetLp p) c
  have hI := setIntegral_mono_set hfI.restrict
    (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) (Eventually.of_forall hsub)
  have h := (mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg
      (abs_nonneg (E.ballMean f y r - c)) p)).trans (hm.trans (hI.trans (hPI x R hR hR₁ f)))
  have hh : |E.ballMean f y r - c| ^ p ≤ (B * R ^ E.walkDimension * I) /
      (a * r ^ carpetSimilarityDimension) :=
    (le_div_iff₀ hpos).mpr ((mul_comm _ _).trans_le h)
  exact hh.trans_eq (by ring)

set_option maxHeartbeats 1800000 in
theorem tendsto_ballMean_continuous_dyadic (f : E.continuousCore) (x : CarpetPoints)
    {R : ℝ} (hR : 0 < R) (hR₁ : R ≤ 1) :
    Tendsto (fun n : ℕ ↦ E.ballMean (E.continuousCoreToDomain f) x (R * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 (f.val x)) := by
  obtain ⟨a, _, ha, _, hvol⟩ := exists_carpet_ball_volume_bounds
  let r (n : ℕ) := R * (1 / 2 : ℝ) ^ n
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)).const_mul R
  refine Metric.tendsto_nhds.mpr (fun ε hε ↦ ?_)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp f.val.continuous.continuousAt
    (ε / 2) (half_pos hε)
  filter_upwards [hr.eventually_lt_const hδ] with n hn
  let B := ball x (r n)
  have hp : 0 < r n := mul_pos hR (pow_pos (by norm_num) _)
  have h₁ : r n ≤ 1 := (mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))).trans hR₁
  have hV : 0 < carpetMeasure.real B :=
    (mul_pos ha (Real.rpow_pos_of_pos hp _)).trans_le (hvol x (r n) hp h₁).1
  have hμ : carpetMeasure B ≠ 0 := pos_iff_ne_zero.mp (ENNReal.toReal_pos_iff.mp hV).1
  have hmean : E.ballMean (E.continuousCoreToDomain f) x (r n) - f.val x =
      ⨍ y in B, f.val y - f.val x ∂carpetMeasure := by
    have hI : Integrable f.val carpetMeasure :=
      f.val.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h := setAverage_sub (s := B) hI.integrableOn (integrable_const (f.val x)).integrableOn
    have hEq : E.ballMean (E.continuousCoreToDomain f) x (r n) =
        ⨍ y in B, f.val y ∂carpetMeasure :=
      average_congr (ae_restrict_of_ae (continuousLp_ae_eq p f.val))
    simpa only [hEq, Pi.sub_apply, setAverage_const hμ (measure_ne_top _ _)] using h.symm
  change dist (E.ballMean (E.continuousCoreToDomain f) x (r n)) (f.val x) < ε
  rw [Real.dist_eq, hmean, setAverage_eq, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hV.le)]
  have hN : |∫ y in B, f.val y - f.val x ∂carpetMeasure| ≤ ε / 2 * carpetMeasure.real B := by
    have h := norm_integral_le_of_norm_le_const (μ := carpetMeasure.restrict B)
      (f := fun y ↦ f.val y - f.val x) (C := ε / 2) (by
        filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        exact (hsmall ((mem_ball.mp hy).trans hn)).le)
    simpa only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ, univ_inter] using h
  refine (mul_le_mul_of_nonneg_left hN (inv_nonneg.mpr hV.le)).trans_lt ?_
  rw [mul_left_comm, inv_mul_cancel₀ hV.ne', mul_one]
  exact half_lt_self hε

end CarpetEnergy.SelfSimilarPEnergy
