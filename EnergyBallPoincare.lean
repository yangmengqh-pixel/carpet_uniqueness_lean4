import EnergyBallScale
import CarpetMeanCentering
import EnergyCellUnionCalculus

/-!
# Poincaré inequality on carpet balls
-/

open Filter Function Metric MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 2700000 in
/-- The ball Poincaré inequality at the walk dimension, with the energy
measure on a fixed enlargement of the ball. -/
theorem exists_ball_poincare :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧ ∀ (x : CarpetPoints) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ f : E.domain,
        (∫ y in ball x r, |(f : CarpetLp p) y -
          (⨍ z in ball x r, (f : CarpetLp p) z ∂carpetMeasure)| ^ p ∂carpetMeasure) ≤
          C * r ^ E.walkDimension * (E.energyMeasure f).real (ball x (A * r)) := by
  have hp := zero_lt_one.trans E.one_lt_p
  have hβ := hp.trans_le E.le_walkDimension
  obtain ⟨C₀, hC₀, hPI⟩ := E.exists_neighborhood_poincare 2
  obtain ⟨a, _, ha, _, hvol⟩ := exists_carpet_ball_volume_bounds
  let A := 3 * ((2 : ℝ) + 1) * diam (univ : Set CarpetPoints) + 1
  let C := (2 : ℝ) ^ p * C₀ * (3 : ℝ) ^ E.walkDimension
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact le_add_of_nonneg_left (by positivity)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨A, C, hA, hC, fun x r hr hr₁ f ↦ ?_⟩
  obtain ⟨n, hn₀, hn₁⟩ := exists_ternary_radius_bracket hr hr₁
  let w := centerWord n x
  let S := cellNeighborhood w 2
  let V := wordCellUnion S
  let c := E.wordMean (List.ofFn w) f
  have hsub : ball x r ⊆ V := ball_subset_centerWord_neighborhood_of_le x hn₁
  have hsub' : V ⊆ ball x (A * r) := by
    simpa only [Nat.cast_ofNat] using centerWord_neighborhood_subset_ball (k := 2) x hr hn₀
  have hV : (E.energyMeasure f).real V ≤ (E.energyMeasure f).real (ball x (A * r)) :=
    measureReal_mono hsub'
  have hB : carpetMeasure (ball x r) ≠ 0 := by
    intro hzero
    have hpos := (mul_pos ha (Real.rpow_pos_of_pos hr _)).trans_le (hvol x r hr hr₁).1
    rw [Measure.real, hzero, ENNReal.toReal_zero] at hpos
    exact (lt_irrefl _) hpos
  have hI : Integrable (fun y ↦ |(f : CarpetLp p) y - c| ^ p) carpetMeasure :=
    integrable_abs_sub_const_rpow hp (f : CarpetLp p) c
  have hpart : (∫ y in ball x r, |(f : CarpetLp p) y - c| ^ p ∂carpetMeasure) ≤
      ∫ y in V, |(f : CarpetLp p) y - c| ^ p ∂carpetMeasure :=
    setIntegral_mono_set hI.restrict (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
      (Eventually.of_forall hsub)
  have hsum : (∑ v ∈ S, (E.energy (E.pullbackWord (List.ofFn v) f) : ℝ)) =
      (E.scalingFactor ^ n)⁻¹ * (E.energyMeasure f).real V := by
    rw [← E.cellUnionEnergy_eq_energyMeasure_real, cellUnionEnergy, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos E.isScalingFactor_scalingFactor.1 _).ne', one_mul]
  have hscale : ((8 : ℝ)⁻¹) ^ n * (E.scalingFactor ^ n)⁻¹ = ((1 / 3 : ℝ) ^ n) ^ E.walkDimension := by
    simp only [E.ternary_radius_rpow_walkDimension, mul_inv, mul_pow, inv_pow]
  have hpoinc := hPI n w f
  change (∫ y in V, |(f : CarpetLp p) y - c| ^ p ∂carpetMeasure) ≤
    C₀ * ((8 : ℝ)⁻¹) ^ n * ∑ v ∈ S, (E.energy (E.pullbackWord (List.ofFn v) f) : ℝ) at hpoinc
  rw [hsum, mul_assoc C₀, ← mul_assoc (((8 : ℝ)⁻¹) ^ n), hscale, ← mul_assoc] at hpoinc
  have hrad := Real.rpow_le_rpow (by positivity) (ternary_radius_lt_three_mul hn₀).le hβ.le
  rw [Real.mul_rpow (by norm_num) hr.le] at hrad
  have hbound := mul_le_mul (mul_le_mul_of_nonneg_left hrad hC₀.le) hV
    (measureReal_nonneg) (by positivity : 0 ≤ C₀ * ((3 : ℝ) ^ E.walkDimension * r ^ E.walkDimension))
  have hh := (integral_abs_sub_setAverage_rpow_le E.one_lt_p.le (f : CarpetLp p) hB c).trans
    (mul_le_mul_of_nonneg_left (hpart.trans (hpoinc.trans hbound)) (Real.rpow_nonneg (by norm_num) _))
  refine hh.trans_eq ?_
  dsimp only [C]
  ring

end CarpetEnergy.SelfSimilarPEnergy
