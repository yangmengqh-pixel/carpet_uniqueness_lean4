import EnergyBallMeanComparison

/-!
# Stopping at a ball with a large energy density
-/

open Filter Function Metric MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

private theorem exists_large_increment_of_limit_gap {a : ℕ → ℝ} {b ε θ : ℝ}
    (ha : Tendsto a atTop (𝓝 b)) (hε : 0 < ε) (hgap : ε ≤ |b - a 0|)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) :
    ∃ n, ε * (1 - θ) / 2 * θ ^ n < |a (n + 1) - a n| := by
  by_contra! hn
  let D := ε * (1 - θ) / 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hpartial (n : ℕ) : |a n - a 0| ≤ D * ∑ j ∈ Finset.range n, θ ^ j := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      exact (show |a (n + 1) - a 0| ≤ |a (n + 1) - a n| + |a n - a 0| from
        abs_sub_le _ _ _).trans ((add_le_add (hn n) ih).trans_eq (add_comm _ _))
  have hlt (n : ℕ) : |a n - a 0| ≤ ε / 2 := by
    have hs := (summable_geometric_of_lt_one hθ₀ hθ₁).sum_le_tsum (Finset.range n)
      (fun j _ ↦ pow_nonneg hθ₀ j)
    rw [tsum_geometric_of_lt_one hθ₀ hθ₁] at hs
    refine (hpartial n).trans ((mul_le_mul_of_nonneg_left hs hD).trans_eq ?_)
    dsimp only [D]
    have hne : 1 - θ ≠ 0 := (sub_pos.mpr hθ₁).ne'
    field_simp
  have hh := le_of_tendsto ((ha.sub_const (a 0)).abs) (Eventually.of_forall hlt)
  exact (not_le.mpr (half_lt_self hε)) (hgap.trans hh)

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 3400000 in
/-- If the value of a continuous profile differs substantially from its
ball mean, some smaller ball has energy at least a fixed multiple of its
radius times the scale-adjusted (p)-th power of the difference. -/
theorem exists_ball_energy_stopping (hρ : E.scalingFactor ≤ 1) :
    ∃ A c : ℝ, 1 ≤ A ∧ 0 < c ∧
      ∀ (f : E.continuousCore) (y : CarpetPoints) (R ε : ℝ), 0 < R → R ≤ 1 → 0 < ε →
        ε ≤ |f.val y - E.ballMean (E.continuousCoreToDomain f) y R| →
        ∃ n : ℕ, let r := R * (1 / 2 : ℝ) ^ n
          c * ε ^ p * R ^ (carpetSimilarityDimension - E.walkDimension - 1) * r ≤
            (E.energyMeasure (E.continuousCoreToDomain f)).real (ball y (A * r)) := by
  have hp := zero_lt_one.trans E.one_lt_p
  obtain ⟨A, B, hA, hB, hMean⟩ := E.exists_ballMean_comparison
  let d := carpetSimilarityDimension
  let β := E.walkDimension
  let s := d - β
  let γ := 1 - s
  have hs : 0 ≤ s := sub_nonneg.mpr (E.walkDimension_le_carpetSimilarityDimension_iff.mpr hρ)
  have hγ : 0 < γ := sub_pos.mpr E.carpetSimilarityDimension_sub_walkDimension_lt_one
  let θ := (1 / 2 : ℝ) ^ (γ / p)
  have hθ : 0 < θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ₁ : θ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (div_pos hγ hp)
  let D := B * (2 : ℝ) ^ d
  have hD : 0 < D := mul_pos hB (Real.rpow_pos_of_pos (by norm_num) _)
  let c := (((1 - θ) / 2) ^ p) / D
  have hc : 0 < c := div_pos (Real.rpow_pos_of_pos (half_pos (sub_pos.mpr hθ₁)) _) hD
  refine ⟨A, c, hA, hc, fun f y R ε hR hR₁ hε hgap ↦ ?_⟩
  let g := E.continuousCoreToDomain f
  let r (n : ℕ) := R * (1 / 2 : ℝ) ^ n
  let a (n : ℕ) := E.ballMean g y (r n)
  have hg : ε ≤ |f.val y - a 0| := by simpa only [a, r, pow_zero, mul_one] using hgap
  obtain ⟨n, hn⟩ := exists_large_increment_of_limit_gap
    (E.tendsto_ballMean_continuous_dyadic f y hR hR₁) hε hg hθ.le hθ₁
  have hr (n : ℕ) : 0 < r n := mul_pos hR (pow_pos (by norm_num) _)
  have hr₁ (n : ℕ) : r n ≤ 1 :=
    (mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))).trans hR₁
  have hsucc : r (n + 1) = r n / 2 := by
    dsimp only [r]
    rw [pow_succ, ← mul_assoc]
    ring
  have hnest : ball y (r (n + 1)) ⊆ ball y (r n) :=
    ball_subset_ball (by rw [hsucc]; exact (half_lt_self (hr n)).le)
  let M := (E.energyMeasure g).real (ball y (A * r n))
  have hdiff := hMean g y y (r n) (r (n + 1)) (hr n) (hr₁ n) (hr _) (hr₁ _) hnest
  have hdiff' : |a (n + 1) - a n| ^ p ≤ D * (r n) ^ (-s) * M := by
    refine hdiff.trans_eq ?_
    rw [hsucc, Real.div_rpow (hr n).le (by norm_num), div_div_eq_mul_div]
    have he : (r n) ^ β / (r n) ^ d = (r n) ^ (-s) := by
      rw [← Real.rpow_sub (hr n), show β - d = -s by dsimp only [s]; ring]
    rw [div_eq_mul_inv, mul_right_comm ((r n) ^ β), ← div_eq_mul_inv, he]
    dsimp only [D]
    ring
  let U := ε * (1 - θ) / 2 * θ ^ n
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hpower := (Real.rpow_le_rpow hU hn.le hp.le).trans hdiff'
  have hs' : D * (r n) ^ (-s) * M * (r n) ^ s = D * M := by
    calc
      _ = D * M * ((r n) ^ (-s) * (r n) ^ s) := by ring
      _ = _ := by rw [← Real.rpow_add (hr n), neg_add_cancel, Real.rpow_zero, mul_one]
  have hθpow : (θ ^ n) ^ p = (((1 / 2 : ℝ) ^ n) ^ γ) := by
    dsimp only [θ]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    field_simp
  have hcoeff : U ^ p * (r n) ^ s =
      (D * c) * ε ^ p * R ^ (s - 1) * r n := by
    have hθp : 0 ≤ (1 - θ) / 2 := (half_pos (sub_pos.mpr hθ₁)).le
    have hUeq : U = ε * ((1 - θ) / 2) * θ ^ n := by dsimp only [U]; ring
    rw [hUeq, Real.mul_rpow (mul_nonneg hε.le hθp) (pow_nonneg hθ.le _),
      Real.mul_rpow hε.le hθp, hθpow]
    have hDc : D * c = ((1 - θ) / 2) ^ p := by
      dsimp only [c]
      rw [mul_comm D, div_mul_cancel₀ _ hD.ne']
    rw [hDc]
    let a := (1 / 2 : ℝ) ^ n
    change (ε ^ p * ((1 - θ) / 2) ^ p) * a ^ γ * (R * a) ^ s =
      ((1 - θ) / 2) ^ p * ε ^ p * R ^ (s - 1) * (R * a)
    have ha : 0 < a := pow_pos (by norm_num) _
    have haγ : a ^ γ * a ^ s = a := by
      rw [← Real.rpow_add ha, show γ + s = 1 by dsimp only [γ]; ring, Real.rpow_one]
    have hRadd : R ^ (s - 1) * R = R ^ s := by
      calc
        _ = R ^ (s - 1) * R ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hR, sub_add_cancel]
    rw [Real.mul_rpow hR.le ha.le]
    calc
      _ = ((1 - θ) / 2) ^ p * ε ^ p * R ^ s * (a ^ γ * a ^ s) := by ring
      _ = _ := by rw [haγ, ← hRadd]; ring
  have h := mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg (hr n).le s)
  rw [hs', hcoeff] at h
  refine ⟨n, (mul_le_mul_iff_right₀ hD).mp ?_⟩
  convert h using 1
  ring

end SelfSimilarPEnergy
end CarpetEnergy
