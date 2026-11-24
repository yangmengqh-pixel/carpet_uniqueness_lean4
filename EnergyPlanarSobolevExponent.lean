import EnergyWalkScale

/-!
# Choice of a Sobolev exponent for the planar argument
-/

open Filter
open scoped Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem lt_two_of_scalingFactor_le_one (hρ : E.scalingFactor ≤ 1) : p < 2 := by
  apply (Real.rpow_lt_rpow_left_iff (by norm_num : 1 < (3 : ℝ))).mp
  have h := E.three_rpow_div_eight_le_scalingFactor.trans hρ
  rw [div_le_one (by norm_num : 0 < (8 : ℝ))] at h
  exact h.trans_lt (by rw [Real.rpow_two]; norm_num)

set_option maxHeartbeats 1100000 in
/-- The strict Sobolev range contains an exponent with (2p/q<2-p)
whenever the renormalization factor is at most one. -/
theorem exists_planar_sobolev_exponent (hρ : E.scalingFactor ≤ 1) :
    ∃ q > p, 2 * p * q⁻¹ < 2 - p ∧
      ((8 : ℝ)⁻¹) ^ q⁻¹ * E.scalingFactor⁻¹ ^ p⁻¹ < 1 := by
  have hp := zero_lt_one.trans E.one_lt_p
  have hp₂ := E.lt_two_of_scalingFactor_le_one hρ
  have hρ₀ := E.isScalingFactor_scalingFactor.1
  let t₀ : ℝ := (2 - p) / (2 * p)
  let R (t : ℝ) := ((8 : ℝ)⁻¹) ^ t * E.scalingFactor⁻¹ ^ p⁻¹
  have ht₀ : 0 < t₀ := div_pos (sub_pos.mpr hp₂) (mul_pos (by norm_num) hp)
  have ht₀' : p⁻¹ - t₀ = 1 / 2 := by dsimp [t₀]; field_simp; ring
  have hρ' : E.scalingFactor⁻¹ ^ p⁻¹ ≤ (8 : ℝ) ^ p⁻¹ / 3 := by
    have hlo : 0 < (3 : ℝ) ^ p / 8 := by positivity
    have hinv := (inv_le_inv₀ hρ₀ hlo).mpr E.three_rpow_div_eight_le_scalingFactor
    have hm := Real.rpow_le_rpow (inv_nonneg.mpr hρ₀.le) hinv (inv_nonneg.mpr hp.le)
    rwa [inv_div, Real.div_rpow (by norm_num) (by positivity),
      Real.rpow_rpow_inv (by norm_num : 0 ≤ (3 : ℝ)) hp.ne'] at hm
  have hR : R t₀ < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hρ'
      (Real.rpow_nonneg (by norm_num : 0 ≤ ((8 : ℝ)⁻¹)) t₀)
    apply hmul.trans_lt
    rw [← mul_div_assoc, Real.inv_rpow (by norm_num), mul_comm,
      ← div_eq_mul_inv, ← Real.rpow_sub (by norm_num), ht₀',
      div_lt_one (by norm_num : 0 < (3 : ℝ))]
    have h := Real.rpow_lt_rpow (by norm_num : 0 ≤ (8 : ℝ))
      (show (8 : ℝ) < 3 ^ (2 : ℕ) by norm_num) (by norm_num : 0 < (1 : ℝ) / 2)
    rwa [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (3 : ℝ)),
      show (↑(2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at h
  have hcont : Continuous R := (Real.continuous_const_rpow (by norm_num)).mul continuous_const
  have hE : ∀ᶠ t in 𝓝 t₀, 0 < t ∧ R t < 1 := (lt_mem_nhds ht₀).and
    ((hcont.tendsto t₀).eventually_lt_const hR)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hE
  let t := t₀ - ε / 2
  have hdist : dist t t₀ < ε := by
    rw [Real.dist_eq, show t - t₀ = -(ε / 2) by dsimp [t]; ring, abs_neg,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have ht : 0 < t := (hball hdist).1
  have hlt : t < t₀ := sub_lt_self _ (half_pos hε)
  have htp : t < p⁻¹ := hlt.trans (by linarith)
  have hqp : p < t⁻¹ := by
    have hh := (inv_lt_inv₀ (inv_pos.mpr hp) ht).mpr htp
    rwa [inv_inv] at hh
  refine ⟨t⁻¹, hqp, ?_, ?_⟩
  · rw [inv_inv]
    have hh := mul_lt_mul_of_pos_left hlt (show 0 < 2 * p by positivity)
    have he : 2 * p * t₀ = 2 - p := by dsimp [t₀]; field_simp
    exact hh.trans_eq he
  · rw [inv_inv]
    exact (hball hdist).2

end CarpetEnergy.SelfSimilarPEnergy
