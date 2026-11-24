import EnergyPlanarBallMoments
import EnergyCarpetSobolev
import EnergyPlanarSobolevExponent

/-!
# A density point obstruction in the low walk-dimension regime
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

private theorem not_uniform_rpow_le_of_lt {a C R s t : ℝ} (ha : 0 < a)
    (hR : 0 < R) (hst : s < t) :
    ¬ ∀ r ∈ Ioo 0 R, a * r ^ s ≤ C * r ^ t := by
  intro h
  have hlim : Tendsto (fun r : ℝ ↦ C * r ^ (t - s)) (𝓝[>] 0) (𝓝 0) := by
    have he := ((Real.continuous_rpow_const (sub_nonneg.mpr hst.le)).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Real.zero_rpow (sub_pos.mpr hst).ne', mul_zero] using he.const_mul C
  have hrs : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioo 0 R :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (gt_mem_nhds hR))
  obtain ⟨r, hr, hlt⟩ := (hrs.and (hlim.eventually_lt_const ha)).exists
  have hpow := Real.rpow_pos_of_pos hr.1 s
  have hh := (mul_le_mul_iff_right₀ hpow).mp
    (show r ^ s * a ≤ r ^ s * (C * r ^ (t - s)) from by
      rw [mul_comm _ a, mul_left_comm, ← Real.rpow_add hr.1, add_sub_cancel]
      exact h r hr)
  exact hlt.not_ge hh

set_option maxHeartbeats 3500000 in
/-- The pulse argument in Case 2 of Theorem 5.2. An upper bound of
order (r^{2-p}) for the volume pushforward suffices at the chosen point. -/
theorem not_exists_planar_density_point_of_scalingFactor_le_one
    (hρ : E.scalingFactor ≤ 1)
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (u : Fin 2 → E.continuousCore) :
    ¬ ∃ (z : Fin 2 → ℝ) (a b c R : ℝ), 0 < a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 < R ∧
      let H := E.continuousCoreTuple u
      let ν := carpetMeasure.map H
      let κ := (E.pairEnergyMeasure u).map H
      ∀ r ∈ Ioo 0 R,
        a * r ^ (2 : ℕ) ≤ ν.real (ball z r) ∧
        ν.real (ball z r) ≤ c * r ^ (2 - p) ∧ κ.real (ball z r) ≤ b * r ^ (2 : ℕ) := by
  rintro ⟨z, a, b, c, R, ha, hb, hc₀, hR, hdensity⟩
  have hp := zero_lt_one.trans E.one_lt_p
  have hp₂ := E.lt_two_of_scalingFactor_le_one hρ
  obtain ⟨q, hq, hexp, hratio⟩ := E.exists_planar_sobolev_exponent hρ
  have hq₀ := hp.trans hq
  obtain ⟨A, hA, hSob⟩ := E.exists_lpNorm_le_graph_of_geometric_ratio hq.le hratio
  obtain ⟨D, hD, hPulse⟩ := E.exists_planar_ball_pulse h hc u
  let K := D ^ p * (9 * b)
  let L := c * (3 : ℝ) ^ (2 - p)
  let Cp := (2 : ℝ) ^ p * K + L
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  let H := E.continuousCoreTuple u
  let ν := carpetMeasure.map H
  let κ := (E.pairEnergyMeasure u).map H
  have ht : 2 * q⁻¹ < (2 - p) * p⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (lt_div_iff₀ hp).mpr
    calc
      2 * q⁻¹ * p = 2 * p * q⁻¹ := by ring
      _ < 2 - p := hexp
  apply not_uniform_rpow_le_of_lt (Real.rpow_pos_of_pos ha q⁻¹)
    (div_pos hR (by norm_num : (0 : ℝ) < 3)) ht
  intro r hr
  have hr₀ : 0 < r := hr.1
  have hrR : r ∈ Ioo 0 R := ⟨hr₀, hr.2.trans (div_lt_self hR (by norm_num))⟩
  have h3r : 3 * r ∈ Ioo 0 R := ⟨by positivity, by linarith [(lt_div_iff₀ (show (0 : ℝ) < 3 by norm_num)).mp hr.2]⟩
  have hκ : (D / r) ^ p * κ.real (ball z (3 * r)) ≤ K * r ^ (2 - p) := by
    refine (mul_le_mul_of_nonneg_left (hdensity (3 * r) h3r).2.2
      (Real.rpow_nonneg (div_nonneg hD.le hr₀.le) _)).trans_eq ?_
    rw [Real.div_rpow hD.le hr₀.le, Real.rpow_sub hr₀, Real.rpow_two, mul_pow]
    dsimp only [K]
    ring
  have hν : ν.real (ball z (3 * r)) ≤ L * r ^ (2 - p) := by
    refine ((hdensity _ h3r).2.1).trans_eq ?_
    rw [Real.mul_rpow (by norm_num) hr₀.le, mul_assoc]
  obtain ⟨v, hvq, hvp, hvE⟩ := hPulse z r hr₀
  let f := E.continuousCoreToDomain v
  have hM (s : ℝ) : (∫ x, |v.val x| ^ s ∂carpetMeasure) ≥ 0 :=
    integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hfp : ‖(f : CarpetLp p)‖ ^ p ≤ L * r ^ (2 - p) := by
    rw [← integral_abs_rpow_eq_norm_rpow hp]
    refine le_trans ?_ (hvp.trans hν)
    exact le_of_eq (integral_congr_ae ((continuousLp_ae_eq p v.val).mono
      (fun x hx ↦ congrArg (fun y : ℝ ↦ |y| ^ p) hx)))
  have hfe : (E.energy f : ℝ) ≤ (2 : ℝ) ^ p * (K * r ^ (2 - p)) := by
    have hx := hvE.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg (div_nonneg hD.le hr₀.le) _)
        ENNReal.toReal_nonneg) hκ (inv_nonneg.mpr hp.le)) (by norm_num))
    have hy := Real.rpow_le_rpow (apply_nonneg E.rootSeminorm f) hx hp.le
    rw [E.rootSeminorm_apply, Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne',
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _),
      Real.rpow_inv_rpow (by positivity) hp.ne'] at hy
    exact hy
  have hg : E.graphSeminorm f ≤ (Cp * r ^ (2 - p)) ^ p⁻¹ := by
    rw [E.graphSeminorm_apply, energyGraphNorm]
    apply Real.rpow_le_rpow (by positivity) _ (inv_nonneg.mpr hp.le)
    exact (add_le_add hfe hfp).trans_eq (by dsimp only [Cp]; ring)
  have hLp : (a * r ^ (2 : ℕ)) ^ q⁻¹ ≤ lpNorm v.val (ENNReal.ofReal q) carpetMeasure := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq₀) ENNReal.ofReal_ne_top
      v.val.continuous.aestronglyMeasurable, ENNReal.toReal_ofReal hq₀.le]
    simp only [Real.norm_eq_abs]
    exact Real.rpow_le_rpow (by positivity) ((hdensity _ hrR).1.trans (hvq q hq₀))
      (inv_nonneg.mpr hq₀.le)
  have hcomb := hLp.trans ((hSob v).trans (mul_le_mul_of_nonneg_left hg hA.le))
  rw [Real.mul_rpow ha.le (by positivity), ← Real.rpow_natCast_mul hr₀.le,
    Real.mul_rpow hCp (Real.rpow_nonneg hr₀.le _), ← Real.rpow_mul hr₀.le, ← mul_assoc] at hcomb
  simpa only [Nat.cast_ofNat] using hcomb

end CarpetEnergy.SelfSimilarPEnergy
