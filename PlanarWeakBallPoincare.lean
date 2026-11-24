import PlanarCenteredBallMoment
import PlanarDerivativeNormBound
import PlanarMollificationLocalMoment
import WeakDerivativeMollification

/-!
# Ball Poincaré for weak planar coordinate derivatives
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CarpetEnergy

set_option maxHeartbeats 6200000 in
/-- The local smooth estimate passes to weak derivatives through
the mollifications, using the derivative mass in a ball of twice the radius. -/
theorem integral_abs_weak_sub_ballMean_rpow_le {p : ℝ} (hp : 1 ≤ p)
    {u : PlanarCoordinates → ℝ} (hum : Measurable u) (hu : Integrable u volume)
    (v : Fin 2 → PlanarCoordinates → ℝ) (hvm : ∀ i, Measurable (v i))
    (hv : ∀ i, Integrable (v i) volume)
    (hvP : ∀ i, Integrable (fun x ↦ |v i x| ^ p) volume)
    (hD : ∀ i, HasWeakDirectionalDerivative volume u (v i) (planarDirection i))
    (x : PlanarCoordinates) {r : ℝ} (hr : 0 < r) :
    let B := ball x r
    let a := (volume.real B)⁻¹ * ∫ y in B, u y ∂volume
    Integrable (fun y ↦ |u y - a| ^ p) (volume.restrict B) ∧
    (∫ y in B, |u y - a| ^ p ∂volume) ≤
      (4 * (2 * r) ^ p * (2 : ℝ) ^ (p - 1)) *
        ((∫ y in ball x (2 * r), |v 0 y| ^ p ∂volume) +
          ∫ y in ball x (2 * r), |v 1 y| ^ p ∂volume) := by
  let B := ball x r
  let μ := (volume : Measure PlanarCoordinates).restrict B
  let m := volume.real B
  let a := m⁻¹ * ∫ y, u y ∂μ
  let f (n : ℕ) := mollify volume n u
  let b (n : ℕ) := m⁻¹ * ∫ y, f n y ∂μ
  let D := (2 : ℝ) ^ (p - 1)
  let C := (4 * (2 * r) ^ p)
  let R := (∫ y in ball x (2 * r), |v 0 y| ^ p ∂volume) +
      ∫ y in ball x (2 * r), |v 1 y| ^ p ∂volume
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD₀ : 0 ≤ D := by dsimp only [D]; positivity
  have hR : 0 ≤ R := add_nonneg (integral_nonneg fun y ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (integral_nonneg fun y ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hfc (n : ℕ) : ContDiff ℝ 1 (f n) := contDiff_mollify volume hu
  have hI (n : ℕ) : Integrable (f n) volume := integrable_mollify volume n hu
  have hhp : 0 ≤ p := zero_le_one.trans hp
  have hmeans : Tendsto b atTop (𝓝 a) := by
    apply Tendsto.const_mul
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hh := tendsto_integral_abs_mollify_sub volume hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    rw [← integral_sub (hI n).restrict hu.restrict, Real.norm_eq_abs]
    exact abs_integral_le_integral_abs.trans
      (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ ↦ abs_nonneg _)
        ((hI n).sub hu).abs)
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n ↦ |f n y - b n| ^ p) atTop (𝓝 (|u y - a| ^ p)) := by
    filter_upwards [ae_restrict_of_ae (ae_tendsto_mollify volume hu)] with y hy
    exact ((Real.continuous_rpow_const hhp).tendsto _).comp (hy.sub hmeans).abs
  have hde (n : ℕ) (i : Fin 2) (y : PlanarCoordinates) :
      fderiv ℝ (f n) y (planarDirection i) = mollify volume n (v i) y :=
    fderiv_mollify_apply_eq_mollify_of_weakDerivative hu (hD i) n y
  have hfDb (n : ℕ) (y : PlanarCoordinates) :
      ‖fderiv ℝ (f n) y‖ ^ p ≤ D *
        (|mollify volume n (v 0) y| ^ p + |mollify volume n (v 1) y| ^ p) := by
    have h := planar_opNorm_rpow_le hp (fderiv ℝ (f n) y)
    simpa only [hde] using h
  have hev : ∀ᶠ n in atTop, (mollifierBump (X := PlanarCoordinates) n).rOut ≤ r :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually_le_const hr
  have hbound : ∀ᶠ n in atTop, (∫ y, |f n y - b n| ^ p ∂μ) ≤ C * D * R := by
    filter_upwards [hev] with n hn
    have hmind (i : Fin 2) :
        (∫ y, |mollify volume n (v i) y| ^ p ∂μ) ≤
          ∫ y in ball x (2 * r), |v i y| ^ p ∂volume :=
      integral_abs_mollify_rpow_ball_le hp (hvm i) (hv i) (hvP i) x hr hn
    have hIp (i : Fin 2) : Integrable (fun y ↦ |mollify volume n (v i) y| ^ p) μ :=
      (integrable_abs_rpow_mollify_and_integral_le volume hp n (hv i) (hvP i)).1.restrict
    have hFcont : Continuous (fun y ↦ ‖fderiv ℝ (f n) y‖ ^ p) :=
      ((hfc n).continuous_fderiv (by norm_num)).norm.rpow_const (fun _ ↦ Or.inr hhp)
    have hFI : Integrable (fun y ↦ ‖fderiv ℝ (f n) y‖ ^ p) μ :=
      (hFcont.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
    have hh := integral_mono hFI (((hIp 0).add (hIp 1)).const_mul D) (hfDb n)
    rw [integral_const_mul] at hh
    change _ ≤ D * ∫ y, |mollify volume n (v 0) y| ^ p + |mollify volume n (v 1) y| ^ p ∂μ at hh
    rw [integral_add (hIp 0) (hIp 1)] at hh
    have hF := hh.trans (mul_le_mul_of_nonneg_left (add_le_add (hmind 0) (hmind 1)) hD₀)
    have h := integral_abs_sub_ballMean_rpow_le hp (hfc n) x hr
    exact h.trans ((mul_le_mul_of_nonneg_left hF hC).trans_eq (by ring))
  have hMeas (n : ℕ) : Integrable (fun y ↦ |f n y - b n| ^ p) μ :=
    ((((hfc n).continuous.sub continuous_const).abs.rpow_const (fun _ ↦ Or.inr hhp)).continuousOn.integrableOn_compact
      (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  let L (y : PlanarCoordinates) := |u y - a| ^ p
  have hlim' : (fun y ↦ ENNReal.ofReal (L y)) =ᵐ[μ]
      (fun y ↦ liminf (fun n ↦ ENNReal.ofReal (|f n y - b n| ^ p)) atTop) := by
    filter_upwards [hlim] with y hy
    exact (((ENNReal.continuous_ofReal.tendsto _).comp hy).liminf_eq).symm
  have hFin : (∫⁻ y, ENNReal.ofReal (L y) ∂μ) ≤ ENNReal.ofReal (C * D * R) := by
    rw [lintegral_congr_ae hlim']
    refine (lintegral_liminf_le' (u := atTop) (fun n ↦ (hMeas n).aemeasurable.ennreal_ofReal)).trans
      (liminf_le_of_frequently_le' ?_)
    refine (hbound.mono (fun n hn ↦ ?_)).frequently
    rw [← ofReal_integral_eq_lintegral_ofReal (hMeas n) (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
    exact ENNReal.ofReal_le_ofReal hn
  have hL : Integrable L μ := by
    refine ⟨((Real.continuous_rpow_const hhp).measurable.comp
      (continuous_abs.measurable.comp (hum.sub measurable_const))).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)).mpr
      (hFin.trans_lt ENNReal.ofReal_lt_top)
  rw [← ofReal_integral_eq_lintegral_ofReal hL (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)] at hFin
  exact ⟨hL, (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hC hD₀) hR)).mp hFin⟩

end CarpetEnergy
