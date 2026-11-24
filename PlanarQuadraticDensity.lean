import PlanarWeakBallPoincare
import PlanarBoundedBallMeans
import UpperDensityBallCover

/-!
# Upper quadratic density from bounded means and local gradient mass
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace CarpetEnergy

/-- The sum of the two coordinate derivative moments as a measure. -/
noncomputable def planarGradientMeasure (p : ℝ) (v : Fin 2 → PlanarCoordinates → ℝ) :
    Measure PlanarCoordinates :=
  volume.withDensity (fun y ↦ ENNReal.ofReal (|v 0 y| ^ p + |v 1 y| ^ p))

theorem planarGradientMeasure_apply {p : ℝ} {v : Fin 2 → PlanarCoordinates → ℝ}
    (hv : ∀ i, Integrable (fun y ↦ |v i y| ^ p) volume) {A : Set PlanarCoordinates}
    (hA : MeasurableSet A) :
    planarGradientMeasure p v A =
      ENNReal.ofReal ((∫ y in A, |v 0 y| ^ p ∂volume) + ∫ y in A, |v 1 y| ^ p ∂volume) := by
  rw [planarGradientMeasure, withDensity_apply _ hA, ← integral_add (hv 0).restrict (hv 1).restrict]
  exact (ofReal_integral_eq_lintegral_ofReal ((hv 0).restrict.add (hv 1).restrict)
    (Eventually.of_forall fun _ ↦ add_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (abs_nonneg _) _))).symm

theorem isFiniteMeasure_planarGradientMeasure {p : ℝ} {v : Fin 2 → PlanarCoordinates → ℝ}
    (hv : ∀ i, Integrable (fun y ↦ |v i y| ^ p) volume) :
    IsFiniteMeasure (planarGradientMeasure p v) :=
  ⟨by rw [planarGradientMeasure_apply hv MeasurableSet.univ]; exact ENNReal.ofReal_lt_top⟩

private theorem abs_add_rpow_le {p a b : ℝ} (hp : 1 ≤ p) :
    |a + b| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  apply (Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (zero_le_one.trans hp)).trans
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨|a|, abs_nonneg _⟩ : ℝ≥0) (⟨|b|, abs_nonneg _⟩ : ℝ≥0) hp

set_option maxHeartbeats 6200000 in
/-- A point with bounded mollifications and upper gradient growth of
order (r^{2-p}) has bounded quadratic density for the dominated measure. -/
theorem unbounded_quadraticDensity_subset_of_sobolev_dominator
    {p : ℝ} (hp : 1 < p) {κ : Measure PlanarCoordinates} {s : ℝ≥0∞}
    (hs : 0 < s) (hsfin : s ≠ ∞)
    {u : PlanarCoordinates → ℝ} (hum : Measurable u) (hu₀ : ∀ x, 0 ≤ u x)
    (hu : Integrable u volume) (huP : Integrable (fun x ↦ u x ^ p) volume)
    (v : Fin 2 → PlanarCoordinates → ℝ) (hvm : ∀ i, Measurable (v i))
    (hv : ∀ i, Integrable (v i) volume) (hvP : ∀ i, Integrable (fun x ↦ |v i x| ^ p) volume)
    (hD : ∀ i, HasWeakDirectionalDerivative volume u (v i) (planarDirection i))
    (hdom : s • κ ≤ volume.withDensity (fun y ↦ ENNReal.ofReal (u y ^ p))) :
    UnboundedUpperBallDensity κ 2 ⊆ UnboundedPlanarMollification u ∪
      UnboundedUpperBallDensity (planarGradientMeasure p v) (2 - p) := by
  intro x hx
  by_contra hx'
  have hxu : x ∉ UnboundedPlanarMollification u := fun h ↦ hx' (Or.inl h)
  have hxv : x ∉ UnboundedUpperBallDensity (planarGradientMeasure p v) (2 - p) :=
    fun h ↦ hx' (Or.inr h)
  obtain ⟨M, hM, hmean⟩ := exists_bound_planar_ballMean_of_not_mem_unboundedMollification hu hu₀ hxu
  have : IsFiniteMeasure (planarGradientMeasure p v) := isFiniteMeasure_planarGradientMeasure hvP
  obtain ⟨N, R, hN, hR, hgrad⟩ := exists_upper_density_bound_of_notMem hxv
  let D := (2 : ℝ) ^ (p - 1)
  let C := D * (16 * D * N + 4 * M ^ p)
  have hD₀ : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hp₀ := zero_lt_one.trans hp
  have hsR := ENNReal.toReal_pos hs.ne' hsfin
  have hloc (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1 / 2) (hrR : 2 * r < R) :
      (∫ y in ball x r, u y ^ p ∂volume) ≤ C * r ^ (2 : ℕ) := by
    let B := ball x r
    let a := (volume.real B)⁻¹ * ∫ y in B, u y ∂volume
    have ha : 0 ≤ a := mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hu₀)
    have hA : a ≤ M := hmean r hr hr₁
    obtain ⟨hI, hPI⟩ := integral_abs_weak_sub_ballMean_rpow_le hp.le hum hu v hvm hv hvP hD x hr
    have hgr :
        (∫ y in ball x (2 * r), |v 0 y| ^ p ∂volume) + ∫ y in ball x (2 * r), |v 1 y| ^ p ∂volume ≤
          N * (2 * r) ^ (2 - p) := by
      have h := hgrad (2 * r) ⟨by positivity, hrR⟩
      rw [measureReal_def, planarGradientMeasure_apply hvP isOpen_ball.measurableSet,
        ENNReal.toReal_ofReal (add_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
          (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _))] at h
      exact h
    have hpow : (2 * r) ^ p * (2 * r) ^ (2 - p) = (2 * r) ^ (2 : ℕ) := by
      rw [← Real.rpow_add (show 0 < 2 * r by positivity), show p + (2 - p) = 2 by ring,
        Real.rpow_two]
    have hPIs : (∫ y in B, |u y - a| ^ p ∂volume) ≤ 16 * D * N * r ^ (2 : ℕ) := by
      refine (hPI.trans (mul_le_mul_of_nonneg_left hgr (by positivity))).trans_eq ?_
      calc
        _ = 4 * D * N * ((2 * r) ^ p * (2 * r) ^ (2 - p)) := by ring
        _ = _ := by rw [hpow]; ring
    have hμ₀ : 0 ≤ volume.real B := ENNReal.toReal_nonneg
    have hBfin : volume B ≠ ∞ := by
      rw [show B = ball x r from rfl, planar_volume_ball x hr.le]
      exact ENNReal.ofReal_ne_top
    let : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hBfin.lt_top⟩
    have hsumI : Integrable (fun y ↦ D * (|u y - a| ^ p + a ^ p)) (volume.restrict B) :=
      (hI.add (integrable_const _)).const_mul _
    have hE := integral_mono huP.restrict hsumI (fun y ↦ by
      change u y ^ p ≤ D * (|u y - a| ^ p + a ^ p)
      have h := abs_add_rpow_le (a := u y - a) (b := a) hp.le
      rwa [sub_add_cancel, abs_of_nonneg (hu₀ y), abs_of_nonneg ha] at h)
    rw [integral_const_mul] at hE
    change _ ≤ D * ∫ y in B, |u y - a| ^ p + a ^ p ∂volume at hE
    rw [integral_add hI (integrable_const _), integral_const,
      show (volume.restrict B).real univ = (volume B).toReal from by
        rw [measureReal_def, Measure.restrict_apply_univ], smul_eq_mul] at hE
    have hμ : (volume B).toReal = 4 * r ^ (2 : ℕ) := by
      rw [show B = ball x r from rfl, planar_volume_ball x hr.le, ENNReal.toReal_ofReal (by positivity)]
    rw [hμ] at hE
    refine hE.trans ((mul_le_mul_of_nonneg_left (add_le_add hPIs
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha hA hp₀.le) (by positivity))) hD₀).trans_eq ?_)
    dsimp only [C]
    ring
  let T := min (1 / 2 : ℝ) (R / 2)
  have hT : 0 < T := lt_min (by norm_num) (half_pos hR)
  let A := C / s.toReal + 1
  have hA : 0 < A := add_pos_of_nonneg_of_pos (div_nonneg hC hsR.le) one_pos
  obtain ⟨r, hr, hκ⟩ := hx A hA T hT
  have hr₁ : r ≤ 1 / 2 := hr.2.le.trans (min_le_left _ _)
  have hrR : 2 * r < R := by
    have h := hr.2.trans_le (min_le_right (1 / 2 : ℝ) (R / 2))
    linarith
  let B := ball x r
  have hdomB := hdom B
  rw [smul_apply, smul_eq_mul, withDensity_apply _ isOpen_ball.measurableSet,
    ← ofReal_integral_eq_lintegral_ofReal huP.restrict
      (Eventually.of_forall fun y ↦ Real.rpow_nonneg (hu₀ y) _)] at hdomB
  have hBound : s * ENNReal.ofReal (A * r ^ (2 : ℕ)) ≤ ENNReal.ofReal (C * r ^ (2 : ℕ)) := by
    have hκ' : ENNReal.ofReal (A * r ^ (2 : ℕ)) ≤ κ B := by
      simpa only [Real.rpow_two] using hκ
    exact (mul_le_mul_of_nonneg_left hκ' bot_le).trans (hdomB.trans (ENNReal.ofReal_le_ofReal (hloc r hr.1 hr₁ hrR)))
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ A * r ^ (2 : ℕ)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ C * r ^ (2 : ℕ))] at hh
  rw [← mul_assoc] at hh
  have hf := (mul_le_mul_iff_left₀ (sq_pos_of_pos hr.1)).mp hh
  dsimp only [A] at hf
  rw [mul_add, mul_div_cancel₀ _ hsR.ne', mul_one] at hf
  linarith

end CarpetEnergy
