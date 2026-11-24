import PlanarRootWeightedMeasure

/-!
# Moments of test functions attenuated by a reciprocal cutoff
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

theorem integral_attenuated_rpow_le {p : ℝ} (hp : 0 < p) {κ : Measure Plane2}
    {s : ℝ≥0∞} (hs : 0 < s) (hsfin : s ≠ ∞)
    {a b f : Plane2 → ℝ} (ha : Measurable a) (ha₀ : ∀ x, 0 ≤ a x)
    (hb : Measurable b) (hb01 : ∀ x, b x ∈ Icc (0 : ℝ) 1) (hf : Measurable f)
    (hfκ : Integrable (fun x ↦ |f x| ^ p) κ) (hfI : Integrable (fun x ↦ |f x| ^ p) volume)
    {C : ℝ} (hC : 0 ≤ C) (hrec : ∀ x, (a x + 1) * (1 - b x) ≤ C)
    (hdom : s • κ ≤ volume.withDensity (fun x ↦ ENNReal.ofReal (a x ^ p))) :
    (∫ x, |(1 - b x) * f x| ^ p ∂κ) ≤ (C ^ p / s.toReal) * ∫ x, |f x| ^ p ∂volume := by
  let F (x : Plane2) := (1 - b x) * f x
  have hFM : Measurable F := (measurable_const.sub hb).mul hf
  have hFκ : Integrable (fun x ↦ |F x| ^ p) κ := by
    apply hfκ.mono' (((Real.continuous_rpow_const hp.le).measurable.comp
      (continuous_abs.measurable.comp hFM)).aestronglyMeasurable)
    exact Eventually.of_forall fun x ↦ by
      change ‖|((1 - b x) * f x)| ^ p‖ ≤ |f x| ^ p
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        abs_mul, abs_of_nonneg (sub_nonneg.mpr (hb01 x).2)]
      exact Real.rpow_le_rpow (mul_nonneg (sub_nonneg.mpr (hb01 x).2) (abs_nonneg _))
        (mul_le_of_le_one_left (abs_nonneg _) (sub_le_self _ (hb01 x).1)) hp.le
  have h := smul_integral_rpow_le_root_weighted_lintegral ha ha₀ hFM hp hFκ hdom
  have hbound :
      (∫⁻ x, ENNReal.ofReal (((a x + 1) * |F x|) ^ p) ∂volume) ≤
        ENNReal.ofReal (C ^ p * ∫ x, |f x| ^ p ∂volume) := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hfI.const_mul _)
      (Eventually.of_forall fun x ↦ mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg (abs_nonneg _) _))]
    apply lintegral_mono
    intro x
    change ENNReal.ofReal (((a x + 1) * |(1 - b x) * f x|) ^ p) ≤
      ENNReal.ofReal (C ^ p * |f x| ^ p)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hb01 x).2), ← mul_assoc,
      ← Real.mul_rpow hC (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (mul_nonneg (mul_nonneg (by linarith [ha₀ x]) (sub_nonneg.mpr (hb01 x).2)) (abs_nonneg _)) _ hp.le
    exact mul_le_mul_of_nonneg_right (hrec x) (abs_nonneg _)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h.trans hbound)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)),
    ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hC _) (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _))] at hreal
  have hsR := ENNReal.toReal_pos hs.ne' hsfin
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hsR).mpr (by simpa only [mul_comm s.toReal] using hreal)

/-- Dominated convergence for moments against a fixed finite test,
as the cutoffs converge almost everywhere. -/
theorem tendsto_integral_attenuated_rpow {p : ℝ} (hp : 0 < p) {κ : Measure Plane2}
    {u : ℕ → Plane2 → ℝ} {b f : Plane2 → ℝ}
    (hu : ∀ n, Measurable (u n)) (hu01 : ∀ n x, u n x ∈ Icc (0 : ℝ) 1)
    (hf : Measurable f) (hfI : Integrable (fun x ↦ |f x| ^ p) κ)
    (hlim : ∀ᵐ x ∂κ, Tendsto (fun n ↦ u n x) atTop (𝓝 (b x))) :
    Tendsto (fun n ↦ ∫ x, |(1 - u n x) * f x| ^ p ∂κ) atTop
      (𝓝 (∫ x, |(1 - b x) * f x| ^ p ∂κ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ |f x| ^ p)
    (fun n ↦ ((Real.continuous_rpow_const hp.le).measurable.comp (continuous_abs.measurable.comp
      ((measurable_const.sub (hu n)).mul hf))).aestronglyMeasurable) hfI
  · intro n
    exact Eventually.of_forall fun x ↦ by
      change ‖|(1 - u n x) * f x| ^ p‖ ≤ |f x| ^ p
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        abs_mul, abs_of_nonneg (sub_nonneg.mpr (hu01 n x).2)]
      exact Real.rpow_le_rpow (mul_nonneg (sub_nonneg.mpr (hu01 n x).2) (abs_nonneg _))
        (mul_le_of_le_one_left (abs_nonneg _) (sub_le_self _ (hu01 n x).1)) hp.le
  · filter_upwards [hlim] with x hx
    exact ((Real.continuous_rpow_const hp.le).tendsto _).comp (((tendsto_const_nhds.sub hx).mul_const _).abs)

end CarpetEnergy
