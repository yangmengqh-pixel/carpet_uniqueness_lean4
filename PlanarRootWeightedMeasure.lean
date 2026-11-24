import PlanarSobolevLocalization
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Comparing moments against a measure and its Sobolev dominator
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

/-- A density bound can be localized to a compact set supporting the
dominated measure. -/
theorem root_weight_domination_of_ae_eq {κ : Measure Plane2} {s : ℝ≥0∞}
    {a u : Plane2 → ℝ} (p : ℝ)
    {K : Set Plane2} (hK : MeasurableSet K) (hκK : ∀ᵐ x ∂κ, x ∈ K)
    (hEq : ∀ x ∈ K, a x = u x)
    (hdom : s • κ ≤ volume.withDensity (fun x ↦ ENNReal.ofReal (u x ^ p))) :
    s • κ ≤ volume.withDensity (fun x ↦ ENNReal.ofReal (a x ^ p)) := by
  have hκ : κ.restrict K = κ := Measure.restrict_eq_self_of_ae_mem hκK
  have hres :
      (volume.withDensity (fun x ↦ ENNReal.ofReal (u x ^ p))).restrict K =
      (volume.withDensity (fun x ↦ ENNReal.ofReal (a x ^ p))).restrict K := by
    rw [restrict_withDensity hK, restrict_withDensity hK]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hK] with x hx
    rw [hEq x hx]
  calc
    s • κ = (s • κ).restrict K := by rw [Measure.restrict_smul, hκ]
    _ ≤ (volume.withDensity (fun x ↦ ENNReal.ofReal (u x ^ p))).restrict K :=
      Measure.restrict_mono le_rfl hdom
    _ ≤ _ := hres.le.trans Measure.restrict_le_self

/-- A dominated measure's moment is bounded by the moment with the
pointwise root weight. -/
theorem smul_integral_rpow_le_root_weighted_lintegral {κ : Measure Plane2} {s : ℝ≥0∞}
    {a f : Plane2 → ℝ} (ha : Measurable a) (ha₀ : ∀ x, 0 ≤ a x)
    (hf : Measurable f) {p : ℝ} (hp : 0 < p)
    (hfi : Integrable (fun x ↦ |f x| ^ p) κ)
    (hdom : s • κ ≤ volume.withDensity (fun x ↦ ENNReal.ofReal (a x ^ p))) :
    s * ENNReal.ofReal (∫ x, |f x| ^ p ∂κ) ≤
      ∫⁻ x, ENNReal.ofReal (((a x + 1) * |f x|) ^ p) ∂volume := by
  let G (x : Plane2) := ENNReal.ofReal (|f x| ^ p)
  have hG : Measurable G :=
    ((Real.continuous_rpow_const hp.le).measurable.comp (continuous_abs.measurable.comp hf)).ennreal_ofReal
  have hA : Measurable (fun x ↦ ENNReal.ofReal (a x ^ p)) :=
    ((Real.continuous_rpow_const hp.le).measurable.comp ha).ennreal_ofReal
  rw [ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
  change s • (∫⁻ x, G x ∂κ) ≤ _
  rw [← lintegral_smul_measure]
  refine (lintegral_mono' hdom (show G ≤ G from le_rfl)).trans ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ hA hG]
  apply lintegral_mono
  intro x
  dsimp only [G, Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (ha₀ x) _), Real.mul_rpow (by linarith [ha₀ x]) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (ha₀ x) (by linarith) hp.le) (Real.rpow_nonneg (abs_nonneg _) _))

end CarpetEnergy
