import SmoothTranslationLp
import SmoothMollificationLp
import WeakDerivativeMollification
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Translation estimates for weakly differentiable functions
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [HasContDiffBump X] [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [μ.IsAddHaarMeasure]

set_option maxHeartbeats 2200000 in
/-- The directional Sobolev estimate passes from mollifications to the
original function using Fatou's lemma. -/
theorem HasWeakDirectionalDerivative.integral_abs_translation_sub_rpow_le
    {p : ℝ} (hp : 1 ≤ p) {u v : X → ℝ} {z : X}
    (h : HasWeakDirectionalDerivative μ u v z)
    (hu : Integrable u μ) (hv : Integrable v μ)
    (hvp : Integrable (fun x ↦ |v x| ^ p) μ) :
    Integrable (fun x ↦ |u (x + z) - u x| ^ p) μ ∧
      (∫ x, |u (x + z) - u x| ^ p ∂μ) ≤ ∫ x, |v x| ^ p ∂μ := by
  let B := ∫ x, |v x| ^ p ∂μ
  let F (n : ℕ) (x : X) := |mollify μ n u (x + z) - mollify μ n u x| ^ p
  let G (x : X) := |u (x + z) - u x| ^ p
  have hF₀ (n : ℕ) (x : X) : 0 ≤ F n x := Real.rpow_nonneg (abs_nonneg _) _
  have hG₀ (x : X) : 0 ≤ G x := Real.rpow_nonneg (abs_nonneg _) _
  have hD (n : ℕ) (x : X) : fderiv ℝ (mollify μ n u) x z = mollify μ n v x :=
    fderiv_mollify_apply_eq_mollify_of_weakDerivative hu h n x
  have hF (n : ℕ) : Integrable (F n) μ ∧ (∫ x, F n x ∂μ) ≤ B := by
    obtain ⟨hDI, hDB⟩ := integrable_abs_rpow_mollify_and_integral_le μ hp n hv hvp
    have hI : Integrable (fun x ↦ |fderiv ℝ (mollify μ n u) x z| ^ p) μ := by
      simp only [hD]
      exact hDI
    obtain ⟨hFI, hFB⟩ := integral_abs_translation_sub_rpow_le_of_contDiff μ hp
      (contDiff_mollify μ hu) z hI
    simp only [hD] at hFB
    exact ⟨hFI, hFB.trans hDB⟩
  have ha := ae_tendsto_mollify μ hu
  have ha' : ∀ᵐ x ∂μ, Tendsto (fun n ↦ mollify μ n u (x + z)) atTop (𝓝 (u (x + z))) :=
    (measurePreserving_add_right μ z).quasiMeasurePreserving.ae ha
  have hGlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)) := by
    filter_upwards [ha, ha'] with x hx hx'
    exact ((Real.continuous_rpow_const (zero_le_one.trans hp)).tendsto _).comp (hx'.sub hx).abs
  have hlim := lintegral_liminf_le' (u := atTop) (fun n ↦ (hF n).1.aemeasurable.ennreal_ofReal)
  have hlim' : (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≤ ENNReal.ofReal B := by
    have he : (fun x ↦ ENNReal.ofReal (G x)) =ᵐ[μ]
        (fun x ↦ liminf (fun n ↦ ENNReal.ofReal (F n x)) atTop) := by
      filter_upwards [hGlim] with x hx
      exact (((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq).symm
    rw [lintegral_congr_ae he]
    refine hlim.trans (liminf_le_of_frequently_le' (Eventually.of_forall fun n ↦ ?_).frequently)
    rw [← ofReal_integral_eq_lintegral_ofReal (hF n).1 (Eventually.of_forall (hF₀ n))]
    exact ENNReal.ofReal_le_ofReal (hF n).2
  have hG : Integrable G μ := ⟨aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hF n).1.aestronglyMeasurable) hGlim,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hG₀)).mpr
      (hlim'.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hG, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hG (Eventually.of_forall hG₀)] at hlim'
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _))).mp hlim'

end CarpetEnergy
