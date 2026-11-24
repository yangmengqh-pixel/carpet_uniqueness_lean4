import SmoothMollification
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Jensen's inequality for the normalized mollifier
-/

open ContinuousLinearMap Filter Function MeasureTheory Set
open scoped Convolution ENNReal

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [HasContDiffBump X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [μ.IsAddHaarMeasure]

set_option maxHeartbeats 3400000 in
theorem abs_mollify_rpow_le_mollify_abs_rpow {p : ℝ} (hp : 1 ≤ p) (n : ℕ)
    {f : X → ℝ} (hf : Integrable f μ) (hfp : Integrable (fun x ↦ |f x| ^ p) μ) (x : X) :
    |mollify μ n f x| ^ p ≤ mollify μ n (fun y ↦ |f y| ^ p) x := by
  let B := mollifierBump (X := X) n
  let K := B.normed μ
  let ν := μ.withDensity (fun y ↦ ENNReal.ofReal (K y))
  have hK₀ (y : X) : 0 ≤ K y := B.nonneg_normed y
  have hKc : Continuous K := B.continuous_normed
  have hKm : Measurable (fun y ↦ ENNReal.ofReal (K y)) := hKc.measurable.ennreal_ofReal
  have htop : ∀ᵐ y ∂μ, ENNReal.ofReal (K y) < ∞ :=
    Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)
  have : IsProbabilityMeasure ν := ⟨by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal B.integrable_normed (Eventually.of_forall hK₀),
      B.integral_normed, ENNReal.ofReal_one]⟩
  let C : ℝ := (∫ y, B y ∂μ)⁻¹
  have hC : 0 ≤ C := inv_nonneg.mpr B.integral_pos.le
  have hKb (y : X) : ‖K y‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hK₀ y)]
    change B y / (∫ y, B y ∂μ) ≤ C
    rw [div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_right B.le_one hC).trans_eq (one_mul _)
  have hInt {g : X → ℝ} (hg : Integrable g μ) : Integrable (fun y ↦ g (x - y)) ν := by
    have htr : Integrable (fun y ↦ g (x - y)) μ := by
      simpa only [sub_eq_add_neg, Function.comp_apply] using (hg.comp_add_left x).comp_neg
    apply (integrable_withDensity_iff_integrable_smul' hKm htop).mpr
    simpa only [ENNReal.toReal_ofReal (hK₀ _), smul_eq_mul] using htr.bdd_mul hKc.aestronglyMeasurable
      (Eventually.of_forall hKb)
  have hI {g : X → ℝ} : (∫ y, g (x - y) ∂ν) = mollify μ n g x := by
    rw [integral_withDensity_eq_integral_toReal_smul hKm htop]
    simp only [ENNReal.toReal_ofReal (hK₀ _), smul_eq_mul]
    rfl
  have hpow := (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const (zero_le_one.trans hp)).continuousOn isClosed_Ici
    (Eventually.of_forall fun y ↦ (abs_nonneg (f (x - y)) : 0 ≤ |f (x - y)|))
    (hInt hf).abs (hInt hfp)
  have hmean : |mollify μ n f x| ≤ ∫ y, |f (x - y)| ∂ν := by
    rw [← hI]
    exact abs_integral_le_integral_abs
  exact (Real.rpow_le_rpow (abs_nonneg _) hmean (zero_le_one.trans hp)).trans
    (hpow.trans_eq (hI (g := fun y ↦ |f y| ^ p)))

set_option maxHeartbeats 1250000 in
/-- Mollification preserves the upper bound on the (L^p) moment. -/
theorem integrable_abs_rpow_mollify_and_integral_le {p : ℝ} (hp : 1 ≤ p) (n : ℕ)
    {f : X → ℝ} (hf : Integrable f μ) (hfp : Integrable (fun x ↦ |f x| ^ p) μ) :
    Integrable (fun x ↦ |mollify μ n f x| ^ p) μ ∧
      (∫ x, |mollify μ n f x| ^ p ∂μ) ≤ ∫ x, |f x| ^ p ∂μ := by
  let G := fun x ↦ |f x| ^ p
  have hG₀ (x : X) : 0 ≤ G x := Real.rpow_nonneg (abs_nonneg _) _
  have hA : Integrable (mollify μ n G) μ := integrable_mollify μ n hfp
  have hle (x : X) : |mollify μ n f x| ^ p ≤ mollify μ n G x :=
    abs_mollify_rpow_le_mollify_abs_rpow μ hp n hf hfp x
  have hmeas : AEStronglyMeasurable (fun x ↦ |mollify μ n f x| ^ p) μ :=
    ((contDiff_mollify μ hf).continuous.abs.rpow_const (fun _ ↦ Or.inr (zero_le_one.trans hp))).aestronglyMeasurable
  have hI : Integrable (fun x ↦ |mollify μ n f x| ^ p) μ := by
    apply hA.mono hmeas
    exact Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        Real.norm_eq_abs, abs_of_nonneg (mollify_nonneg μ n hG₀ x)]
      exact hle x)
  refine ⟨hI, (integral_mono hI hA hle).trans_eq ?_⟩
  unfold mollify
  rw [integral_convolution (lsmul ℝ ℝ) ((mollifierBump n).integrable_normed (μ := μ)) hfp,
    (mollifierBump n).integral_normed]
  simp only [lsmul_apply, one_smul]

end CarpetEnergy
