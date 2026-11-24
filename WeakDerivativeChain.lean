import WeakDerivativeMollification
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Chain rule for a scalar function with bounded derivative

Both a weakly differentiable function and its derivative have
smooth approximations in L¹. The classical chain rule and
integration by parts pass to the limit through bounded tests.
-/

open Filter Function MeasureTheory Set
open scoped NNReal Topology

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [HasContDiffBump X] [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [μ.IsAddHaarMeasure]

set_option maxHeartbeats 2600000 in
theorem HasWeakDirectionalDerivative.comp_bounded_deriv
    {u v : X → ℝ} {e : X} (hu : Integrable u μ) (hv : Integrable v μ)
    (h : HasWeakDirectionalDerivative μ u v e)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) (hγ₀ : γ 0 = 0)
    {C : ℝ} (hC : 0 ≤ C) (hC' : ∀ t, |deriv γ t| ≤ C) :
    HasWeakDirectionalDerivative μ (γ ∘ u) (fun x ↦ deriv γ (u x) * v x) e := by
  let U (n : ℕ) := mollify μ n u
  let V (n : ℕ) := mollify μ n v
  let C₀ : ℝ≥0 := ⟨C, hC⟩
  have hγd : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  have hγdc : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have hLip : LipschitzWith C₀ γ := lipschitzWith_of_nnNorm_deriv_le hγd fun t ↦ by
    change ‖deriv γ t‖ ≤ C
    rw [Real.norm_eq_abs]
    exact hC' t
  have hLip' (a b : ℝ) : |γ a - γ b| ≤ C * |a - b| := by
    have hd := (lipschitzWith_iff_dist_le_mul.mp hLip) a b
    change dist (γ a) (γ b) ≤ C * dist a b at hd
    simpa only [Real.dist_eq] using hd
  have hIntγ {f : X → ℝ} (hf : Integrable f μ) : Integrable (γ ∘ f) μ := by
    apply (hf.norm.const_mul C).mono (hγ.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    filter_upwards with x
    have hh := hLip' (f x) 0
    rw [hγ₀, sub_zero, sub_zero] at hh
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC, abs_abs] using hh
  have hIntγd {f g : X → ℝ} (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ) :
      Integrable (fun x ↦ deriv γ (f x) * g x) μ :=
    hg.bdd_mul (hγdc.comp_aestronglyMeasurable hf)
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hC' _)
  have hU (n : ℕ) : Integrable (U n) μ := integrable_mollify μ n hu
  have hV (n : ℕ) : Integrable (V n) μ := integrable_mollify μ n hv
  have huL := tendsto_integral_abs_mollify_sub μ hu
  have hvL := tendsto_integral_abs_mollify_sub μ hv
  let a (n : ℕ) := γ ∘ U n
  let a₀ := γ ∘ u
  let b (n : ℕ) (x : X) := deriv γ (U n x) * V n x
  let b₀ (x : X) := deriv γ (u x) * v x
  have ha (n : ℕ) : Integrable (a n) μ := hIntγ (hU n)
  have ha₀ : Integrable a₀ μ := hIntγ hu
  have hb (n : ℕ) : Integrable (b n) μ := hIntγd (hU n).aestronglyMeasurable (hV n)
  have hb₀ : Integrable b₀ μ := hIntγd hu.aestronglyMeasurable hv
  have haL : Tendsto (fun n ↦ ∫ x, |a n x - a₀ x| ∂μ) atTop (𝓝 0) := by
    have hh := huL.const_mul C
    rw [mul_zero] at hh
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))
    intro n
    change (∫ x, |a n x - a₀ x| ∂μ) ≤ C * ∫ x, |U n x - u x| ∂μ
    rw [← integral_const_mul]
    exact integral_mono ((ha n).sub ha₀).abs (((hU n).sub hu).abs.const_mul C)
      (fun x ↦ hLip' (U n x) (u x))
  let err (n : ℕ) (x : X) := |(deriv γ (U n x) - deriv γ (u x)) * v x|
  have herr (n : ℕ) : Integrable (err n) μ := by
    have h₁ := hIntγd (hU n).aestronglyMeasurable hv
    have h₂ := hIntγd hu.aestronglyMeasurable hv
    simpa only [err, sub_mul, Pi.sub_apply] using (h₁.sub h₂).abs
  have herrL : Tendsto (fun n ↦ ∫ x, err n x ∂μ) atTop (𝓝 0) := by
    have hh : Tendsto (fun n ↦ ∫ x, err n x ∂μ) atTop (𝓝 (∫ _ : X, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x ↦ 2 * C * |v x|)
        (fun n ↦ (herr n).aestronglyMeasurable) (hv.abs.const_mul (2 * C))
      · intro n
        apply Eventually.of_forall
        intro x
        dsimp only [err]
        rw [Real.norm_eq_abs, abs_abs, abs_mul]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact (abs_sub _ _).trans (by linarith only [hC' (U n x), hC' (u x)])
      · filter_upwards [ae_tendsto_mollify μ hu] with x hx
        have ht := (hγdc.tendsto _).comp hx
        simpa only [err, U, Function.comp_def, sub_self, zero_mul, abs_zero] using
          ((ht.sub (tendsto_const_nhds (x := deriv γ (u x)))).mul_const (v x)).abs
    simpa only [integral_zero] using hh
  have hbL : Tendsto (fun n ↦ ∫ x, |b n x - b₀ x| ∂μ) atTop (𝓝 0) := by
    have hh := (hvL.const_mul C).add herrL
    rw [mul_zero, zero_add] at hh
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))
    intro n
    change (∫ x, |b n x - b₀ x| ∂μ) ≤ C * (∫ x, |V n x - v x| ∂μ) + ∫ x, err n x ∂μ
    have hI : Integrable (fun x ↦ C * |V n x - v x|) μ := ((hV n).sub hv).abs.const_mul C
    rw [← integral_const_mul, ← integral_add hI (herr n)]
    apply integral_mono ((hb n).sub hb₀).abs (hI.add (herr n))
    intro x
    change |b n x - b₀ x| ≤ C * |V n x - v x| + err n x
    have he : b n x - b₀ x =
        deriv γ (U n x) * (V n x - v x) + (deriv γ (U n x) - deriv γ (u x)) * v x := by
      dsimp [b, b₀]
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add_left (mul_le_mul_of_nonneg_right (hC' _) (abs_nonneg _)) _
  intro φ hφ hφs
  let D (x : X) := fderiv ℝ φ x e
  have hDc : Continuous D := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨B₁, hB₁⟩ := hφs.exists_bound_of_continuous hφ.continuous
  obtain ⟨B₂, hB₂⟩ := (HasCompactSupport.fderiv_apply ℝ hφs e).exists_bound_of_continuous hDc
  have hφb (x : X) : |φ x| ≤ max B₁ 0 := by
    rw [← Real.norm_eq_abs]
    exact (hB₁ x).trans (le_max_left _ _)
  have hDb (x : X) : |D x| ≤ max B₂ 0 := by
    rw [← Real.norm_eq_abs]
    exact (hB₂ x).trans (le_max_left _ _)
  have hleft := tendsto_integral_mul_of_integral_abs_sub ha ha₀ hDc.aestronglyMeasurable hDb haL
  have hright := tendsto_integral_mul_of_integral_abs_sub hb hb₀ hφ.continuous.aestronglyMeasurable hφb hbL
  have heq (n : ℕ) : (∫ x, a n x * D x ∂μ) = -(∫ x, b n x * φ x ∂μ) := by
    have hUn : ContDiff ℝ 1 (U n) := contDiff_mollify μ (n := n) hu
    have haDiff : Differentiable ℝ (a n) := (hγ.comp hUn).differentiable (by norm_num)
    have hd (x : X) : fderiv ℝ (a n) x e = b n x := by
      change fderiv ℝ (γ ∘ U n) x e = b n x
      rw [fderiv_comp x (hγd _) (hUn.differentiable (by norm_num) _),
        ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul,
        fderiv_mollify_apply_eq_mollify_of_weakDerivative hu h]
    have hφbound : ∀ᵐ x ∂μ, ‖φ x‖ ≤ max B₁ 0 :=
      Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hφb x
    have hDbound : ∀ᵐ x ∂μ, ‖D x‖ ≤ max B₂ 0 :=
      Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hDb x
    have h₁ : Integrable (fun x ↦ fderiv ℝ (a n) x e * φ x) μ := by
      simp_rw [hd]
      exact (hb n).mul_bdd hφ.continuous.aestronglyMeasurable hφbound
    have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁
      ((ha n).mul_bdd hDc.aestronglyMeasurable hDbound)
      ((ha n).mul_bdd hφ.continuous.aestronglyMeasurable hφbound)
      (fun x _ ↦ haDiff x) (fun x _ ↦ hφ.differentiable (by norm_num) x)
    simpa only [hd] using hi
  exact tendsto_nhds_unique hleft (hright.neg.congr fun n ↦ (heq n).symm)

end CarpetEnergy
