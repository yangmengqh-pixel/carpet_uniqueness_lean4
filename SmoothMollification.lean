import IntegralAbsoluteConvergence
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth mollification in L¹

Normalized smooth bump functions form an approximate identity.
Lebesgue differentiation supplies pointwise convergence almost
everywhere, and preservation of mass gives L¹ convergence.
-/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped Convolution Topology

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [HasContDiffBump X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [μ.IsAddHaarMeasure]

/-- A sequence of smooth bumps of uniformly comparable radii. -/
noncomputable def mollifierBump (n : ℕ) : ContDiffBump (0 : X) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

/-- Smooth convolution with the normalized bump at index `n`. -/
noncomputable def mollify (n : ℕ) (f : X → ℝ) : X → ℝ :=
  (mollifierBump n).normed μ ⋆[lsmul ℝ ℝ, μ] f

theorem contDiff_mollify {n : ℕ} {f : X → ℝ} (hf : Integrable f μ) :
    ContDiff ℝ 1 (mollify μ n f) :=
  (mollifierBump n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (mollifierBump n).contDiff_normed hf.locallyIntegrable

theorem integrable_mollify (n : ℕ) {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (mollify μ n f) μ :=
  ((mollifierBump n).integrable_normed (μ := μ)).integrable_convolution (lsmul ℝ ℝ) hf

omit [FiniteDimensional ℝ X] [BorelSpace X] [μ.IsAddHaarMeasure] in
theorem mollify_nonneg (n : ℕ) {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) (x : X) :
    0 ≤ mollify μ n f x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg ((mollifierBump n).nonneg_normed (μ := μ) y) (hf _)

theorem ae_tendsto_mollify {f : X → ℝ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ mollify μ n f x) atTop (𝓝 (f x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · refine Eventually.of_forall fun n ↦ ?_
    unfold mollifierBump
    linarith
  · exact hf.locallyIntegrable

private theorem integral_mollify (n : ℕ) {f : X → ℝ} (hf : Integrable f μ) :
    (∫ x, mollify μ n f x ∂μ) = ∫ x, f x ∂μ := by
  unfold mollify
  rw [integral_convolution (lsmul ℝ ℝ)
    ((mollifierBump n).integrable_normed (μ := μ)) hf, (mollifierBump n).integral_normed]
  simp only [lsmul_apply, one_smul]

private theorem tendsto_integral_abs_mollify_sub_of_nonneg {f : X → ℝ}
    (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x) :
    Tendsto (fun n ↦ ∫ x, |mollify μ n f x - f x| ∂μ) atTop (𝓝 0) := by
  apply tendsto_integral_abs_sub_of_nonneg_of_integrals μ
    (fun n ↦ integrable_mollify μ n hf) hf
    (fun n ↦ Eventually.of_forall (mollify_nonneg μ n hn)) (Eventually.of_forall hn)
    (ae_tendsto_mollify μ hf)
  exact tendsto_const_nhds.congr (fun n ↦ (integral_mollify μ n hf).symm)

theorem mollify_sub (n : ℕ) {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (x : X) :
    mollify μ n (f - g) x = mollify μ n f x - mollify μ n g x := by
  let B := mollifierBump (X := X) n
  have h₁ := ((B.hasCompactSupport_normed (μ := μ)).convolutionExists_left (lsmul ℝ ℝ)
    B.continuous_normed hf.locallyIntegrable x).integrable
  have h₂ := ((B.hasCompactSupport_normed (μ := μ)).convolutionExists_left (lsmul ℝ ℝ)
    B.continuous_normed hg.locallyIntegrable x).integrable
  change (∫ t, B.normed μ t * (f - g) (x - t) ∂μ) =
    (∫ t, B.normed μ t * f (x - t) ∂μ) - ∫ t, B.normed μ t * g (x - t) ∂μ
  simp_rw [Pi.sub_apply, mul_sub]
  exact integral_sub h₁ h₂

theorem tendsto_integral_abs_mollify_sub {f : X → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n ↦ ∫ x, |mollify μ n f x - f x| ∂μ) atTop (𝓝 0) := by
  let fpos (x : X) := max (f x) 0
  let fneg (x : X) := max (-f x) 0
  have hp : Integrable fpos μ := hf.sup (integrable_zero _ _ _)
  have hn : Integrable fneg μ := hf.neg.sup (integrable_zero _ _ _)
  have hdiff : f = fpos - fneg := by
    funext x
    change f x = max (f x) 0 - max (-f x) 0
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_sub, neg_neg]
  have hi (n : ℕ) : (∫ x, |mollify μ n f x - f x| ∂μ) ≤
      (∫ x, |mollify μ n fpos x - fpos x| ∂μ) + ∫ x, |mollify μ n fneg x - fneg x| ∂μ := by
    have hIpos : Integrable (fun x ↦ |mollify μ n fpos x - fpos x|) μ :=
      ((integrable_mollify μ n hp).sub hp).abs
    have hIneg : Integrable (fun x ↦ |mollify μ n fneg x - fneg x|) μ :=
      ((integrable_mollify μ n hn).sub hn).abs
    have hi : Integrable (fun x ↦ |mollify μ n f x - f x|) μ :=
      ((integrable_mollify μ n hf).sub hf).abs
    rw [← integral_add hIpos hIneg]
    apply integral_mono hi (hIpos.add hIneg)
    intro x
    have h := mollify_sub μ n hp hn x
    have he : mollify μ n f x - f x =
        (mollify μ n fpos x - fpos x) - (mollify μ n fneg x - fneg x) := by
      rw [hdiff, h, Pi.sub_apply]
      ring
    change |mollify μ n f x - f x| ≤ |mollify μ n fpos x - fpos x| + |mollify μ n fneg x - fneg x|
    rw [he]
    exact (abs_sub _ _)
  have hpos := tendsto_integral_abs_mollify_sub_of_nonneg μ hp (fun _ ↦ le_max_right _ _)
  have hneg := tendsto_integral_abs_mollify_sub_of_nonneg μ hn (fun _ ↦ le_max_right _ _)
  have hu := hpos.add hneg
  rw [zero_add] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) hi

end CarpetEnergy
