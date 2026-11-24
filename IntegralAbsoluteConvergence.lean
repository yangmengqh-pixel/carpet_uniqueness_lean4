import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Convergence of absolute differences from convergence of mass

For nonnegative functions, convergence almost everywhere and
convergence of the integrals imply convergence in L¹.
-/

open Filter MeasureTheory
open scoped Topology

namespace CarpetEnergy

theorem tendsto_integral_abs_sub_of_nonneg_of_integrals {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hf₀ : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) (hg₀ : ∀ᵐ x ∂μ, 0 ≤ g x)
    (h : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hm : Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ))) :
    Tendsto (fun n ↦ ∫ x, |f n x - g x| ∂μ) atTop (𝓝 0) := by
  let m (n : ℕ) (x : X) := min (f n x) (g x)
  have hmInt (n : ℕ) : Integrable (m n) μ := by
    have hmeas : AEStronglyMeasurable (m n) μ :=
      ((hf n).aemeasurable.min hg.aemeasurable).aestronglyMeasurable
    apply hg.mono hmeas
    filter_upwards [hf₀ n, hg₀] with x hx hy
    change ‖min (f n x) (g x)‖ ≤ ‖g x‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_min hx hy), abs_of_nonneg hy]
    exact min_le_right _ _
  have hmlim : Tendsto (fun n ↦ ∫ x, m n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence g
    · exact fun n ↦ (hmInt n).aestronglyMeasurable
    · exact hg
    · intro n
      filter_upwards [hf₀ n, hg₀] with x hx hy
      change ‖min (f n x) (g x)‖ ≤ g x
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hy)]
      exact min_le_right _ _
    · filter_upwards [h] with x hx
      simpa only [min_self] using hx.min (tendsto_const_nhds (x := g x))
  have he (n : ℕ) : (∫ x, |f n x - g x| ∂μ) =
      (∫ x, f n x ∂μ) + (∫ x, g x ∂μ) - 2 * (∫ x, m n x ∂μ) := by
    have hpoint (x : X) : |f n x - g x| = f n x + g x - 2 * m n x := by
      rcases le_total (f n x) (g x) with hx | hx
      · rw [abs_of_nonpos (sub_nonpos.mpr hx), show m n x = f n x from min_eq_left hx]
        ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hx), show m n x = g x from min_eq_right hx]
        ring
    simp_rw [hpoint]
    change (∫ x, (f n + g) x - 2 * m n x ∂μ) = _
    rw [integral_sub ((hf n).add hg) ((hmInt n).const_mul 2)]
    simp only [Pi.add_apply, integral_add (hf n) hg, integral_const_mul]
  have hh := (hm.add (tendsto_const_nhds (x := ∫ x, g x ∂μ))).sub (hmlim.const_mul 2)
  have hzero : (∫ x, g x ∂μ) + (∫ x, g x ∂μ) - 2 * (∫ x, g x ∂μ) = 0 := by ring
  rw [hzero] at hh
  exact hh.congr fun n ↦ (he n).symm

theorem tendsto_integral_mul_of_integral_abs_sub {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {g φ : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hφ : AEStronglyMeasurable φ μ) {B : ℝ} (hb : ∀ x, |φ x| ≤ B)
    (h : Tendsto (fun n ↦ ∫ x, |f n x - g x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, f n x * φ x ∂μ) atTop (𝓝 (∫ x, g x * φ x ∂μ)) := by
  have hb' : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B :=
    Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hb x
  have hI (n : ℕ) : Integrable (fun x ↦ |(f n x - g x) * φ x|) μ :=
    (((hf n).sub hg).mul_bdd hφ hb').abs
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim := h.const_mul B
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ dist_nonneg) ?_
  intro n
  have he : (∫ x, (f n x - g x) * φ x ∂μ) =
      (∫ x, f n x * φ x ∂μ) - ∫ x, g x * φ x ∂μ := by
    simp_rw [sub_mul]
    exact integral_sub ((hf n).mul_bdd hφ hb') (hg.mul_bdd hφ hb')
  change dist (∫ x, f n x * φ x ∂μ) (∫ x, g x * φ x ∂μ) ≤ B * ∫ x, |f n x - g x| ∂μ
  rw [Real.dist_eq, ← he]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  apply integral_mono (hI n) (((hf n).sub hg).abs.const_mul B)
  intro x
  change |(f n x - g x) * φ x| ≤ B * |f n x - g x|
  rw [abs_mul, mul_comm B]
  exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

end CarpetEnergy
