import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# A smooth ball cutoff with an inverse-radius derivative bound
-/

open Function Metric Set

namespace CarpetEnergy

theorem exists_planar_ball_cutoffs :
    ∃ D > (0 : ℝ), ∀ (z : Fin 2 → ℝ) (r : ℝ), 0 < r →
      ∃ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ 1 φ ∧
        (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ ball z r, φ x = 1) ∧
        (∀ x ∉ ball z (3 * r), φ x = 0 ∧ fderiv ℝ φ x = 0) ∧
        ∀ x i, |fderiv ℝ φ x (Pi.single i 1)| ≤ D / r := by
  let V := Fin 2 → ℝ
  let ψ : ContDiffBump (0 : V) := ⟨1, 2, by norm_num, by norm_num⟩
  have hDiff : ContDiff ℝ 1 (ψ : V → ℝ) := ψ.contDiff
  have hcont : Continuous (fderiv ℝ (ψ : V → ℝ)) := hDiff.continuous_fderiv (by norm_num)
  obtain ⟨y, _, hy⟩ := (isCompact_closedBall (0 : V) 2).exists_isMaxOn
    ⟨0, mem_closedBall_self (by norm_num)⟩ hcont.norm.continuousOn
  let D := max ‖fderiv ℝ (ψ : V → ℝ) y‖ 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hb (x : V) : ‖fderiv ℝ (ψ : V → ℝ) x‖ ≤ D := by
    by_cases hx : x ∈ closedBall (0 : V) 2
    · exact (hy hx).trans (le_max_left _ _)
    · rw [fderiv_of_notMem_tsupport ℝ (show x ∉ tsupport (ψ : V → ℝ) from by rwa [ψ.tsupport_eq])]
      exact norm_zero.trans_le hD.le
  refine ⟨D, hD, fun z r hr ↦ ?_⟩
  let T : V → V := fun x ↦ r⁻¹ • (x - z)
  let φ : V → ℝ := ψ ∘ T
  have hT : ContDiff ℝ 1 T := (contDiff_id.sub contDiff_const).const_smul _
  have hf : ContDiff ℝ 1 φ := hDiff.comp hT
  have hnorm (x : V) : ‖T x‖ = dist x z / r := by
    rw [dist_eq_norm, div_eq_inv_mul]
    dsimp [T]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have hder (x : V) : fderiv ℝ φ x = (fderiv ℝ (ψ : V → ℝ) (T x)).comp
      (r⁻¹ • ContinuousLinearMap.id ℝ V) := by
    have hdt : HasFDerivAt T (r⁻¹ • ContinuousLinearMap.id ℝ V) x := by
      exact ((hasFDerivAt_id x).sub_const z).const_smul r⁻¹
    exact (((hDiff.differentiable (by norm_num) (T x)).hasFDerivAt).comp x hdt).fderiv
  refine ⟨φ, hf, fun _ ↦ ⟨ψ.nonneg, ψ.le_one⟩, ?_, ?_, ?_⟩
  · intro x hx
    apply ψ.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, hnorm]
    exact (div_le_one hr).mpr (mem_ball.mp hx).le
  · intro x hx
    have hout : T x ∉ closedBall (0 : V) 2 := by
      rw [mem_closedBall, dist_zero_right, hnorm, not_le]
      apply (lt_div_iff₀ hr).mpr
      exact (mul_lt_mul_of_pos_right (by norm_num : (2 : ℝ) < 3) hr).trans_le (not_lt.mp hx)
    constructor
    · exact notMem_support.mp (fun hs ↦ hout (ball_subset_closedBall (ψ.support_eq ▸ hs)))
    · rw [hder, fderiv_of_notMem_tsupport ℝ (show T x ∉ tsupport (ψ : V → ℝ) from by rwa [ψ.tsupport_eq])]
      exact ContinuousLinearMap.zero_comp _
  · intro x i
    let e : V := Pi.single i 1
    have he : ‖e‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro j
      by_cases hij : j = i
      · subst j
        simp [e]
      · simp [e, Pi.single_eq_of_ne hij]
    rw [hder, ← Real.norm_eq_abs]
    change ‖fderiv ℝ (ψ : V → ℝ) (T x) (r⁻¹ • e)‖ ≤ D / r
    refine ((fderiv ℝ (ψ : V → ℝ) (T x)).le_opNorm _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), div_eq_mul_inv]
    simpa only [mul_one] using
      mul_le_mul (hb (T x)) (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hr.le))
        (by positivity) hD.le

end CarpetEnergy
