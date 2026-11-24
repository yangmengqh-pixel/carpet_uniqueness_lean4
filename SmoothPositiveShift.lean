import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Extending a positive shift smoothly past the nonnegative axis
-/

open Filter
open scoped Topology

namespace CarpetEnergy

theorem exists_smooth_positive_shift {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ → ℝ, ContDiff ℝ 1 S ∧ (∀ t, 0 < S t) ∧
      ∀ t ≥ 0, S t = t + ε ∧ HasDerivAt S 1 t := by
  let T (t : ℝ) := 4 * t / ε + 2
  let S (t : ℝ) := ε / 2 + Real.smoothTransition (T t) * (t + ε / 2)
  have hT : ContDiff ℝ 1 T :=
    ((contDiff_const.mul contDiff_id).div_const ε).add contDiff_const
  have hS : ContDiff ℝ 1 S :=
    contDiff_const.add ((Real.smoothTransition.contDiff.comp hT).mul
      (contDiff_id.add contDiff_const))
  refine ⟨S, hS, ?_, ?_⟩
  · intro t
    by_cases ht : t + ε / 2 ≤ 0
    · have h0 : T t ≤ 0 := by
        dsimp only [T]
        have hh : 4 * t / ε ≤ -2 := (div_le_iff₀ hε).mpr (by linarith)
        linarith
      dsimp only [S]
      rw [Real.smoothTransition.zero_of_nonpos h0, zero_mul, add_zero]
      exact half_pos hε
    · exact add_pos_of_pos_of_nonneg (half_pos hε)
        (mul_nonneg (Real.smoothTransition.nonneg _) (le_of_not_ge ht))
  · intro t ht
    have hLt : 1 < T t := by
      dsimp only [T]
      have hh : 0 ≤ 4 * t / ε := div_nonneg (mul_nonneg (by norm_num) ht) hε.le
      linarith
    have hEq (s : ℝ) (hs : 1 ≤ T s) : S s = s + ε := by
      dsimp only [S]
      rw [Real.smoothTransition.one_of_one_le hs, one_mul]
      ring
    refine ⟨hEq t hLt.le, ?_⟩
    have he : S =ᶠ[𝓝 t] fun s ↦ s + ε :=
      ((hT.continuous.tendsto t).eventually (lt_mem_nhds hLt)).mono (fun s hs ↦ hEq s hs.le)
    exact ((hasDerivAt_id t).add_const ε).congr_of_eventuallyEq he

end CarpetEnergy
