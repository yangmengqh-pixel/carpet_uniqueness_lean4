import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz extensions of smooth functions and their affine remainders
-/

open Filter Metric Set
open scoped NNReal

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- A C¹ real function restricted to a bounded ball admits a globally
Lipschitz extension. -/
theorem exists_lipschitz_extension_of_contDiff_closedBall
    (φ : X → ℝ) (hφ : ContDiff ℝ 1 φ) (R : ℝ) :
    ∃ b : ℝ≥0, 0 < b ∧ ∃ ψ : X → ℝ, LipschitzWith b ψ ∧ EqOn φ ψ (closedBall 0 R) := by
  have hs : IsCompact (closedBall (0 : X) R) := isCompact_closedBall _ _
  have hD : Continuous (fderiv ℝ φ) := (contDiff_one_iff_fderiv.mp hφ).2
  obtain ⟨M, hM⟩ := (hs.image hD.norm).bddAbove
  let b : ℝ≥0 := ⟨max M 0 + 1, by positivity⟩
  have hb : 0 < b := by exact_mod_cast (show (0 : ℝ) < max M 0 + 1 by positivity)
  have hLip : LipschitzOnWith b φ (closedBall 0 R) := by
    apply (convex_closedBall _ _).lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ)
    · exact fun x _ ↦ (contDiff_one_iff_fderiv.mp hφ).1 x
    · intro x hx
      have h := hM (mem_image_of_mem (fun x ↦ ‖fderiv ℝ φ x‖) hx)
      have hbound : ‖fderiv ℝ φ x‖ ≤ max M 0 + 1 :=
        h.trans ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one))
      exact_mod_cast hbound
  exact ⟨b, hb, hLip.extend_real⟩

set_option maxHeartbeats 1000000 in
/-- Uniform continuity of the derivative on a larger ball gives a
uniform Lipschitz constant for the affine remainder on sufficiently
small balls centered in the original ball. -/
theorem exists_uniform_lipschitz_extension_of_affine_remainder
    (φ : X → ℝ) (hφ : ContDiff ℝ 1 φ) (R : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    ∃ δ > (0 : ℝ), ∀ x ∈ closedBall 0 R, ∃ ψ : X → ℝ, LipschitzWith b ψ ∧
      EqOn (fun y ↦ φ y - fderiv ℝ φ x y) ψ (closedBall x δ) := by
  let K := closedBall (0 : X) (R + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hD : Continuous (fderiv ℝ φ) := (contDiff_one_iff_fderiv.mp hφ).2
  have hb' : 0 < (b : ℝ) := hb
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hD.continuousOn) (b : ℝ) hb'
  let δ := min 1 (r / 2)
  have hδ : 0 < δ := lt_min one_pos (half_pos hr)
  refine ⟨δ, hδ, fun x hx ↦ ?_⟩
  let F (y : X) := φ y - fderiv ℝ φ x y
  have hxK : x ∈ K := (closedBall_subset_closedBall (by linarith)) hx
  have hLip : LipschitzOnWith b F (closedBall x δ) := by
    apply (convex_closedBall _ _).lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
      (f' := fun y ↦ fderiv ℝ φ y - fderiv ℝ φ x)
    · intro y _
      exact (((contDiff_one_iff_fderiv.mp hφ).1 y).hasFDerivAt.sub
        (fderiv ℝ φ x).hasFDerivAt).hasFDerivWithinAt
    · intro y hy
      have hyK : y ∈ K := by
        change dist y 0 ≤ R + 1
        exact (dist_triangle y x 0).trans (by
          have hy' : dist y x ≤ 1 := hy.trans (min_le_left _ _)
          have hx' : dist x 0 ≤ R := hx
          linarith only [hy', hx'])
      have hyr : dist y x < r := hy.trans_lt
        ((min_le_right _ _).trans_lt (half_lt_self hr))
      have h := hmod y hyK x hxK hyr
      rw [dist_eq_norm] at h
      exact_mod_cast h.le
  exact hLip.extend_real

end CarpetEnergy
