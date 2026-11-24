import EnergyRelativeGraphSeminorm
import Mathlib.Topology.UniformSpace.Equiv

/-!
# Completeness for the comparable graph seminorm
-/

open Function
open scoped ENNReal NNReal Uniformity

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem completeSpace_of_graphSeminorm_comparison (T : Seminorm ℝ E.domain)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ f, a * E.graphSeminorm f ≤ T f ∧ T f ≤ b * E.graphSeminorm f) :
    letI := T.toAddGroupSeminorm.toSeminormedAddCommGroup
    CompleteSpace E.domain := by
  let : SeminormedAddCommGroup E.domain := T.toAddGroupSeminorm.toSeminormedAddCommGroup
  let a' : ℝ≥0 := ⟨a⁻¹, inv_nonneg.mpr ha.le⟩
  let b' : ℝ≥0 := ⟨b, hb.le⟩
  have hTo : LipschitzWith a' E.toGraph := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [dist_eq_norm]
    change E.graphSeminorm (x - y) ≤ a⁻¹ * T (x - y)
    exact (le_inv_mul_iff₀ ha).mpr (h (x - y)).1
  have hFrom : LipschitzWith b' E.graphToDomain := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [dist_eq_norm]
    exact (h (E.graphToDomain x - E.graphToDomain y)).2
  let e : E.domain ≃ᵤ E.GraphDomain :=
    { toFun := E.toGraph
      invFun := E.graphToDomain
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      uniformContinuous_toFun := hTo.uniformContinuous
      uniformContinuous_invFun := hFrom.uniformContinuous }
  exact e.completeSpace_iff.mpr inferInstance

theorem regular_graph_of_graphSeminorm_comparison (T : Seminorm ℝ E.domain)
    {b : ℝ} (hb : 0 < b) (h : ∀ f, T f ≤ b * E.graphSeminorm f)
    (f : E.domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ (v : C(CarpetPoints, ℝ)) (hv : continuousLp p v ∈ E.domain),
      T (⟨continuousLp p v, hv⟩ - f) < ε := by
  obtain ⟨v, hv, happ⟩ := E.regular_graph f (ε / b) (div_pos hε hb)
  exact ⟨v, hv, (h _).trans_lt (by
    rw [mul_comm]
    exact (lt_div_iff₀ hb).mp happ)⟩

end CarpetEnergy.SelfSimilarPEnergy
