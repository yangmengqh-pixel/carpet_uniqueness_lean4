import EnergyRelativeGeneralizedContraction
import EnergyRelativeInvariance

/-!
# The energy-root seminorm of the renormalized graph limit
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

private theorem finitePowerSum_one (a : Fin 1 → ℝ) (ha : 0 ≤ a 0) (q : ℝ) (hq : 0 < q) :
    finitePowerSum q a = a 0 := by
  unfold finitePowerSum
  rw [Fin.sum_univ_one, Real.rpow_rpow_inv ha hq.ne']

set_option maxHeartbeats 1000000 in
theorem root_add_le_of_generalizedContraction
    {G : E.domain → ℝ} (hG : ∀ f, 0 ≤ G f)
    (h : E.HasFiniteGeneralizedPContraction G) (f g : E.domain) :
    G (f + g) ^ p⁻¹ ≤ G f ^ p⁻¹ + G g ^ p⁻¹ := by
  have hp := zero_lt_one.trans E.one_lt_p
  let T (u : Fin 2 → ℝ) (_ : Fin 1) := u 0 + u 1
  have hT (u v : Fin 2 → ℝ) :
      finitePowerSum p (fun i ↦ |T u i - T v i|) ≤
        finitePowerSum 1 (fun i ↦ |u i - v i|) := by
    rw [finitePowerSum_one _ (abs_nonneg _) p hp]
    unfold finitePowerSum
    simp only [Real.rpow_one, inv_one, Fin.sum_univ_two]
    change |u 0 + u 1 - (v 0 + v 1)| ≤ |u 0 - v 0| + |u 1 - v 1|
    rw [show u 0 + u 1 - (v 0 + v 1) = (u 0 - v 0) + (u 1 - v 1) by ring]
    exact abs_add_le _ _
  obtain ⟨L, hLip⟩ := exists_lipschitzWith_mixed_components one_pos hp T hT
  have h0 : ∀ i, T 0 i = 0 := fun _ ↦ add_zero _
  obtain ⟨D, hD⟩ := h 2 1 1 p one_pos E.one_lt_p.le le_rfl T hT hLip h0
  let u : Fin 2 → E.domain := ![f, g]
  have hu : E.domainMixedOperation D u 0 = f + g := by
    apply Subtype.ext
    apply Lp.ext
    have hh := ae_pointwiseLp T hLip h0 (fun j ↦ (u j : CarpetLp p)) 0
    have hfg := Lp.coeFn_add (f : CarpetLp p) (g : CarpetLp p)
    exact hh.trans hfg.symm
  have hle := hD u
  simp only [div_self hp.ne', one_div] at hle
  rw [finitePowerSum_one _ (hG _) 1 one_pos, hu] at hle
  unfold finitePowerSum at hle
  rw [Fin.sum_univ_two, inv_inv] at hle
  change G (f + g) ≤ (G f ^ p⁻¹ + G g ^ p⁻¹) ^ p at hle
  have hs : 0 ≤ G f ^ p⁻¹ + G g ^ p⁻¹ :=
    add_nonneg (Real.rpow_nonneg (hG f) _) (Real.rpow_nonneg (hG g) _)
  have ht := Real.rpow_le_rpow (hG _) hle (inv_nonneg.mpr hp.le)
  rw [Real.rpow_rpow_inv hs hp.ne'] at ht
  exact ht

/-- Positive p-homogeneity and the mixed contraction for addition
give the p-th root of the limiting energy as a seminorm. -/
noncomputable def relativeRootSeminorm (G : E.domain → ℝ)
    (hG : ∀ f, 0 ≤ G f) (hhom : ∀ a : ℝ, ∀ f, G (a • f) = |a| ^ p * G f)
    (h : E.HasFiniteGeneralizedPContraction G) : Seminorm ℝ E.domain :=
  Seminorm.of (fun f ↦ G f ^ p⁻¹) (E.root_add_le_of_generalizedContraction hG h) (by
    intro a f
    rw [hhom, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (hG _),
      Real.rpow_rpow_inv (abs_nonneg _) (zero_lt_one.trans E.one_lt_p).ne', Real.norm_eq_abs])

end CarpetEnergy.SelfSimilarPEnergy
