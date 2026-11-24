import EnergyRelativeCompleteness
import EnergyRelativeUniformConvex
import EnergyRelativeSmoothCore
import EnergyQuasiUniqueness

/-!
# A smooth Definition 2.1 energy from the discrete graph construction

The construction uses the scale and domain of a given self-similar
energy. The comparison bounds transfer graph completeness and regularity.
The scalar midpoint inequality gives uniform convexity for the constructed
graph norm itself.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The p-energy has a linear first variation at every energy-domain
function. The derivative is divided by p in the normalization. -/
def HasLinearFirstVariations : Prop :=
  ∀ f : E.domain, ∃ L : E.domain →ₗ[ℝ] ℝ, ∀ g : E.domain,
    HasDerivAt (fun t : ℝ ↦ (E.energy (f + t • g) : ℝ)) (p * L g) 0

private theorem unitContraction_of_generalized
    {G : E.domain → ℝ} (hG : ∀ f, 0 ≤ G f) (h : E.HasFiniteGeneralizedPContraction G)
    (f : E.domain) :
    ∃ g : E.domain, ((g : CarpetLp p) =ᵐ[carpetMeasure]
      fun x ↦ min (max ((f : CarpetLp p) x) 0) 1) ∧ G g ≤ G f := by
  let φ (x : ℝ) := min (max x 0) 1
  have hφ : LipschitzWith 1 φ := (LipschitzWith.id.max_const 0).min_const 1
  let T (u : Fin 1 → ℝ) (_ : Fin 1) := φ (u 0)
  have hp := zero_lt_one.trans E.one_lt_p
  have hone (q : ℝ) (hq : 0 < q) (a : Fin 1 → ℝ) (ha : 0 ≤ a 0) :
      finitePowerSum q a = a 0 := by
    unfold finitePowerSum
    rw [Fin.sum_univ_one, Real.rpow_rpow_inv ha hq.ne']
  have ht (u v : Fin 1 → ℝ) :
      finitePowerSum p (fun i ↦ |T u i - T v i|) ≤
        finitePowerSum p (fun i ↦ |u i - v i|) := by
    rw [hone p hp _ (abs_nonneg _), hone p hp _ (abs_nonneg _)]
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hφ.dist_le_mul (u 0) (v 0)
  obtain ⟨L, hLip⟩ := exists_lipschitzWith_mixed_components hp hp T ht
  have h0 : ∀ i, T 0 i = 0 := by intro i; norm_num [T, φ]
  obtain ⟨D, hD⟩ := h 1 1 p p hp le_rfl le_rfl T ht hLip h0
  let u : Fin 1 → E.domain := fun _ ↦ f
  let g := E.domainMixedOperation D u 0
  have he := ae_pointwiseLp T hLip h0 (fun i ↦ (u i : CarpetLp p)) 0
  have hle := hD u
  simp only [div_self hp.ne'] at hle
  rw [hone 1 one_pos _ (hG _), hone 1 one_pos _ (hG _)] at hle
  exact ⟨g, he, hle⟩

set_option maxHeartbeats 1500000 in
/-- Starting from any Definition 2.1 energy, the rescaled discrete
graph energies yield a Definition 2.1 energy with generalized
p-contraction and linear first variations. -/
theorem exists_selfSimilarPEnergy_with_uniform_first_variations :
    ∃ D : SelfSimilarPEnergy p, D.domain = E.domain ∧ D.scalingFactor = E.scalingFactor ∧
      D.HasFiniteGeneralizedPContraction (fun f ↦ (D.energy f : ℝ)) ∧
      D.HasInfinityGeneralizedPContraction (fun f ↦ (D.energy f : ℝ)) ∧
      D.HasLinearFirstVariations ∧ HasUniformSymmetricIncrement (fun f ↦ (D.energy f : ℝ)) := by
  have hp := zero_lt_one.trans E.one_lt_p
  obtain ⟨j, F, l, G, A, hA, B, hB, hj, hF, hl₀, _, hcomp, hlim, he⟩ :=
    E.exists_selfSimilarized_discreteLimit
  let : l.NeBot := hl₀
  have hG (f : E.domain) : 0 ≤ G f :=
    (mul_nonneg hA.le (NNReal.coe_nonneg _)).trans (hcomp f).1
  obtain ⟨hhom, hconst, hsym⟩ := E.renormalizedGammaLimit_invariance hF hlim
  have hgcp := E.renormalizedGammaLimit_hasFiniteGeneralizedPContraction hj hF hlim
  let S := E.relativeRootSeminorm G hG hhom hgcp
  have hS (f : E.domain) : G f = S f ^ p := by
    change G f = (G f ^ p⁻¹) ^ p
    exact (Real.rpow_inv_rpow (hG f) hp.ne').symm
  let T := E.relativeGraphSeminorm S
  obtain ⟨a, ha, b, hb, hT⟩ := E.exists_relativeGraphSeminorm_comparison G S hS hA hcomp
  let energy (f : E.domain) : ℝ≥0 := ⟨G f, hG f⟩
  have hz (f : E.domain) : energy f = 0 ↔ ∃ a : ℝ, (f : CarpetLp p) = constantLp p a := by
    rw [← E.zero_iff_constant]
    constructor
    · intro h
      apply NNReal.eq
      have h0 : G f = 0 := congrArg NNReal.toReal h
      have he := (hcomp f).1
      rw [h0, ← mul_zero A] at he
      exact le_antisymm (le_of_mul_le_mul_left he hA) (NNReal.coe_nonneg _)
    · intro h
      apply NNReal.eq
      have he := (hcomp f).2
      rw [h, NNReal.coe_zero, mul_zero] at he
      exact le_antisymm he (hG f)
  let D : SelfSimilarPEnergy p :=
    { one_lt_p := E.one_lt_p
      domain := E.domain
      energy := energy
      constant_mem := E.constant_mem
      zero_iff_constant := hz
      add_constant := fun f a ↦ NNReal.eq (hconst a f)
      smul_energy := hhom
      rootSeminorm := S
      rootSeminorm_apply := fun _ ↦ rfl
      graphSeminorm := T
      graphSeminorm_apply := fun f ↦ by
        change T f = (G f + ‖(f : CarpetLp p)‖ ^ p) ^ p⁻¹
        rw [E.relativeGraphSeminorm_apply, hS]
      graph_complete := E.completeSpace_of_graphSeminorm_comparison T ha hb hT
      graph_uniformConvex := E.renormalizedGammaLimit_graph_uniformConvex hj hF hlim S hS T rfl
      regular_sup := E.regular_sup
      regular_graph := E.regular_graph_of_graphSeminorm_comparison T hb (fun f ↦ (hT f).2)
      symmetry := fun σ f ↦ ⟨E.pullbackSymmetry σ f, symmetryPullback_isLpPullback (p := p) σ (f : CarpetLp p), NNReal.eq (hsym σ f)⟩
      selfSimilar := ⟨E.scalingFactor, E.isScalingFactor_scalingFactor.1, fun f ↦
        ⟨fun i ↦ E.pullback i f, fun i ↦ cellPullback_isLpPullback (p := p) i (f : CarpetLp p), he f⟩⟩
      continuous_gluing := E.continuous_gluing
      unit_contractivity := fun f ↦ by
        obtain ⟨g, hg, hle⟩ := E.unitContraction_of_generalized hG hgcp f
        exact ⟨g, hg, NNReal.coe_le_coe.mp hle⟩ }
  refine ⟨D, rfl, (E.scalingFactor_eq D).symm, hgcp, hgcp.infinity E hG, ?_⟩
  let pull (i : Fin 8) : E.domain →ₗ[ℝ] E.domain :=
    { toFun := E.pullback i
      map_add' := fun f g ↦ E.pullbackWord_add [i] f g
      map_smul' := fun a f ↦ E.pullbackWord_smul [i] a f }
  have hd := HasUniformSymmetricIncrement.of_renormalizationMean_limit
    E.isScalingFactor_scalingFactor.1.le pull (E.gammaLimit_toReal_hasUniformSymmetricIncrement hj hF) hlim
  have hpow : HasUniformSymmetricIncrement (fun f : E.domain ↦ S f ^ p) := by
    rw [show (fun f : E.domain ↦ S f ^ p) = G from (funext hS).symm]
    exact hd
  refine ⟨?_, hd⟩
  intro f
  change ∃ L : E.domain →ₗ[ℝ] ℝ, ∀ g : E.domain,
    HasDerivAt (fun t : ℝ ↦ G (f + t • g)) (p * L g) 0
  simpa only [hS] using exists_linear_first_variation_of_uniformSymmetricIncrement S E.one_lt_p hpow f

/-- The reference energy has linear first variations and both forms of
generalized contraction. -/
theorem exists_selfSimilarPEnergy_with_first_variations :
    ∃ D : SelfSimilarPEnergy p, D.domain = E.domain ∧ D.scalingFactor = E.scalingFactor ∧
      D.HasFiniteGeneralizedPContraction (fun f ↦ (D.energy f : ℝ)) ∧
      D.HasInfinityGeneralizedPContraction (fun f ↦ (D.energy f : ℝ)) ∧
      D.HasLinearFirstVariations := by
  obtain ⟨D, hD, hρ, hfin, hInf, hvar, _⟩ := E.exists_selfSimilarPEnergy_with_uniform_first_variations
  exact ⟨D, hD, hρ, hfin, hInf, hvar⟩

end CarpetEnergy.SelfSimilarPEnergy
