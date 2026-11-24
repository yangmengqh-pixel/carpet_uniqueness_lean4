import EnergyRelativeSelfSimilarEnergy
import EnergyGlobalNormalization

/-!
# Lipschitz compositions of finite tuples in the continuous core
-/

open Filter Function MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 1300000 in
/-- A scalar map with an `ℓ^p` Lipschitz bound acts on a continuous
finite-energy tuple with the same energy-root bound. -/
theorem exists_core_comp_finite_lipschitz
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {m : ℕ} (u : Fin m → E.continuousCore) (φ : (Fin m → ℝ) → ℝ) {b : ℝ} (hb : 0 < b)
    (hφ : ∀ x y, |φ x - φ y| ≤ b * finitePowerSum p (fun j ↦ |x j - y j|)) :
    ∃ v : E.continuousCore, (∀ x, v.val x = φ (fun j ↦ (u j).val x)) ∧
      E.rootSeminorm (E.continuousCoreToDomain v) ≤
        b * finitePowerSum p (fun j ↦ E.rootSeminorm (E.continuousCoreToDomain (u j))) := by
  have hp := zero_lt_one.trans E.one_lt_p
  let T (x : Fin m → ℝ) (_ : Fin 1) := (φ x - φ 0) / b
  have hT (x y : Fin m → ℝ) :
      finitePowerSum p (fun i ↦ |T x i - T y i|) ≤
        finitePowerSum p (fun j ↦ |x j - y j|) := by
    unfold finitePowerSum
    rw [Fin.sum_univ_one, Real.rpow_rpow_inv (abs_nonneg _) hp.ne']
    change |(φ x - φ 0) / b - (φ y - φ 0) / b| ≤ _
    rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hb, div_le_iff₀ hb, mul_comm _ b]
    exact hφ x y
  obtain ⟨L, hLip⟩ := exists_lipschitzWith_mixed_components hp hp T hT
  have h0 : ∀ i, T 0 i = 0 := by intro i; simp only [T, sub_self, zero_div]
  obtain ⟨D, hD⟩ := hc m 1 p p hp le_rfl le_rfl T hT hLip h0
  let z := E.domainMixedOperation D (fun j ↦ E.continuousCoreToDomain (u j)) 0
  let ψ : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ T (fun j ↦ (u j).val x) 0,
      (hLip 0).continuous.comp (continuous_pi (fun j ↦ (u j).val.continuous))⟩
  have hψ : continuousLp p ψ = (z : CarpetLp p) := by
    apply Lp.ext
    have hae (j : Fin m) : ((E.continuousCoreToDomain (u j) : CarpetLp p) : CarpetPoints → ℝ) =ᵐ[carpetMeasure]
        (u j).val := continuousLp_ae_eq p (u j).val
    have hz := ae_pointwiseLp T hLip h0 (fun j ↦ (E.continuousCoreToDomain (u j) : CarpetLp p)) 0
    filter_upwards [(Filter.eventually_all.mpr hae), hz, continuousLp_ae_eq p ψ] with x hx hz hxψ
    have heq : (fun j ↦ (E.continuousCoreToDomain (u j) : CarpetLp p) x) =
        (fun j ↦ (u j).val x) := funext hx
    change (z : CarpetLp p) x = T (fun j ↦ (E.continuousCoreToDomain (u j) : CarpetLp p) x) 0 at hz
    rw [heq] at hz
    exact hxψ.trans hz.symm
  have hmem : continuousLp p ψ ∈ E.domain := hψ.symm ▸ z.property
  let q : E.continuousCore := ⟨ψ, hmem⟩
  have hq : E.continuousCoreToDomain q = z := Subtype.ext hψ
  let v : E.continuousCore := b • q + E.constCore (φ 0)
  refine ⟨v, ?_, ?_⟩
  · intro x
    change b * ((φ (fun j ↦ (u j).val x) - φ 0) / b) + φ 0 = _
    field_simp
    ring
  have he := hD (fun j ↦ E.continuousCoreToDomain (u j))
  simp only [div_self hp.ne', finitePowerSum, Real.rpow_one, inv_one, Fin.sum_univ_one] at he
  change (E.energy z : ℝ) ≤ ∑ j : Fin m, (E.energy (E.continuousCoreToDomain (u j)) : ℝ) at he
  have hpow (f : E.domain) : (E.rootSeminorm f) ^ p = (E.energy f : ℝ) := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'
  have hz : E.rootSeminorm z ≤
      finitePowerSum p (fun j ↦ E.rootSeminorm (E.continuousCoreToDomain (u j))) := by
    unfold finitePowerSum
    simp only [hpow, E.rootSeminorm_apply z]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) he (inv_nonneg.mpr hp.le)
  have hv : E.rootSeminorm (E.continuousCoreToDomain v) = b * E.rootSeminorm z := by
    dsimp only [v]
    rw [E.rootSeminorm_apply, map_add, map_smul, E.continuousCoreToDomain_constCore,
      E.add_constant, ← E.rootSeminorm_apply, hq,
      map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hb]
  rw [hv]
  exact mul_le_mul_of_nonneg_left hz hb.le

/-- A Lipschitz bound for the coordinate supremum norm also gives
the same energy-root estimate. -/
theorem exists_core_comp_lipschitzWith
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {m : ℕ} (u : Fin m → E.continuousCore) (φ : (Fin m → ℝ) → ℝ) {b : ℝ≥0}
    (hb : 0 < b) (hφ : LipschitzWith b φ) :
    ∃ v : E.continuousCore, (∀ x, v.val x = φ (fun j ↦ (u j).val x)) ∧
      E.rootSeminorm (E.continuousCoreToDomain v) ≤
        (b : ℝ) * finitePowerSum p (fun j ↦ E.rootSeminorm (E.continuousCoreToDomain (u j))) := by
  classical
  have hp := zero_lt_one.trans E.one_lt_p
  apply E.exists_core_comp_finite_lipschitz hc u φ (show 0 < (b : ℝ) from hb)
  intro x y
  have h := hφ.dist_le_mul x y
  rw [Real.dist_eq, dist_eq_norm] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ b.coe_nonneg)
  apply (pi_norm_le_iff_of_nonneg (finitePowerSum_nonneg p (fun _ ↦ abs_nonneg _))).mpr
  intro i
  change ‖x i - y i‖ ≤ _
  rw [Real.norm_eq_abs]
  unfold finitePowerSum
  rw [← Real.rpow_rpow_inv (abs_nonneg (x i - y i)) hp.ne']
  exact Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _)
    (Finset.single_le_sum (f := fun j ↦ |x j - y j| ^ p)
      (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i))
    (inv_nonneg.mpr hp.le)

end CarpetEnergy.SelfSimilarPEnergy
