import EnergyLevelComponentRemoval
import EnergyApproximateMinimum
import EnergyZeroExteriorNorm

/-!
# Level crossings for continuous approximations to constrained minimizers
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem integral_posPart_tendsto [Fact (1 ≤ ENNReal.ofReal p)]
    (f : E.domain) (u : ℕ → E.continuousCore) (W : Set CarpetPoints) (t : ℝ)
    (hu : Tendsto (fun n ↦ E.toGraph (E.continuousCoreToDomain (u n))) atTop
      (𝓝 (E.toGraph f))) :
    Tendsto (fun n ↦ ∫ x in W, max ((u n).val x - t) 0 ∂carpetMeasure) atTop
      (𝓝 (∫ x in W, max ((f : CarpetLp p) x - t) 0 ∂carpetMeasure)) := by
  let k := continuousLp p (ContinuousMap.const CarpetPoints t)
  let F (g : CarpetLp p) := lpSetIntegral W (Lp.posPart (g - k))
  have hF : Continuous F :=
    (lpSetIntegral W).continuous.comp (Lp.continuous_posPart.comp (continuous_id.sub continuous_const))
  have hcoe (g : CarpetLp p) : F g = ∫ x in W, max (g x - t) 0 ∂carpetMeasure := by
    apply integral_congr_ae
    apply ae_restrict_of_ae
    filter_upwards [Lp.coeFn_posPart (g - k), Lp.coeFn_sub g k,
      continuousLp_ae_eq p (ContinuousMap.const CarpetPoints t)] with x hpos hsub hk
    rw [hpos, hsub, Pi.sub_apply, show k x = t from hk]
  have hh := (hF.tendsto (f : CarpetLp p)).comp
    ((E.graphInclusion.continuous.tendsto (E.toGraph f)).comp hu)
  change Tendsto (fun n ↦ F (E.continuousCoreToDomain (u n) : CarpetLp p)) atTop
    (𝓝 (F (f : CarpetLp p))) at hh
  simp only [hcoe] at hh
  refine hh.congr fun n ↦ integral_congr_ae ?_
  apply ae_restrict_of_ae
  filter_upwards [continuousLp_ae_eq p (u n).val] with x hx
  change max (continuousLp p (u n).val x - t) 0 = _
  rw [hx]

set_option maxHeartbeats 4600000 in
/-- If a harmonic profile has positive excess on an interior set, then
eventually one superlevel component of each continuous graph approximant
meets both that set and the prescribed exterior. -/
theorem eventually_exists_connected_superlevel_crossing [Fact (1 ≤ ENNReal.ofReal p)]
    {U W : Set CarpetPoints} (hUm : MeasurableSet U) (hWm : MeasurableSet W)
    (hU : carpetMeasure Uᶜ ≠ 0)
    (f : E.domain) (hf : E.MinimizesWithExterior Uᶜ f)
    (u : ℕ → E.continuousCore) (t : ℝ)
    (hu : Tendsto (fun n ↦ E.toGraph (E.continuousCoreToDomain (u n))) atTop
      (𝓝 (E.toGraph f)))
    (hpos : 0 < ∫ x in W, max ((f : CarpetLp p) x - t) 0 ∂carpetMeasure) :
    ∀ᶠ n in atTop, ∃ S : Set CarpetPoints, IsConnected S ∧
      S ⊆ {x | t < (u n).val x} ∧ (S ∩ W).Nonempty ∧ (S \ U).Nonempty := by
  let d (n : ℕ) := E.continuousCoreToDomain (u n)
  let δ (n : ℕ) := ‖E.toGraph (d n) - E.toGraph f‖
  let B := E.rootSeminorm f + 1
  let K := 2 * p * (2 * B + 1) ^ (p - 1)
  let I := ∫ x in W, max ((f : CarpetLp p) x - t) 0 ∂carpetMeasure
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hu
  have hbound (n : ℕ) : E.rootSeminorm (d n - f) ≤ δ n := by
    change _ ≤ ‖E.toGraph (d n - f)‖
    rw [E.norm_toGraph]
    exact E.rootSeminorm_le_graphSeminorm _
  have hfB : E.rootSeminorm f ≤ B := le_add_of_nonneg_right zero_le_one
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨C, hC, hnorm⟩ := E.exists_norm_le_root_of_ae_zero_on hU
  have hsmall : Tendsto (fun n ↦ C * (K * δ n) ^ p⁻¹) atTop (𝓝 0) := by
    have hmul : Tendsto (fun n ↦ K * δ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hδ.const_mul K
    have hpow := hmul.rpow_const (p := p⁻¹) (Or.inr (inv_nonneg.mpr hp.le))
    simpa only [Real.zero_rpow (inv_ne_zero hp.ne'), mul_zero] using hpow.const_mul C
  have hlim := E.integral_posPart_tendsto f u W t hu
  filter_upwards [hδ.eventually_lt_const zero_lt_one,
    hsmall.eventually_lt_const (show 0 < I / 2 from half_pos hpos),
    hlim.eventually_const_lt (show I / 2 < I from half_lt_self hpos)] with n hδn hsmalln hIn
  by_contra hnone
  let G := {x | t < (u n).val x}
  let S := W ∩ G
  let V := ⋃ x : S, connectedComponentIn G x.val
  have hV : V ⊆ U := by
    intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp hy
    by_contra hyU
    have hxC := mem_connectedComponentIn x.property.2
    exact hnone ⟨_, isConnected_connectedComponentIn_iff.mpr x.property.2,
      connectedComponentIn_subset _ _, ⟨x.val, hxC, x.property.1⟩, ⟨y, hx, hyU⟩⟩
  obtain ⟨v, hv1, hv0, hsplit⟩ := E.exists_superlevel_component_excess (u n) t S
  let w := E.continuousCoreToDomain v
  have hzero : ∀ᵐ x ∂carpetMeasure.restrict Uᶜ, (w : CarpetLp p) x = 0 := by
    filter_upwards [ae_restrict_of_ae (continuousLp_ae_eq p v.val), ae_restrict_mem hUm.compl] with x hx hxU
    exact hx.trans (hv0 x (fun hxV ↦ hxU (hV hxV)))
  have hsplit' : (E.energy (d n - w) : ℝ) + (E.energy w : ℝ) = (E.energy (d n) : ℝ) := by
    simpa only [d, w, map_sub] using hsplit
  have hdB : E.rootSeminorm (d n) ≤ B := by
    have h := map_add_le_add E.rootSeminorm (d n - f) f
    rw [sub_add_cancel] at h
    exact h.trans (by linarith [hbound n])
  have hwB : E.rootSeminorm w ≤ B := by
    refine le_trans ?_ hdB
    rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _)
      (by linarith only [hsplit', NNReal.coe_nonneg (E.energy (d n - w))])
      (inv_nonneg.mpr hp.le)
  have hneg : ∀ᵐ x ∂carpetMeasure.restrict Uᶜ, ((-w : E.domain) : CarpetLp p) x = 0 := by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_neg (w : CarpetLp p)), hzero] with x hx hw
    exact hx.trans (by simp only [Pi.neg_apply, hw, neg_zero])
  have hdef := E.energy_le_perturbation_add_defect f (d n) (-w) hf hneg hfB hdB
    (by rw [map_neg_eq_map]; exact hwB) (hbound n) hδn.le
  rw [← sub_eq_add_neg] at hdef
  have hE : (E.energy w : ℝ) ≤ K * δ n := by
    dsimp only [K]
    calc
      _ ≤ 2 * p * δ n * (2 * B + 1) ^ (p - 1) := by linarith only [hdef, hsplit']
      _ = _ := by ring
  have hval (x : CarpetPoints) (hx : x ∈ W) : v.val x = max ((u n).val x - t) 0 := by
    by_cases hxG : x ∈ G
    · have hxV : x ∈ V := mem_iUnion.mpr ⟨⟨x, hx, hxG⟩, mem_connectedComponentIn hxG⟩
      exact (hv1 x hxV).trans (max_eq_left (sub_nonneg.mpr hxG.le)).symm
    · have hxV : x ∉ V := fun hxV ↦ hxG ((iUnion_subset fun _ ↦ connectedComponentIn_subset _ _) hxV)
      exact (hv0 x hxV).trans (max_eq_right (sub_nonpos.mpr (le_of_not_gt hxG))).symm
  have hIeq : ∫ x in W, max ((u n).val x - t) 0 ∂carpetMeasure =
      ∫ x in W, (w : CarpetLp p) x ∂carpetMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (continuousLp_ae_eq p v.val),
      ae_restrict_mem hWm] with x hx hxW
    exact (hx.trans (hval x hxW)).symm
  have hIle : ∫ x in W, (w : CarpetLp p) x ∂carpetMeasure ≤ C * (K * δ n) ^ p⁻¹ := by
    calc
      _ ≤ ‖∫ x in W, (w : CarpetLp p) x ∂carpetMeasure‖ := le_abs_self _
      _ ≤ ‖(w : CarpetLp p)‖ := norm_setIntegral_le W _
      _ ≤ C * E.rootSeminorm w := hnorm w hzero
      _ ≤ _ := by
        rw [E.rootSeminorm_apply]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (NNReal.coe_nonneg _) hE (inv_nonneg.mpr hp.le)) hC.le
  linarith only [hIeq, hIle, hIn, hsmalln]

end CarpetEnergy.SelfSimilarPEnergy
