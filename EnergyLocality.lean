import EnergySeminorm
import EnergyContraction
import EnergyApproximation

/-!
# Locality of the energy measures

Self-similarity gives weak locality on open sets. The setwise seminorm then
identifies the masses of two functions whenever their difference has zero
energy measure on the set under consideration.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem energyMeasure_eq_zero_of_ae_constant_on_open'
    (f : E.domain) {U A : Set CarpetPoints} (hU : IsOpen U) (hA : IsCompact A)
    (hAU : A ⊆ U) {c : ℝ}
    (hconst : (f : CarpetLp p) =ᵐ[carpetMeasure.restrict U] fun _ ↦ c) :
    E.energyMeasure f A = 0 := by
  classical
  obtain ⟨ε, hε, hthick⟩ := hA.exists_thickening_subset_open hU hAU
  obtain ⟨n, hn⟩ := (tendsto_wordMap_radius.eventually_lt_const hε).exists
  rw [E.energyMeasure_eq_sum_words n, Measure.sum_apply _ hA.isClosed.measurableSet, tsum_fintype]
  apply Finset.sum_eq_zero
  intro w _
  let W := wordMap (List.ofFn w)
  have hW := (measurableEmbedding_wordMap (List.ofFn w)).measurable
  rw [smul_apply, smul_eq_mul, Measure.map_apply hW hA.isClosed.measurableSet]
  by_cases h : (A ∩ range W).Nonempty
  · obtain ⟨x, hxA, hxW⟩ := h
    have himg : range W ⊆ U := by
      intro y hy
      exact hthick (mem_thickening_iff.mpr ⟨x, hxA, (wordMap_dist_le n w hy hxW).trans_lt hn⟩)
    have hlocal : ∀ᵐ x ∂carpetMeasure, x ∈ U → (f : CarpetLp p) x = c :=
      ae_imp_of_ae_restrict hconst
    have hpull : (E.pullbackWord (List.ofFn w) f : CarpetLp p) = constantLp p c := by
      apply Lp.ext
      filter_upwards [E.pullbackWord_isLpPullback (List.ofFn w) f,
        (quasiMeasurePreserving_wordMap (List.ofFn w)).ae hlocal,
        Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c] with y h₁ h₂ h₃
      exact h₁.trans ((h₂ (himg (mem_range_self y))).trans h₃.symm)
    have hz : E.energy (E.pullbackWord (List.ofFn w) f) = 0 :=
      (E.zero_iff_constant _).mpr ⟨c, hpull⟩
    have hzmeasure : E.energyMeasure (E.pullbackWord (List.ofFn w) f) = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [E.energyMeasure_univ, hz, ENNReal.coe_zero]
    rw [hzmeasure, zero_apply, mul_zero]
  · have hempty : W ⁻¹' A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨W x, hx, mem_range_self x⟩
    change _ * E.energyMeasure (E.pullbackWord (List.ofFn w) f) (W ⁻¹' A) = 0
    rw [hempty, measure_empty, mul_zero]

/-- The energy measure vanishes on any open set where the function is a.e. constant. -/
theorem energyMeasure_eq_zero_of_ae_constant_on_open
    (f : E.domain) {U : Set CarpetPoints} (hU : IsOpen U) {c : ℝ}
    (hconst : (f : CarpetLp p) =ᵐ[carpetMeasure.restrict U] fun _ ↦ c) :
    E.energyMeasure f U = 0 := by
  rw [hU.measurableSet.measure_eq_iSup_isCompact (E.energyMeasure f)]
  apply le_antisymm _ bot_le
  refine iSup_le fun A ↦ iSup_le fun hAU ↦ iSup_le fun hA ↦ ?_
  exact (E.energyMeasure_eq_zero_of_ae_constant_on_open' f hU hA hAU hconst).le

/-- Zero mass of the difference on a Borel set implies equality of the two masses there. -/
theorem energyMeasure_apply_eq_of_sub_null
    {A : Set CarpetPoints} (hA : MeasurableSet A) (f g : E.domain)
    (h : E.energyMeasure (f - g) A = 0) :
    E.energyMeasure f A = E.energyMeasure g A := by
  let S := E.energyMeasureSeminorm A hA
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hz : S (f - g) = 0 := by
    change ((E.energyMeasure (f - g)).real A) ^ p⁻¹ = 0
    rw [Measure.real, h, ENNReal.toReal_zero, Real.zero_rpow (inv_ne_zero hp.ne')]
  have h₁ := map_add_le_add S (f - g) g
  rw [sub_add_cancel, hz, zero_add] at h₁
  have h₂ := map_add_le_add S (g - f) f
  rw [sub_add_cancel, ← neg_sub f g, map_neg_eq_map, hz, zero_add] at h₂
  have heq : S f = S g := le_antisymm h₁ h₂
  have hmass : (E.energyMeasure f).real A = (E.energyMeasure g).real A :=
    (Real.rpow_left_inj ENNReal.toReal_nonneg ENNReal.toReal_nonneg (inv_ne_zero hp.ne')).mp heq
  have h' := congrArg ENNReal.ofReal hmass
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h'

/-- Weak locality of the energy measure on an open set. -/
theorem energyMeasure_apply_eq_of_sub_constant_on_open
    {U : Set CarpetPoints} (hU : IsOpen U) (f g : E.domain) {c : ℝ}
    (h : ((f - g : E.domain) : CarpetLp p) =ᵐ[carpetMeasure.restrict U] fun _ ↦ c) :
    E.energyMeasure f U = E.energyMeasure g U :=
  E.energyMeasure_apply_eq_of_sub_null hU.measurableSet f g
    (E.energyMeasure_eq_zero_of_ae_constant_on_open (f - g) hU h)

/-- The energy measure of a continuous domain function vanishes on each of
its level sets, as in (3.4). -/
theorem energyMeasure_levelSet_eq_zero (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) (a : ℝ) :
    E.energyMeasure ⟨continuousLp p u, hu⟩ {x | u x = a} = 0 := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let A : Set CarpetPoints := {x | u x = a}
  have hA : MeasurableSet A := measurableSet_eq_fun u.continuous.measurable measurable_const
  let S := E.energyMeasureSeminorm A hA
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  let cut (n : ℕ) := E.shiftedTruncation (a - ε n) (2 * ε n) f
  let v (n : ℕ) : E.domain := f - cut n
  have hcut (n : ℕ) : (cut n : CarpetLp p) =ᵐ[carpetMeasure]
      fun x ↦ min (max (u x - (a - ε n)) 0) (2 * ε n) :=
    (E.shiftedTruncation_ae (a - ε n) (mul_pos zero_lt_two (hε n)) f).trans
      ((continuousLp_ae_eq p u).mono fun x hx ↦
        congrArg (fun t : ℝ ↦ min (max (t - (a - ε n)) 0) (2 * ε n)) hx)
  have hnorm (n : ℕ) : ‖(cut n : CarpetLp p)‖ ≤ 2 * ε n := by
    apply norm_carpetLp_le_of_ae_bound _ (mul_nonneg zero_le_two (hε n).le)
    filter_upwards [hcut n] with x hx
    rw [hx, Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) (by positivity))]
    exact min_le_right _ _
  have hroot (n : ℕ) : E.rootSeminorm (v n) ≤ 2 * E.rootSeminorm f := by
    calc
      E.rootSeminorm (v n) ≤ E.rootSeminorm f + E.rootSeminorm (cut n) :=
        map_sub_le_add E.rootSeminorm _ _
      _ ≤ 2 * E.rootSeminorm f := by
        rw [two_mul]
        exact add_le_add_right
          (E.rootSeminorm_shiftedTruncation_le (a - ε n) (mul_pos zero_lt_two (hε n)) f) _
  have hB (n : ℕ) : E.graphSeminorm (v n) ≤
      ((2 * E.rootSeminorm f) ^ p + (‖(f : CarpetLp p)‖ + 2) ^ p) ^ p⁻¹ := by
    have hb : 2 * ε n ≤ 2 := by linarith only [hεle n]
    apply E.graphSeminorm_le_of_le _ _ (hroot n)
    exact (norm_sub_le _ _).trans (add_le_add_right ((hnorm n).trans hb) _)
  have hlimNorm : Tendsto (fun n ↦ ‖(cut n : CarpetLp p)‖) atTop (𝓝 0) := by
    have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n ↦ 2 * ε n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hεlim.const_mul 2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ norm_nonneg _) hnorm
  have hlim : Tendsto (fun n ↦ (v n : CarpetLp p)) atTop (𝓝 (f : CarpetLp p)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [v, Submodule.coe_sub, sub_sub_cancel_left, norm_neg] using hlimNorm
  have hSv (n : ℕ) : S (v n) ≤ 0 := by
    let U : Set CarpetPoints := u ⁻¹' Ioo (a - ε n) (a + ε n)
    have hU : IsOpen U := isOpen_Ioo.preimage u.continuous
    have hAU : A ⊆ U := by
      intro x hx
      change u x = a at hx
      change u x ∈ Ioo (a - ε n) (a + ε n)
      rw [hx]
      exact ⟨by linarith [hε n], by linarith [hε n]⟩
    have hconst : (v n : CarpetLp p) =ᵐ[carpetMeasure.restrict U] fun _ ↦ a - ε n := by
      apply (ae_restrict_iff' hU.measurableSet).mpr
      filter_upwards [Lp.coeFn_sub (f : CarpetLp p) (cut n : CarpetLp p),
        continuousLp_ae_eq p u, hcut n] with x hx hf hcx hxU
      change u x ∈ Ioo (a - ε n) (a + ε n) at hxU
      change (v n : CarpetLp p) x = (f : CarpetLp p) x - (cut n : CarpetLp p) x at hx
      change (f : CarpetLp p) x = u x at hf
      rw [hx, hf, hcx, max_eq_left (sub_nonneg.mpr hxU.1.le),
        min_eq_left (by linarith [hxU.2])]
      ring
    have hz := measure_mono_null hAU (E.energyMeasure_eq_zero_of_ae_constant_on_open (v n) hU hconst)
    change ((E.energyMeasure (v n)).real A) ^ p⁻¹ ≤ 0
    rw [Measure.real, hz, ENNReal.toReal_zero, Real.zero_rpow
      (inv_ne_zero (zero_lt_one.trans E.one_lt_p).ne')]
  obtain ⟨g, hg, hSg⟩ := E.exists_domain_of_tendsto_of_seminorm_le S
    (fun z ↦ (E.energyMeasureSeminorm_le_rootSeminorm A hA z).trans
      (E.rootSeminorm_le_graphSeminorm z)) v (f : CarpetLp p) hB
    (fun r hr ↦ Eventually.of_forall fun n ↦ (hSv n).trans hr.le) hlim
  have hgf : g = f := Subtype.ext hg
  have hzero : S f = 0 := le_antisymm (hgf ▸ hSg) (apply_nonneg S f)
  change ((E.energyMeasure f).real A) ^ p⁻¹ = 0 at hzero
  rw [Measure.real, Real.rpow_eq_zero_iff_of_nonneg ENNReal.toReal_nonneg] at hzero
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_zero] using
    congrArg ENNReal.ofReal hzero.1

/-- Strong locality for continuous domain functions, as in (3.5). -/
theorem energyMeasure_apply_eq_of_sub_constant
    {A : Set CarpetPoints} (hA : MeasurableSet A) (u v : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) (hv : continuousLp p v ∈ E.domain)
    {a : ℝ} (h : ∀ x ∈ A, u x - v x = a) :
    E.energyMeasure ⟨continuousLp p u, hu⟩ A =
      E.energyMeasure ⟨continuousLp p v, hv⟩ A := by
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let g : E.domain := ⟨continuousLp p v, hv⟩
  have heq : continuousLp p (u - v) = ((f - g : E.domain) : CarpetLp p) := by
    apply Lp.ext
    filter_upwards [continuousLp_ae_eq p (u - v), continuousLp_ae_eq p u,
      continuousLp_ae_eq p v, Lp.coeFn_sub (f : CarpetLp p) (g : CarpetLp p)] with x h₁ h₂ h₃ h₄
    change (continuousLp p (u - v)) x = u x - v x at h₁
    exact h₁.trans (h₄.trans (congrArg₂ Sub.sub h₂ h₃)).symm
  have hm : continuousLp p (u - v) ∈ E.domain := heq.symm ▸ (f - g).property
  have hdiff : (⟨continuousLp p (u - v), hm⟩ : E.domain) = f - g := Subtype.ext heq
  apply E.energyMeasure_apply_eq_of_sub_null hA f g
  rw [← hdiff]
  exact measure_mono_null (fun x hx ↦ h x hx) (E.energyMeasure_levelSet_eq_zero (u - v) hm a)

/-- Truncation to a strip retains precisely the energy measure in the open strip. -/
theorem energyMeasure_shiftedTruncation_eq_restrict (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    E.energyMeasure (E.shiftedTruncation a b ⟨continuousLp p u, hu⟩) =
      (E.energyMeasure ⟨continuousLp p u, hu⟩).restrict (u ⁻¹' Ioo a (a + b)) := by
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let g := E.shiftedTruncation a b f
  let v : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ min (max (u x - a) 0) b,
      ((u.continuous.sub continuous_const).max continuous_const).min continuous_const⟩
  have heq : continuousLp p v = (g : CarpetLp p) := by
    apply Lp.ext
    exact (continuousLp_ae_eq p v).trans
      (((E.shiftedTruncation_ae a hb f).trans
        ((continuousLp_ae_eq p u).mono fun _ hx ↦
          congrArg (fun t : ℝ ↦ min (max (t - a) 0) b) hx))).symm
  have hv : continuousLp p v ∈ E.domain := heq.symm ▸ g.property
  have hgv : (⟨continuousLp p v, hv⟩ : E.domain) = g := Subtype.ext heq
  let A : Set CarpetPoints := u ⁻¹' Ioo a (a + b)
  have hA : MeasurableSet A := measurableSet_Ioo.preimage u.continuous.measurable
  have hz : E.energyMeasure g Aᶜ = 0 := by
    have hsub : Aᶜ ⊆ {x | v x = 0} ∪ {x | v x = b} := by
      intro x hx
      change ¬ (a < u x ∧ u x < a + b) at hx
      rcases not_and_or.mp hx with hx | hx
      · left
        change min (max (u x - a) 0) b = 0
        rw [max_eq_right (sub_nonpos.mpr (not_lt.mp hx)), min_eq_left hb.le]
      · right
        change min (max (u x - a) 0) b = b
        exact min_eq_right ((show b ≤ u x - a by linarith [not_lt.mp hx]).trans (le_max_left _ _))
    rw [← hgv]
    exact measure_mono_null hsub (measure_union_null
      (E.energyMeasure_levelSet_eq_zero v hv 0) (E.energyMeasure_levelSet_eq_zero v hv b))
  have hre : (E.energyMeasure g).restrict A = E.energyMeasure g :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hz)
  change E.energyMeasure g = (E.energyMeasure f).restrict A
  rw [← hre]
  apply Measure.ext
  intro B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB, ← hgv]
  exact E.energyMeasure_apply_eq_of_sub_constant (hB.inter hA) v u hv hu
    (a := -a) (by
      intro x hx
      have hxA : a < u x ∧ u x < a + b := hx.2
      change min (max (u x - a) 0) b - u x = -a
      rw [max_eq_left (sub_nonneg.mpr hxA.1.le), min_eq_left (by linarith [hxA.2])]
      ring)

end CarpetEnergy.SelfSimilarPEnergy
