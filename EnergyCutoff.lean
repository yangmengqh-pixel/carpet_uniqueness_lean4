import CarpetConnected
import EnergyLipschitz
import Mathlib.Topology.Algebra.Indicator

/-!
# Cutting off continuous finite-energy functions along open components

If the positive set splits into two open pieces, restricting the function to
either piece preserves the energy domain and decreases the energy.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private noncomputable def continuousWordMap : List (Fin 8) → C(CarpetPoints, CarpetPoints)
  | [] => ContinuousMap.id _
  | i :: w => (⟨cellMap i, continuous_cellMap i⟩ : C(CarpetPoints, CarpetPoints)).comp
      (continuousWordMap w)

private theorem coe_continuousWordMap (w : List (Fin 8)) :
    (continuousWordMap w : CarpetPoints → CarpetPoints) = wordMap w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change cellMap i ∘ (continuousWordMap w : CarpetPoints → CarpetPoints) = cellMap i ∘ wordMap w
    rw [ih]

private theorem continuousLp_mem_of_cells (v : C(CarpetPoints, ℝ)) (n : ℕ)
    (h : ∀ w : Fin n → Fin 8, continuousLp p (v.comp (continuousWordMap (List.ofFn w))) ∈ E.domain) :
    continuousLp p v ∈ E.domain := by
  induction n generalizing v with
  | zero => exact h Fin.elim0
  | succ n ih =>
    apply (E.continuous_gluing v).mpr
    intro i
    apply ih
    intro w
    have hw := h (Fin.cons i w)
    rw [List.ofFn_cons] at hw
    exact hw

private theorem continuousLp_const_eq (a : ℝ) :
    continuousLp p (ContinuousMap.const CarpetPoints a) = constantLp p a := by
  apply Lp.ext
  exact (continuousLp_ae_eq p _).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a).symm

private theorem continuousLp_zero_mem : continuousLp p (0 : C(CarpetPoints, ℝ)) ∈ E.domain := by
  rw [show (0 : C(CarpetPoints, ℝ)) = ContinuousMap.const CarpetPoints 0 from rfl,
    continuousLp_const_eq]
  exact E.constant_mem 0

private theorem continuousLp_comp_wordMap_mem (v : C(CarpetPoints, ℝ))
    (h : continuousLp p v ∈ E.domain) (w : List (Fin 8)) :
    continuousLp p (v.comp (continuousWordMap w)) ∈ E.domain := by
  let f : E.domain := ⟨continuousLp p v, h⟩
  have hco : continuousLp p (v.comp (continuousWordMap w)) = (E.pullbackWord w f : CarpetLp p) := by
    apply Lp.ext
    have h1 := continuousLp_ae_eq p (v.comp (continuousWordMap w))
    have h2 := (quasiMeasurePreserving_wordMap w).ae_eq_comp (continuousLp_ae_eq p v)
    have h3 := E.pullbackWord_isLpPullback w f
    rw [ContinuousMap.coe_comp, coe_continuousWordMap] at h1
    exact h1.trans (h2.symm.trans h3.symm)
  rw [hco]
  exact (E.pullbackWord w f).property

private theorem continuousLp_indicator_mem_of_compact (v : C(CarpetPoints, ℝ))
    (hv : continuousLp p v ∈ E.domain) {U A : Set CarpetPoints}
    (hU : IsOpen U) (hA : IsCompact A) (hAU : A ⊆ U)
    (hzero : ∀ x ∈ U \ A, v x = 0) (g : C(CarpetPoints, ℝ))
    (hg : (g : CarpetPoints → ℝ) = U.indicator v) :
    continuousLp p g ∈ E.domain := by
  obtain ⟨ε, hε, hthick⟩ := hA.exists_thickening_subset_open hU hAU
  obtain ⟨n, hn⟩ := (tendsto_wordMap_radius.eventually_lt_const hε).exists
  apply E.continuousLp_mem_of_cells g n
  intro w
  let W := wordMap (List.ofFn w)
  by_cases h : (A ∩ range W).Nonempty
  · obtain ⟨x, hxA, hxW⟩ := h
    have hsub : range W ⊆ U := by
      intro y hy
      exact hthick (mem_thickening_iff.mpr ⟨x, hxA, (wordMap_dist_le n w hy hxW).trans_lt hn⟩)
    have heq : g.comp (continuousWordMap (List.ofFn w)) = v.comp (continuousWordMap (List.ofFn w)) := by
      ext y
      change g (continuousWordMap (List.ofFn w) y) = v (continuousWordMap (List.ofFn w) y)
      rw [show continuousWordMap (List.ofFn w) y = W y from congrFun (coe_continuousWordMap _) y,
        show g (W y) = U.indicator v (W y) from congrFun hg _, indicator_of_mem (hsub (mem_range_self y))]
    rw [heq]
    exact E.continuousLp_comp_wordMap_mem v hv _
  · have heq : g.comp (continuousWordMap (List.ofFn w)) = 0 := by
      ext y
      change g (continuousWordMap (List.ofFn w) y) = 0
      rw [show continuousWordMap (List.ofFn w) y = W y from congrFun (coe_continuousWordMap _) y,
        show g (W y) = U.indicator v (W y) from congrFun hg _]
      by_cases hy : W y ∈ U
      · rw [indicator_of_mem hy]
        exact hzero _ ⟨hy, fun hA ↦ h ⟨W y, hA, mem_range_self y⟩⟩
      · exact indicator_of_notMem hy _
    rw [heq]
    exact E.continuousLp_zero_mem

private theorem energy_le_of_continuous_indicator (v g : C(CarpetPoints, ℝ))
    (hv : continuousLp p v ∈ E.domain) (hg : continuousLp p g ∈ E.domain)
    {U : Set CarpetPoints} (hU : MeasurableSet U) (heq : (g : CarpetPoints → ℝ) = U.indicator v) :
    E.energy ⟨continuousLp p g, hg⟩ ≤ E.energy ⟨continuousLp p v, hv⟩ := by
  let a : E.domain := ⟨continuousLp p g, hg⟩
  let b : E.domain := ⟨continuousLp p v, hv⟩
  have hmass : (E.energyMeasure a) U = (E.energyMeasure b) U :=
    E.energyMeasure_apply_eq_of_sub_constant hU g v hg hv (a := 0) fun x hx ↦ by
      rw [show g x = U.indicator v x from congrFun heq x, indicator_of_mem hx, sub_self]
  have hnull : (E.energyMeasure a) Uᶜ = 0 := by
    apply measure_mono_null _ (E.energyMeasure_levelSet_eq_zero g hg 0)
    intro x hx
    change g x = 0
    rw [show g x = U.indicator v x from congrFun heq x, indicator_of_notMem hx]
  apply ENNReal.coe_le_coe.mp
  change (E.energy a : ℝ≥0∞) ≤ (E.energy b : ℝ≥0∞)
  rw [← E.energyMeasure_univ, ← E.energyMeasure_univ]
  calc
    E.energyMeasure a univ = E.energyMeasure a U + E.energyMeasure a Uᶜ := by
      rw [← measure_union disjoint_compl_right hU.compl, union_compl_self]
    _ = E.energyMeasure b U := by rw [hmass, hnull, add_zero]
    _ ≤ E.energyMeasure b univ := measure_mono (subset_univ _)

private theorem eq_zero_on_frontier_of_open_positive_split
    (u : C(CarpetPoints, ℝ)) (hu : ∀ x, 0 ≤ u x)
    {U : Set CarpetPoints} (hU : IsOpen U)
    (hV : IsOpen ({x | 0 < u x} \ U)) :
    ∀ x ∈ frontier U, u x = 0 := by
  intro x hx
  apply le_antisymm _ (hu x)
  by_contra! hn
  have hx' : x ∉ U := by
    intro hu'
    exact hx.2 (by rwa [hU.interior_eq])
  have hnbhd : {x | 0 < u x} \ U ∈ 𝓝 x := hV.mem_nhds ⟨hn, hx'⟩
  obtain ⟨y, hy, hyU⟩ := mem_closure_iff_nhds.mp hx.1 _ hnbhd
  exact hy.2 hyU

private theorem exists_posPart_sub_mem (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) (t : ℝ) :
    ∃ hv : continuousLp p
      (⟨fun x ↦ max (u x - t) 0, (u.continuous.sub continuous_const).max continuous_const⟩ :
        C(CarpetPoints, ℝ)) ∈ E.domain,
      E.energy ⟨_, hv⟩ ≤ E.energy ⟨continuousLp p u, hu⟩ := by
  let φ : ℝ → ℝ := fun r ↦ max (r - t) 0
  have hφ : LipschitzWith 1 φ := by
    have hshift : LipschitzWith 1 (fun r : ℝ ↦ r - t) := LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [dist_sub_right, NNReal.coe_one, one_mul]
    have h := Lp.lipschitzWith_pos_part.comp hshift
    simpa only [one_mul, Function.comp_def] using h
  let v : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ φ (u x), (u.continuous.sub continuous_const).max continuous_const⟩
  let f : E.domain := ⟨continuousLp p u, hu⟩
  obtain ⟨g, hg, hle⟩ := E.exists_energyMeasure_comp_le hφ f
  have heq : continuousLp p v = (g : CarpetLp p) := by
    apply Lp.ext
    have haux : φ ∘ (f : CarpetLp p) =ᵐ[carpetMeasure] fun x ↦ φ (u x) :=
      (continuousLp_ae_eq p u).mono fun x hx ↦ congrArg φ hx
    exact (continuousLp_ae_eq p v).trans (haux.symm.trans hg.symm)
  have hv : continuousLp p v ∈ E.domain := heq.symm ▸ g.property
  refine ⟨hv, ?_⟩
  have heq' : (⟨continuousLp p v, hv⟩ : E.domain) = g := Subtype.ext heq
  change E.energy ⟨continuousLp p v, hv⟩ ≤ E.energy f
  rw [heq']
  apply ENNReal.coe_le_coe.mp
  rw [← E.energyMeasure_univ, ← E.energyMeasure_univ]
  simpa only [NNReal.one_rpow, ENNReal.coe_one, one_smul] using hle univ

/-- The cutoff argument of Lemma 3.7 for an open partition of the positive set. -/
theorem exists_continuous_indicator_of_open_positive_split
    (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain) (hn : ∀ x, 0 ≤ u x)
    {U : Set CarpetPoints} (hU : IsOpen U)
    (hV : IsOpen ({x | 0 < u x} \ U)) :
    ∃ g : C(CarpetPoints, ℝ), ∃ hg : continuousLp p g ∈ E.domain,
      (g : CarpetPoints → ℝ) = U.indicator u ∧
      E.energy ⟨continuousLp p g, hg⟩ ≤ E.energy ⟨continuousLp p u, hu⟩ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hfront := eq_zero_on_frontier_of_open_positive_split u hn hU hV
  let g : C(CarpetPoints, ℝ) := ⟨U.indicator u, u.continuous.indicator hfront⟩
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let v (n : ℕ) : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ max (u x - ε n) 0, (u.continuous.sub continuous_const).max continuous_const⟩
  have hv (n : ℕ) : ∃ hm : continuousLp p (v n) ∈ E.domain,
      E.energy ⟨_, hm⟩ ≤ E.energy ⟨continuousLp p u, hu⟩ := E.exists_posPart_sub_mem u hu (ε n)
  choose hm henergy using hv
  let a (n : ℕ) : C(CarpetPoints, ℝ) := ⟨U.indicator (v n), (v n).continuous.indicator
    fun x hx ↦ by
      change max (u x - ε n) 0 = 0
      rw [hfront x hx]
      exact max_eq_right (sub_nonpos.mpr (hε n).le)⟩
  have ha (n : ℕ) : continuousLp p (a n) ∈ E.domain := by
    let V : Set CarpetPoints := {x | 0 < u x} \ U
    let A : Set CarpetPoints := {x | ε n ≤ u x} \ V
    have hA : IsCompact A :=
      ((isClosed_le continuous_const u.continuous).inter hV.isClosed_compl).isCompact
    have hAU : A ⊆ U := fun x hx ↦ by
      by_contra hx'
      exact hx.2 ⟨(hε n).trans_le hx.1, hx'⟩
    apply E.continuousLp_indicator_mem_of_compact (v n) (hm n) hU hA hAU _ (a n) rfl
    intro x hx
    have hx' : u x < ε n := by
      by_contra! h
      exact hx.2 ⟨h, fun hv' ↦ hv'.2 hx.1⟩
    exact max_eq_right (sub_nonpos.mpr hx'.le)
  let f (n : ℕ) : E.domain := ⟨continuousLp p (a n), ha n⟩
  let f₀ : E.domain := ⟨continuousLp p u, hu⟩
  have hroot (n : ℕ) : E.rootSeminorm (f n) ≤ E.rootSeminorm f₀ := by
    rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
    apply Real.rpow_le_rpow (E.energy (f n)).property _ (inv_nonneg.mpr hp.le)
    exact_mod_cast (E.energy_le_of_continuous_indicator (v n) (a n) (hm n) (ha n) hU.measurableSet rfl
      |>.trans (henergy n))
  have hnorm (n : ℕ) : ‖(f n : CarpetLp p)‖ ≤ ‖u‖ := by
    apply norm_carpetLp_le_of_ae_bound _ (norm_nonneg _)
    filter_upwards [continuousLp_ae_eq p (a n)] with x hx
    change (f n : CarpetLp p) x = U.indicator (v n) x at hx
    rw [hx]
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
      have hp' : 0 ≤ max (u x - ε n) 0 := le_max_right _ _
      change ‖max (u x - ε n) 0‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg hp']
      exact (max_le (sub_le_self _ (hε n).le) (hn x)).trans
        ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using u.norm_coe_le_norm x))
    · rw [indicator_of_notMem hxU, norm_zero]
      exact norm_nonneg _
  have hB (n : ℕ) : E.graphSeminorm (f n) ≤
      (E.rootSeminorm f₀ ^ p + ‖u‖ ^ p) ^ p⁻¹ :=
    E.graphSeminorm_le_of_le (f n) (hnorm n) (hroot n)
  have hdiff (n : ℕ) : ‖(f n : CarpetLp p) - continuousLp p g‖ ≤ ε n := by
    apply norm_carpetLp_le_of_ae_bound _ (hε n).le
    filter_upwards [Lp.coeFn_sub (f n : CarpetLp p) (continuousLp p g),
      continuousLp_ae_eq p (a n), continuousLp_ae_eq p g] with x hx hxa hxg
    change ((f n : CarpetLp p) - continuousLp p g) x =
      (f n : CarpetLp p) x - continuousLp p g x at hx
    change (f n : CarpetLp p) x = U.indicator (v n) x at hxa
    change continuousLp p g x = U.indicator u x at hxg
    rw [hx, hxa, hxg]
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU, indicator_of_mem hxU]
      change ‖max (u x - ε n) 0 - u x‖ ≤ _
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith only [le_max_left (u x - ε n) 0]
      · have hb := max_le (sub_le_self (u x) (hε n).le) (hn x)
        linarith only [hb, hε n]
    · rw [indicator_of_notMem hxU, indicator_of_notMem hxU, sub_self, norm_zero]
      exact (hε n).le
  have hlim : Tendsto (fun n ↦ (f n : CarpetLp p)) atTop (𝓝 (continuousLp p g)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεlim
        (fun _ ↦ norm_nonneg _) hdiff)
  obtain ⟨z, hz, hr⟩ := E.exists_domain_of_tendsto_of_seminorm_le E.rootSeminorm
    E.rootSeminorm_le_graphSeminorm f (continuousLp p g) hB
    (fun r h ↦ Eventually.of_forall fun n ↦ (hroot n).trans h.le) hlim
  have hg : continuousLp p g ∈ E.domain := hz ▸ z.property
  have heq : (⟨continuousLp p g, hg⟩ : E.domain) = z := Subtype.ext hz.symm
  refine ⟨g, hg, rfl, ?_⟩
  rw [heq]
  apply NNReal.coe_le_coe.mp
  rw [E.rootSeminorm_apply, E.rootSeminorm_apply] at hr
  exact (Real.rpow_le_rpow_iff (E.energy z).property (E.energy f₀).property (inv_pos.mpr hp)).mp hr

/-- Lemma 3.7. Cutting off a nonnegative continuous domain function to a
union of connected components of its positive set decreases its energy. -/
theorem exists_continuous_indicator_of_component_union
    (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain) (hn : ∀ x, 0 ≤ u x)
    (S : Set CarpetPoints) :
    let U := ⋃ x : S, connectedComponentIn {x | 0 < u x} x.val
    ∃ g : C(CarpetPoints, ℝ), ∃ hg : continuousLp p g ∈ E.domain,
      (g : CarpetPoints → ℝ) = U.indicator u ∧
      E.energy ⟨continuousLp p g, hg⟩ ≤ E.energy ⟨continuousLp p u, hu⟩ := by
  let P : Set CarpetPoints := {x | 0 < u x}
  let U := ⋃ x : S, connectedComponentIn P x.val
  have hP : IsOpen P := isOpen_lt continuous_const u.continuous
  have hU : IsOpen U := isOpen_iUnion fun _ ↦ hP.connectedComponentIn
  have hV : IsOpen (P \ U) := by
    have hEq : P \ U = ⋃ y : {y : CarpetPoints // y ∈ P \ U}, connectedComponentIn P y.val := by
      ext x
      constructor
      · intro hx
        exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_connectedComponentIn hx.1⟩
      · intro hx
        obtain ⟨y, hy⟩ := mem_iUnion.mp hx
        refine ⟨connectedComponentIn_subset P y.val hy, ?_⟩
        intro hxU
        obtain ⟨z, hz⟩ := mem_iUnion.mp hxU
        have heq := (connectedComponentIn_eq hy).trans (connectedComponentIn_eq hz).symm
        exact y.property.2 (mem_iUnion.mpr ⟨z, heq ▸ mem_connectedComponentIn y.property.1⟩)
    rw [hEq]
    exact isOpen_iUnion fun _ ↦ hP.connectedComponentIn
  exact E.exists_continuous_indicator_of_open_positive_split u hu hn hU hV

end CarpetEnergy.SelfSimilarPEnergy
