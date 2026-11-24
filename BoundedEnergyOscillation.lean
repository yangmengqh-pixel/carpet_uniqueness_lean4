import EnergyOppositeComponents
import EnergyVanishing

/-!
# Bounded functions of small energy

A nonnegative bounded function with a nontrivial Lp norm and sufficiently
small energy has a positive component meeting all four corner interiors.
The two parts of a centered function are then controlled by the capacity
bound for opposite components.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem exists_energy_bound_for_fixed_zero_set [Fact (1 ≤ ENNReal.ofReal p)]
    (A : Set CarpetPoints) (hA : carpetMeasure A ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ f : E.domain,
      (∀ᵐ x ∂carpetMeasure, 0 ≤ (f : CarpetLp p) x ∧ (f : CarpetLp p) x ≤ 1) →
      ((f : CarpetLp p) =ᵐ[carpetMeasure.restrict A] fun _ ↦ 0) →
      (E.energy f : ℝ) < δ → ‖(f : CarpetLp p)‖ < ε := by
  by_contra! h
  choose f hf_bounds hf_zero hf_energy hf_norm using fun n : ℕ ↦
    h (1 / ((n : ℝ) + 1)) (by positivity)
  have hE : Tendsto (fun n ↦ (E.energy (f n) : ℝ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ ↦ NNReal.coe_nonneg _) (fun n ↦ (hf_energy n).le)
  have hlim := E.tendsto_norm_zero_of_energy_tendsto_zero_of_ae_zero A hA zero_lt_one
    f hf_bounds hf_zero hE
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
  exact hn.not_ge (hf_norm n)

private theorem continuousLp_norm_le_sum_of_pointwise_le [Fact (1 ≤ ENNReal.ofReal p)]
    {ι : Type*} [Fintype ι] (u : C(CarpetPoints, ℝ)) (g : ι → C(CarpetPoints, ℝ))
    (hu : ∀ x, 0 ≤ u x) (hg : ∀ x, u x ≤ ∑ i, g i x) :
    ‖continuousLp p u‖ ≤ ∑ i, ‖continuousLp p (g i)‖ := by
  refine (Lp.norm_le_norm_of_ae_le (g := ∑ i, continuousLp p (g i)) ?_).trans (norm_sum_le _ _)
  filter_upwards [continuousLp_ae_eq p u, Lp.coeFn_finsetSum Finset.univ
    (fun i ↦ continuousLp p (g i)), eventually_all.mpr fun i ↦ continuousLp_ae_eq p (g i)]
    with x hux hsum hgx
  rw [hux]
  have hs : (∑ i, continuousLp p (g i) : CarpetLp p) x = ∑ i, g i x :=
    hsum.trans (by rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i _ ↦ hgx i)
  rw [hs, Real.norm_of_nonneg (hu x), Real.norm_of_nonneg ((hu x).trans (hg x))]
  exact hg x

private theorem exists_spanning_component_of_small_energy [Fact (1 ≤ ENNReal.ofReal p)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain),
      (∀ x, 0 ≤ u x ∧ u x ≤ 1) → ε ≤ ‖continuousLp p u‖ →
      (E.energy ⟨continuousLp p u, hu⟩ : ℝ) < δ →
      ∃ x : CarpetPoints, ∀ i : Fin 4,
        (connectedComponentIn {x | 0 < u x} x ∩ cellOpenPart (cornerCell i)).Nonempty := by
  let K (i : Fin 4) := cellOpenPart (cornerCell i)
  have hK (i : Fin 4) : carpetMeasure (K i) ≠ 0 := by
    change carpetMeasure (cellOpenPart (cornerCell i)) ≠ 0
    rw [carpetMeasure_cellOpenPart]
    norm_num
  choose d hd hsmall using fun i ↦ E.exists_energy_bound_for_fixed_zero_set (K i) (hK i)
    (show 0 < ε / 4 by positivity)
  let δ : ℝ := min (min (d 0) (d 1)) (min (d 2) (d 3))
  have hδ : 0 < δ := lt_min (lt_min (hd _) (hd _)) (lt_min (hd _) (hd _))
  have hδd (i : Fin 4) : δ ≤ d i := by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro u hu hbound hnorm henergy
  let posSet := {x : CarpetPoints | 0 < u x}
  let S (i : Fin 4) := {x | Disjoint (connectedComponentIn posSet x) (K i)}
  let U (i : Fin 4) := ⋃ x : S i, connectedComponentIn posSet x.val
  choose g hg hgu hge using fun i ↦
    E.exists_continuous_indicator_of_component_union u hu (fun x ↦ (hbound x).1) (S i)
  have hgb (i : Fin 4) (x : CarpetPoints) : 0 ≤ g i x ∧ g i x ≤ 1 := by
    have hi := congrFun (hgu i) x
    by_cases hx : x ∈ U i
    · rw [indicator_of_mem hx] at hi
      exact hi.symm ▸ hbound x
    · rw [indicator_of_notMem hx] at hi
      exact hi.symm ▸ ⟨le_rfl, zero_le_one⟩
  have hgzero (i : Fin 4) (x : CarpetPoints) (hx : x ∈ K i) : g i x = 0 := by
    have hnot : x ∉ U i := by
      intro hh
      obtain ⟨y, hy⟩ := mem_iUnion.mp hh
      exact Set.disjoint_left.mp y.property hy hx
    have he := congrFun (hgu i) x
    rwa [indicator_of_notMem hnot] at he
  have hn (i : Fin 4) : ‖continuousLp p (g i)‖ < ε / 4 := by
    apply hsmall i ⟨continuousLp p (g i), hg i⟩
    · exact (continuousLp_ae_eq p (g i)).mono fun x hx ↦ hx.symm ▸ hgb i x
    · have ha : (continuousLp p (g i) : CarpetPoints → ℝ) =ᵐ[carpetMeasure.restrict (K i)] g i :=
        ae_restrict_of_ae (continuousLp_ae_eq p (g i))
      exact ha.trans ((ae_restrict_mem (isOpen_cellOpenPart _).measurableSet).mono
        fun x hx ↦ hgzero i x hx)
    · exact (NNReal.coe_le_coe.mpr (hge i)).trans_lt (henergy.trans_le (hδd i))
  by_contra! hspan
  have hsum (x : CarpetPoints) : u x ≤ ∑ i, g i x := by
    by_cases hpos : 0 < u x
    · obtain ⟨i, hi⟩ := hspan x
      have hx : x ∈ S i := Set.disjoint_iff_inter_eq_empty.mpr hi
      have he := congrFun (hgu i) x
      have hxi : x ∈ U i := mem_iUnion.mpr ⟨⟨x, hx⟩, mem_connectedComponentIn hpos⟩
      rw [indicator_of_mem hxi] at he
      rw [← he]
      exact Finset.single_le_sum (fun j _ ↦ (hgb j x).1) (Finset.mem_univ i)
    · exact (not_lt.mp hpos).trans (Finset.sum_nonneg fun j _ ↦ (hgb j x).1)
  have hle := continuousLp_norm_le_sum_of_pointwise_le (p := p) u g (fun x ↦ (hbound x).1) hsum
  have htotal : (∑ i, ‖continuousLp p (g i)‖) < ε := by
    rw [Fin.sum_univ_four]
    linarith [hn 0, hn 1, hn 2, hn 3]
  exact (hle.trans_lt htotal).not_ge hnorm

/-- The continuous function after subtracting its mean under the carpet probability. -/
noncomputable def centeredContinuous (f : C(CarpetPoints, ℝ)) : C(CarpetPoints, ℝ) :=
  ⟨fun x ↦ f x - ∫ y, f y ∂carpetMeasure, f.continuous.sub continuous_const⟩

private theorem continuous_integrable {v : CarpetPoints → ℝ} (hv : Continuous v) :
    Integrable v carpetMeasure :=
  hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace v)

private theorem integral_continuous_le_norm [Fact (1 ≤ ENNReal.ofReal p)]
    (v : C(CarpetPoints, ℝ)) :
    (∫ x, v x ∂carpetMeasure) ≤ ‖continuousLp p v‖ := by
  have hh := norm_setIntegral_le (p := p) univ (continuousLp p v)
  rw [Measure.restrict_univ, integral_congr_ae (continuousLp_ae_eq p v)] at hh
  exact (le_abs_self _).trans hh

private theorem continuous_unit_mean_bounds (f : C(CarpetPoints, ℝ))
    (h : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ (∫ x, f x ∂carpetMeasure) ∧ (∫ x, f x ∂carpetMeasure) ≤ 1 := by
  refine ⟨integral_nonneg fun x ↦ (h x).1, ?_⟩
  have hh := integral_mono (continuous_integrable f.continuous)
    (integrable_const (1 : ℝ)) (fun x ↦ (h x).2)
  simpa [Measure.real] using hh

include E in
private theorem norm_rpow_le_integral_abs_centered [Fact (1 ≤ ENNReal.ofReal p)]
    (f : C(CarpetPoints, ℝ)) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ‖continuousLp p (centeredContinuous f)‖ ^ p ≤
      ∫ x, |centeredContinuous f x| ∂carpetMeasure := by
  let w := centeredContinuous f
  let v : C(CarpetPoints, ℝ) := ⟨fun x ↦ |w x|, w.continuous.abs⟩
  have hv (x : CarpetPoints) : 0 ≤ v x ∧ v x ≤ 1 := by
    have hm := continuous_unit_mean_bounds f hf
    change 0 ≤ |f x - ∫ y, f y ∂carpetMeasure| ∧ |f x - ∫ y, f y ∂carpetMeasure| ≤ 1
    exact ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [(hf x).1, hm.2], by linarith [(hf x).2, hm.1]⟩⟩
  have hnorm : ‖continuousLp p w‖ ≤ ‖continuousLp p v‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [continuousLp_ae_eq p w, continuousLp_ae_eq p v] with x hw hx
    rw [hw, hx, Real.norm_eq_abs, Real.norm_of_nonneg (hv x).1]
    exact le_rfl
  have hI := E.norm_rpow_le_integral (continuousLp p v)
    ((continuousLp_ae_eq p v).mono fun x hx ↦ hx.symm ▸ hv x)
  rw [Real.one_rpow, one_mul, integral_congr_ae (continuousLp_ae_eq p v)] at hI
  exact (Real.rpow_le_rpow (norm_nonneg _) hnorm (zero_le_one.trans E.one_lt_p.le)).trans hI

private theorem integral_positive_parts_centered (f : C(CarpetPoints, ℝ)) :
    let w := centeredContinuous f
    (∫ x, |w x| ∂carpetMeasure) = 2 * (∫ x, max (w x) 0 ∂carpetMeasure) ∧
    (∫ x, |w x| ∂carpetMeasure) = 2 * (∫ x, max (-w x) 0 ∂carpetMeasure) := by
  dsimp only
  let w := centeredContinuous f
  let up (x : CarpetPoints) := max (w x) 0
  let down (x : CarpetPoints) := max (-w x) 0
  have hU : Integrable up carpetMeasure := continuous_integrable (w.continuous.max continuous_const)
  have hD : Integrable down carpetMeasure :=
    continuous_integrable (w.continuous.neg.max continuous_const)
  have hwzero : (∫ x, w x ∂carpetMeasure) = 0 := by
    change (∫ x, f x - (∫ y, f y ∂carpetMeasure) ∂carpetMeasure) = 0
    rw [integral_sub (continuous_integrable f.continuous) (integrable_const _)]
    simp [Measure.real]
  have hsum : (fun x ↦ |w x|) = fun x ↦ up x + down x := by
    funext x
    by_cases h : 0 ≤ w x
    · simp [up, down, abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · have h' := (lt_of_not_ge h).le
      simp [up, down, abs_of_nonpos h', max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
  have hdiff : (w : CarpetPoints → ℝ) = fun x ↦ up x - down x := by
    funext x
    by_cases h : 0 ≤ w x
    · simp [up, down, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · have h' := (lt_of_not_ge h).le
      simp [up, down, max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
  rw [hdiff, integral_sub hU hD] at hwzero
  change (∫ x, |w x| ∂carpetMeasure) = _ ∧ (∫ x, |w x| ∂carpetMeasure) = _
  rw [hsum, integral_add hU hD]
  change (∫ x, up x ∂carpetMeasure) + (∫ x, down x ∂carpetMeasure) = 2 * (∫ x, up x ∂carpetMeasure) ∧
    (∫ x, up x ∂carpetMeasure) + (∫ x, down x ∂carpetMeasure) = 2 * (∫ x, down x ∂carpetMeasure)
  exact ⟨by linarith, by linarith⟩

private theorem integral_max_le_shifted_add {w : CarpetPoints → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, max (w x) 0 ∂carpetMeasure) ≤ t + ∫ x, max (w x - t) 0 ∂carpetMeasure := by
  have hc : Integrable (fun x ↦ max (w x - t) 0) carpetMeasure :=
    continuous_integrable ((hw.sub continuous_const).max continuous_const)
  have he : (∫ x, t + max (w x - t) 0 ∂carpetMeasure) =
      t + ∫ x, max (w x - t) 0 ∂carpetMeasure := by
    rw [integral_add (integrable_const _) hc]
    simp [Measure.real]
  rw [← he]
  apply integral_mono (continuous_integrable (hw.max continuous_const)) ((integrable_const _).add hc)
  intro x
  change max (w x) 0 ≤ t + max (w x - t) 0
  exact max_le (by linarith [le_max_left (w x - t) 0])
    (add_nonneg ht (le_max_right (w x - t) 0))

/-- Taking the positive part after subtracting a constant is 1-Lipschitz. -/
theorem lipschitzWith_sub_part (k : ℝ) : LipschitzWith 1 (fun t : ℝ ↦ max (t - k) 0) := by
  have h : LipschitzWith 1 (fun t : ℝ ↦ t - k) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right]
    exact le_rfl
  exact h.max_const _

/-- Taking the positive part of a constant minus the input is 1-Lipschitz. -/
theorem lipschitzWith_reverse_sub_part (k : ℝ) :
    LipschitzWith 1 (fun t : ℝ ↦ max (k - t) 0) := by
  have h : LipschitzWith 1 (fun t : ℝ ↦ k - t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show k - x - (k - y) = -(x - y) by ring, abs_neg]
  exact h.max_const _

/-- A uniform small-energy bound for centered bounded continuous functions. -/
theorem exists_energy_bound_for_bounded_oscillation
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain),
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (E.energy ⟨continuousLp p f, hf⟩ : ℝ) < δ →
      ‖continuousLp p (centeredContinuous f)‖ < ε := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  let t := ε ^ p / 4
  have ht : 0 < t := div_pos (Real.rpow_pos_of_pos hε _) (by norm_num)
  obtain ⟨d, hd, hspan⟩ := E.exists_spanning_component_of_small_energy ht
  let κ := 2 * E.scalingFactor * (2 * t) ^ p * E.leftRightCapacity
  have hκ : 0 < κ := by
    have hρ := E.isScalingFactor_scalingFactor.1
    have hχ := E.leftRightCapacity_pos
    positivity
  refine ⟨min d κ, lt_min hd hκ, ?_⟩
  intro f hf hbound henergy
  by_contra! hnorm
  let m := ∫ x, f x ∂carpetMeasure
  let w := centeredContinuous f
  let a := m - t
  let b := m + t
  have hab : a < b := by dsimp only [a, b]; linarith
  obtain ⟨u, hu, huf, hue⟩ := E.exists_continuous_comp_energy_le_mul f hf (lipschitzWith_sub_part b)
  obtain ⟨v, hv, hvf, hve⟩ := E.exists_continuous_comp_energy_le_mul f hf (lipschitzWith_reverse_sub_part a)
  simp only [NNReal.coe_one, Real.one_rpow, one_mul] at hue hve
  have hU (x : CarpetPoints) : u x = max (w x - t) 0 := by
    rw [huf]
    change max (f x - (m + t)) 0 = max (f x - m - t) 0
    rw [sub_add_eq_sub_sub]
  have hV (x : CarpetPoints) : v x = max (-w x - t) 0 := by
    rw [hvf]
    change max (m - t - f x) 0 = max (-(f x - m) - t) 0
    congr 1
    ring
  have hmb : 0 ≤ m ∧ m ≤ 1 := continuous_unit_mean_bounds f hbound
  have hub (x : CarpetPoints) : 0 ≤ u x ∧ u x ≤ 1 := by
    rw [huf]
    refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
    dsimp only [b]
    linarith [(hbound x).2, hmb.1]
  have hvb (x : CarpetPoints) : 0 ≤ v x ∧ v x ≤ 1 := by
    rw [hvf]
    refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
    dsimp only [a]
    linarith [(hbound x).1, hmb.2]
  have hlarge : 4 * t ≤ ∫ x, |w x| ∂carpetMeasure := by
    have hh := Real.rpow_le_rpow hε.le hnorm (zero_le_one.trans E.one_lt_p.le)
    calc
      4 * t = ε ^ p := by dsimp only [t]; ring
      _ ≤ _ := hh.trans (E.norm_rpow_le_integral_abs_centered f hbound)
  obtain ⟨hpos, hneg⟩ := integral_positive_parts_centered f
  have hUb : (∫ x, max (w x) 0 ∂carpetMeasure) ≤ t + ∫ x, u x ∂carpetMeasure := by
    rw [integral_congr_ae (Eventually.of_forall hU)]
    exact integral_max_le_shifted_add w.continuous ht.le
  have hVb : (∫ x, max (-w x) 0 ∂carpetMeasure) ≤ t + ∫ x, v x ∂carpetMeasure := by
    rw [integral_congr_ae (Eventually.of_forall hV)]
    exact integral_max_le_shifted_add w.continuous.neg ht.le
  have hUn : t ≤ ‖continuousLp p u‖ := by
    apply le_trans _ (integral_continuous_le_norm u)
    change (∫ x, |w x| ∂carpetMeasure) = 2 * (∫ x, max (w x) 0 ∂carpetMeasure) at hpos
    linarith
  have hVn : t ≤ ‖continuousLp p v‖ := by
    apply le_trans _ (integral_continuous_le_norm v)
    change (∫ x, |w x| ∂carpetMeasure) = 2 * (∫ x, max (-w x) 0 ∂carpetMeasure) at hneg
    linarith
  obtain ⟨x, hx⟩ := hspan u hu hub hUn (hue.trans_lt (henergy.trans_le (min_le_left _ _)))
  obtain ⟨y, hy⟩ := hspan v hv hvb hVn (hve.trans_lt (henergy.trans_le (min_le_left _ _)))
  have hpu : {x | 0 < u x} = {x | b < f x} := by
    ext x
    change 0 < u x ↔ b < f x
    rw [huf, lt_max_iff, sub_pos]
    simp
  have hpv : {x | 0 < v x} = {x | f x < a} := by
    ext x
    change 0 < v x ↔ f x < a
    rw [hvf, lt_max_iff, sub_pos]
    simp
  simp only [hpu] at hx
  simp only [hpv] at hy
  have h := E.energy_ge_of_opposite_components f hf hab x y hx hy
  have he : b - a = 2 * t := by dsimp only [a, b]; ring
  rw [he] at h
  exact (henergy.trans_le (min_le_right _ _)).not_ge h

/-- Proposition 3.6. Bounded continuous functions with vanishing energies
converge to their means in Lp. -/
theorem tendsto_centered_norm_zero_of_bounded_energy_tendsto_zero
    (f : ℕ → C(CarpetPoints, ℝ)) (hf : ∀ n, continuousLp p (f n) ∈ E.domain)
    (hbound : ∀ n x, 0 ≤ f n x ∧ f n x ≤ 1)
    (henergy : Tendsto (fun n ↦ (E.energy ⟨continuousLp p (f n), hf n⟩ : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖continuousLp p (centeredContinuous (f n))‖) atTop (𝓝 0) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _), fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, h⟩ := E.exists_energy_bound_for_bounded_oscillation hε
  exact (henergy.eventually_lt_const hδ).mono fun n hn ↦ h (f n) (hf n) (hbound n) hn

end CarpetEnergy.SelfSimilarPEnergy
