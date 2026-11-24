import CarpetCellAverages
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Lp projections to cell averages

Deleting the null level boundary makes the cells a disjoint partition
up to null sets. The resulting piecewise-constant averaging operator is
contractive by the cell Jensen inequality.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

/-- A word cell with the level boundary removed. -/
noncomputable def openWordCell {n : ℕ} (w : Fin n → Fin 8) : Set CarpetPoints :=
  range (wordMap (List.ofFn w)) \ carpetCellBoundary n

theorem measurableSet_openWordCell {n : ℕ} (w : Fin n → Fin 8) :
    MeasurableSet (openWordCell w) :=
  (measurableEmbedding_wordMap _).measurableSet_range.diff (measurableSet_carpetCellBoundary n)

theorem pairwise_disjoint_openWordCell (n : ℕ) :
    Pairwise (Disjoint on (openWordCell (n := n))) := by
  intro a b hab
  apply disjoint_left.mpr
  intro x ha hb
  exact ha.2 (inter_word_subset_cellBoundary hab ⟨ha.1, hb.1⟩)

theorem iUnion_openWordCell (n : ℕ) :
    (⋃ w : Fin n → Fin 8, openWordCell w) = (carpetCellBoundary n)ᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    exact hw.2
  · intro hx
    obtain ⟨w, hw⟩ := exists_wordMap_range n x
    exact mem_iUnion.mpr ⟨w, hw, hx⟩

theorem carpetMeasure_openWordCell {n : ℕ} (w : Fin n → Fin 8) :
    carpetMeasure (openWordCell w) = ((8 : ℝ≥0∞)⁻¹) ^ n := by
  rw [openWordCell, measure_sdiff_null (carpetMeasure_carpetCellBoundary_eq_zero n),
    carpetMeasure_range_wordMap, List.length_ofFn]

theorem carpetMeasure_restrict_openWordCell {n : ℕ} (w : Fin n → Fin 8) :
    carpetMeasure.restrict (openWordCell w) = carpetMeasure.restrict (range (wordMap (List.ofFn w))) := by
  apply Measure.restrict_congr_set
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (carpetMeasure_carpetCellBoundary_eq_zero n)] with x hx
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hx⟩⟩

theorem integral_eq_sum_openWordCell {h : CarpetPoints → ℝ} (hh : Integrable h carpetMeasure)
    (n : ℕ) : (∫ x, h x ∂carpetMeasure) =
      ∑ w : Fin n → Fin 8, ∫ x in openWordCell w, h x ∂carpetMeasure := by
  classical
  have h := integral_biUnion_finset (Finset.univ : Finset (Fin n → Fin 8))
    (fun w _ ↦ measurableSet_openWordCell w)
    (fun _ _ _ _ hne ↦ pairwise_disjoint_openWordCell n hne)
    (fun _ _ ↦ hh.integrableOn)
  simp only [Finset.mem_univ, iUnion_true, iUnion_openWordCell] at h
  have ha : ∀ᵐ x ∂carpetMeasure, x ∈ (carpetCellBoundary n)ᶜ :=
    measure_eq_zero_iff_ae_notMem.mp (carpetMeasure_carpetCellBoundary_eq_zero n)
  have he := Measure.restrict_eq_self_of_ae_mem ha
  rwa [he] at h

/-- Replace an ambient Lp class by its normalized cell averages. -/
noncomputable def cellAveraging (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (n : ℕ) :
    CarpetLp p →L[ℝ] CarpetLp p :=
  ∑ w : Fin n → Fin 8, (ambientWordMean p (List.ofFn w)).smulRight
    (indicatorConstLp (ENNReal.ofReal p) (measurableSet_openWordCell w) (measure_ne_top _ _) (1 : ℝ))

theorem cellAveraging_ae_eq_on_openWordCell {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (n : ℕ) (f : CarpetLp p) (w : Fin n → Fin 8) :
    ((cellAveraging p n f : CarpetLp p) : CarpetPoints → ℝ)
      =ᵐ[carpetMeasure.restrict (openWordCell w)]
        fun _ ↦ ambientWordMean p (List.ofFn w) f := by
  classical
  let m (v : Fin n → Fin 8) := ambientWordMean p (List.ofFn v) f
  let P (v : Fin n → Fin 8) : CarpetLp p :=
    indicatorConstLp (ENNReal.ofReal p) (measurableSet_openWordCell v) (measure_ne_top _ _) (1 : ℝ)
  have he : cellAveraging p n f = ∑ v : Fin n → Fin 8, m v • P v := by
    simp only [cellAveraging, sum_apply, ContinuousLinearMap.smulRight_apply, P, m]
  have hsum := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin n → Fin 8)) (fun v ↦ m v • P v)
  have hPt (v : Fin n → Fin 8) : ((m v • P v : CarpetLp p) : CarpetPoints → ℝ) =ᵐ[carpetMeasure]
        (fun x ↦ m v * (openWordCell v).indicator (fun _ ↦ (1 : ℝ)) x) := by
    exact (Lp.coeFn_smul (m v) (P v)).trans
      (indicatorConstLp_coeFn.mono fun _ h ↦ congrArg (fun t : ℝ ↦ m v * t) h)
  have hPts : ∀ᵐ x ∂carpetMeasure, ∀ v : Fin n → Fin 8,
      (m v • P v : CarpetLp p) x = m v * (openWordCell v).indicator (fun _ ↦ (1 : ℝ)) x :=
    ae_all_iff.mpr hPt
  rw [he]
  apply (ae_restrict_iff' (measurableSet_openWordCell w)).mpr
  filter_upwards [hsum, hPts] with x hx hpx hxw
  rw [hx, Finset.sum_apply]
  rw [Finset.sum_eq_single w]
  · rw [hpx w, indicator_of_mem hxw, mul_one]
  · intro v _ hne
    have h := disjoint_left.mp (pairwise_disjoint_openWordCell n hne.symm)
    rw [hpx v, indicator_of_notMem (h hxw), mul_zero]
  · simp

/-- The cell averaging projection is a contraction in the ambient Lp norm. -/
theorem norm_cellAveraging_le {p : ℝ} (hp : 1 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)]
    (n : ℕ) (f : CarpetLp p) : ‖cellAveraging p n f‖ ≤ ‖f‖ := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  let g := cellAveraging p n f
  have hint (f : CarpetLp p) : Integrable (fun x ↦ |f x| ^ p) carpetMeasure := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp₀.le] using
      (Lp.memLp f).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top
  have hc (w : Fin n → Fin 8) :
      (∫ x in openWordCell w, |g x| ^ p ∂carpetMeasure) ≤
        ∫ x in openWordCell w, |f x| ^ p ∂carpetMeasure := by
    have he := integral_congr_ae ((cellAveraging_ae_eq_on_openWordCell n f w).mono
      fun x hx ↦ congrArg (fun t : ℝ ↦ |t| ^ p) hx)
    change (∫ x in openWordCell w, |g x| ^ p ∂carpetMeasure) =
      ∫ _x in openWordCell w, |ambientWordMean p (List.ofFn w) f| ^ p ∂carpetMeasure at he
    rw [he, integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      carpetMeasure_openWordCell, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      smul_eq_mul, carpetMeasure_restrict_openWordCell]
    have hh := ambientWordMean_abs_rpow_le hp (List.ofFn w) f
    rw [List.length_ofFn] at hh
    have ha : 0 < (8 : ℝ) ^ n := by positivity
    rw [inv_pow, inv_mul_le_iff₀ ha]
    simpa only [mul_comm (8 ^ n)] using hh
  have h : ‖g‖ ^ p ≤ ‖f‖ ^ p := by
    rw [← integral_abs_rpow_eq_norm_rpow hp₀, ← integral_abs_rpow_eq_norm_rpow hp₀,
      integral_eq_sum_openWordCell (hint g) n, integral_eq_sum_openWordCell (hint f) n]
    exact Finset.sum_le_sum (fun w _ ↦ hc w)
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp₀).mp h

theorem ambientWordMean_continuousLp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (w : List (Fin 8)) (f : C(CarpetPoints, ℝ)) :
    ambientWordMean p w (continuousLp p f) = ∫ x, f (wordMap w x) ∂carpetMeasure := by
  rw [ambientWordMean_eq_integral]
  have he := (continuousLp_ae_eq p f).filter_mono
    (SelfSimilarPEnergy.quasiMeasurePreserving_wordMap w).absolutelyContinuous.ae_le
  rw [integral_congr_ae he]
  exact integral_map (continuous_wordMap w).measurable.aemeasurable f.continuous.aestronglyMeasurable

private theorem cellAveraging_tendsto_continuousLp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (f : C(CarpetPoints, ℝ)) :
    Tendsto (fun n ↦ cellAveraging p n (continuousLp p f)) atTop (𝓝 (continuousLp p f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _), fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, hosc⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous)
      (ε / 2) (half_pos hε)
  filter_upwards [tendsto_wordMap_radius.eventually_lt_const hδ] with n hn
  let u := continuousLp p f
  let g := cellAveraging p n u
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply norm_carpetLp_le_of_ae_bound _ (half_pos hε).le
  have hs : ∀ᵐ x ∂carpetMeasure, ∀ w : Fin n → Fin 8, x ∈ openWordCell w →
      g x = ambientWordMean p (List.ofFn w) u :=
    ae_all_iff.mpr fun w ↦ (ae_restrict_iff' (measurableSet_openWordCell w)).mp
      (cellAveraging_ae_eq_on_openWordCell n u w)
  filter_upwards [hs, Lp.coeFn_sub g u, continuousLp_ae_eq p f,
    measure_eq_zero_iff_ae_notMem.mp (carpetMeasure_carpetCellBoundary_eq_zero n)]
    with x hx hsub hu hxb
  obtain ⟨w, y, hy⟩ := exists_wordMap_range n x
  change ‖(g - u) x‖ ≤ _
  rw [hsub, Pi.sub_apply, hx w ⟨⟨y, hy⟩, hxb⟩, hu, Real.norm_eq_abs,
    ambientWordMean_continuousLp]
  apply SelfSimilarPEnergy.SelfSimilarComponent.abs_wordMean_sub_le
  intro z
  have hd := wordMap_dist_le n w (mem_range_self z) (show x ∈ range (wordMap (List.ofFn w)) from ⟨y, hy⟩)
  exact (show |f (wordMap (List.ofFn w) z) - f x| < ε / 2 from
    Real.dist_eq _ _ ▸ hosc (hd.trans_lt hn)).le

/-- The lifted cell means converge in Lp to every ambient function. -/
theorem cellAveraging_tendsto {p : ℝ} (hp : 1 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] (f : CarpetLp p) :
    Tendsto (fun n ↦ cellAveraging p n f) atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _), fun ε hε ↦ ?_⟩
  let L := ContinuousMap.toLp (E := ℝ) (ENNReal.ofReal p) carpetMeasure ℝ
  have hL (v : C(CarpetPoints, ℝ)) : L v = continuousLp p v := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp carpetMeasure v).trans (continuousLp_ae_eq p v).symm
  have hdense : DenseRange L :=
    ContinuousMap.toLp_denseRange ℝ carpetMeasure ℝ ENNReal.ofReal_ne_top
  obtain ⟨v, hv⟩ := hdense.exists_dist_lt f (show 0 < ε / 3 by positivity)
  let g := continuousLp p v
  have hg : ‖g - f‖ < ε / 3 := by
    rw [hL, dist_eq_norm, norm_sub_rev] at hv
    exact hv
  have h := tendsto_iff_norm_sub_tendsto_zero.mp (cellAveraging_tendsto_continuousLp (p := p) v)
  filter_upwards [h.eventually_lt_const (show 0 < ε / 3 by positivity)] with n hn
  let P := cellAveraging p n
  change ‖P f - f‖ < ε
  have h₁ : ‖P (f - g)‖ ≤ ‖g - f‖ :=
    (norm_cellAveraging_le hp n (f - g)).trans_eq (norm_sub_rev f g)
  have he : P f - f = P (f - g) + (P g - g) + (g - f) := by rw [map_sub]; abel
  rw [he]
  exact (norm_add_le _ _).trans_lt (by
    have hh := norm_add_le (P (f - g)) (P g - g)
    change ‖P g - g‖ < ε / 3 at hn
    linarith)

theorem cellAveraging_tendsto_of_tendsto {p : ℝ} (hp : 1 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)]
    {j : ℕ → ℕ} {u : ℕ → CarpetLp p} {f : CarpetLp p}
    (hj : Tendsto j atTop atTop) (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun n ↦ cellAveraging p (j n) (u n)) atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _), fun a ha ↦ ?_⟩
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp ((cellAveraging_tendsto hp f).comp hj)
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.mp hu).eventually_lt_const (half_pos ha),
    ht.eventually_lt_const (half_pos ha)] with n hn hfn
  let T := cellAveraging p (j n)
  change ‖T (u n) - f‖ < a
  have hb : ‖T (u n) - T f‖ ≤ ‖u n - f‖ := by
    rw [← map_sub]
    exact norm_cellAveraging_le hp _ _
  have he : T (u n) - f = (T (u n) - T f) + (T f - f) := by abel
  rw [he]
  exact (norm_add_le _ _).trans_lt (by
    change ‖T f - f‖ < a / 2 at hfn
    linarith)

end CarpetEnergy
