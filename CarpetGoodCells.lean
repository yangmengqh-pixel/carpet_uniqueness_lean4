import CarpetNeighborhoodMass
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Interior cells of high relative mass

A compact set of positive mass and a small open enlargement replace
pointwise martingale differentiation in the cell selection. The
neighborhood budget allows the choice to avoid small local mass ratios.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

theorem isClosed_carpetOuterBoundary : IsClosed carpetOuterBoundary := by
  apply isClosed_iUnion_of_finite
  intro j
  apply isClosed_iUnion_of_finite
  intro a
  exact isClosed_eq
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) j).comp continuous_subtypeVal) continuous_const

/-- Large levels contain interior cells with positive mass, uniform
comparison to their neighborhood mass, and arbitrarily small relative
mass outside a given positive-measure set. -/
theorem exists_good_interior_cells (ν : Measure CarpetPoints) [IsFiniteMeasure ν]
    [ν.OuterRegular] [ν.InnerRegularCompactLTTop] (hprob : ν univ = 1)
    (hboundary : ν carpetOuterBoundary = 0) (hnull : ∀ n, ν (carpetCellBoundary n) = 0)
    (A : Set CarpetPoints) (hA : MeasurableSet A) (hpos : 0 < ν A) (k : ℕ) :
    ∃ a : ℝ≥0∞, 0 < a ∧ ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∃ w : Fin n → Fin 8,
      0 < ν (range (wordMap (List.ofFn w))) ∧
      a * ν (wordCellUnion (cellNeighborhood w k)) ≤ ν (range (wordMap (List.ofFn w))) ∧
      wordCellUnion (cellNeighborhood w k) ⊆ carpetOuterBoundaryᶜ ∧
      ν (range (wordMap (List.ofFn w)) ∩ Aᶜ) ≤ ENNReal.ofReal ε * ν (range (wordMap (List.ofFn w))) := by
  classical
  let A' := A \ carpetOuterBoundary
  have hA' : MeasurableSet A' := hA.diff measurableSet_carpetOuterBoundary
  have hpos' : 0 < ν A' := (measure_sdiff_null hboundary).symm ▸ hpos
  obtain ⟨B, hBA', hB, hBpos⟩ := hA'.exists_lt_isCompact_of_ne_top (measure_ne_top ν A') hpos'
  let d := (ν B).toReal
  have hd : 0 < d := ENNReal.toReal_pos hBpos.ne' (measure_ne_top _ _)
  let r : ℕ := (2 * k + 1) ^ 2
  have hr : 0 < (r : ℝ) := by dsimp only [r]; positivity
  let α := d / (4 * (r : ℝ))
  have hα : 0 < α := div_pos hd (by positivity)
  refine ⟨ENNReal.ofReal α, ENNReal.ofReal_pos.mpr hα, fun ε hε ↦ ?_⟩
  obtain ⟨U, hAU, hU, hUD⟩ := hA.exists_isOpen_sdiff_lt (measure_ne_top ν A)
    (ENNReal.ofReal_pos.mpr (show 0 < ε * (d / 2) by positivity)).ne'
  have hBO : B ⊆ U ∩ carpetOuterBoundaryᶜ := fun x hx ↦
    ⟨hAU (hBA' hx).1, (hBA' hx).2⟩
  obtain ⟨δ, hδ, hδU⟩ := hB.exists_thickening_subset_open
    (hU.inter isClosed_carpetOuterBoundary.isOpen_compl) hBO
  have hlim : Tendsto
      (fun n : ℕ ↦ ((k : ℝ) + 1) * ((1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_wordMap_radius.const_mul ((k : ℝ) + 1)
  filter_upwards [hlim.eventually_lt_const hδ] with n hn
  let W := Fin n → Fin 8
  let K (w : W) := range (wordMap (List.ofFn w))
  let J (w : W) := wordCellUnion (cellNeighborhood w k)
  let Bad := Finset.univ.filter (fun w : W ↦ ν (K w) < ENNReal.ofReal α * ν (J w))
  let S := Finset.univ.filter (fun w : W ↦ (K w ∩ B).Nonempty ∧ w ∉ Bad)
  have hSarea (w : W) (hw : w ∈ S) : J w ⊆ U ∩ carpetOuterBoundaryᶜ := by
    obtain ⟨x, hx, hxB⟩ := (Finset.mem_filter.mp hw).2.1
    intro y hy
    obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
    have hdist := dist_le_of_mem_cellNeighborhood hv hx hyv
    exact hδU (mem_thickening_iff.mpr ⟨x, hxB, (show dist y x ≤ _ from
      (dist_comm y x).le.trans hdist).trans_lt hn⟩)
  have hSK (w : W) (hw : w ∈ S) : K w ⊆ U := by
    intro x hx
    exact (hSarea w hw (mem_iUnion₂.mpr ⟨w, self_mem_cellNeighborhood w k, hx⟩)).1
  have hcover : B ⊆ wordCellUnion Bad ∪ wordCellUnion S := by
    intro x hx
    obtain ⟨w, hw⟩ := exists_wordMap_range n x
    by_cases hbad : w ∈ Bad
    · exact Or.inl (mem_iUnion₂.mpr ⟨w, hbad, hw⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨⟨x, hw, hx⟩, hbad⟩⟩, hw⟩)
  have hbadMass : (ν (wordCellUnion Bad)).toReal ≤ d / 4 := by
    have h := measure_bad_cell_ratio_le (n := n) ν (hnull n) k (ENNReal.ofReal α)
    rw [hprob, mul_one] at h
    change ν (wordCellUnion Bad) ≤ ENNReal.ofReal α * (r : ℝ≥0∞) at h
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top r)) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le, ENNReal.toReal_natCast] at ht
    have he : α * (r : ℝ) = d / 4 := by
      dsimp only [α]
      field_simp [hr.ne']
    exact ht.trans_eq he
  have hSmass : d / 2 ≤ (ν (wordCellUnion S)).toReal := by
    have h := (measure_mono (μ := ν) hcover).trans (measure_union_le _ _)
    have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at ht
    change d ≤ _ at ht
    linarith
  have hsum : ν (wordCellUnion S) = ∑ w ∈ S, ν (K w) := measure_wordCellUnion ν (hnull n) S
  have hsumA : ν (wordCellUnion S ∩ Aᶜ) = ∑ w ∈ S, ν (K w ∩ Aᶜ) :=
    measure_wordCellUnion_inter ν (hnull n) S hA.compl
  have hsmall : ν (wordCellUnion S ∩ Aᶜ) < ENNReal.ofReal (ε * (d / 2)) := by
    apply lt_of_le_of_lt (measure_mono ?_) hUD.2
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hx.1
    exact ⟨hSK w hw hxw, hx.2⟩
  have hsel : ∃ w ∈ S, 0 < ν (K w) ∧ ν (K w ∩ Aᶜ) ≤ ENNReal.ofReal ε * ν (K w) := by
    by_contra! h
    have hle (w : W) (hw : w ∈ S) : ENNReal.ofReal ε * ν (K w) ≤ ν (K w ∩ Aᶜ) := by
      by_cases hz : ν (K w) = 0
      · rw [hz, mul_zero]
        exact bot_le
      exact (h w hw (pos_iff_ne_zero.mpr hz)).le
    have h' : ENNReal.ofReal ε * ν (wordCellUnion S) ≤ ν (wordCellUnion S ∩ Aᶜ) := by
      rw [hsum, hsumA, Finset.mul_sum]
      exact Finset.sum_le_sum hle
    have h'' : ENNReal.ofReal (d / 2) ≤ ν (wordCellUnion S) :=
      (ENNReal.ofReal_le_ofReal hSmass).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))
    rw [ENNReal.ofReal_mul hε.le] at hsmall
    exact hsmall.not_ge ((mul_le_mul' le_rfl h'').trans h')
  obtain ⟨w, hw, hwm, he⟩ := hsel
  have hgood := (Finset.mem_filter.mp hw).2.2
  have hratio : ENNReal.ofReal α * ν (J w) ≤ ν (K w) := by
    apply le_of_not_gt
    intro h
    exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  exact ⟨w, hwm, hratio, (hSarea w hw).trans inter_subset_right, he⟩

end CarpetEnergy
