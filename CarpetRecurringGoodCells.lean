import CarpetStoppingCells
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Recurring interior cells with good neighborhood ratios

The measure of the set of points eventually trapped in bad cells is
bounded by the uniform budget for one level. A fixed positive subset
therefore admits arbitrarily fine good cells at every point.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CarpetEnergy

/-- A positive subset of a given set where fine interior cells with one
uniform mass ratio recur. The comparison constant is common to every
positive-measure subset subsequently used for stopping. -/
theorem exists_subset_recurring_good_cells (ν : Measure CarpetPoints) [IsFiniteMeasure ν]
    (hnull : ν carpetAllCellBoundaries = 0) (hboundary : ν carpetOuterBoundary = 0)
    (A : Set CarpetPoints) (hA : MeasurableSet A) (hpos : 0 < ν A) (k : ℕ) :
    ∃ α : ℝ≥0∞, 0 < α ∧ ∃ B ⊆ A, MeasurableSet B ∧ 0 < ν B ∧
      ∀ x ∈ B, ∀ N : ℕ, ∃ w : FiniteAddress, N ≤ w.1 ∧
        (0 < ν (range (wordMap (List.ofFn w.2))) ∧
          α * ν (wordCellUnion (cellNeighborhood w.2 k)) ≤ ν (range (wordMap (List.ofFn w.2))) ∧
          wordCellUnion (cellNeighborhood w.2 k) ⊆ carpetOuterBoundaryᶜ) ∧
        x ∈ cleanWordCell w := by
  classical
  let R : ℝ≥0∞ := (((2 * k + 1) ^ 2 : ℕ) : ℝ≥0∞) * ν univ
  have hR₀ : R ≠ 0 := by
    apply (ENNReal.mul_pos (by positivity) (hpos.trans_le (measure_mono (subset_univ _))).ne').ne'
  have hR₁ : R ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)
  let α := (ν A / 2) / R
  have hα : 0 < α := ENNReal.div_pos
    (ENNReal.div_ne_zero.mpr ⟨hpos.ne', by norm_num⟩) hR₁
  have hαR : α * R = ν A / 2 := ENNReal.div_mul_cancel hR₀ hR₁
  let badLevel (n : ℕ) := wordCellUnion (Finset.univ.filter (fun w : Fin n → Fin 8 ↦
    ν (range (wordMap (List.ofFn w))) < α * ν (wordCellUnion (cellNeighborhood w k))))
  let badTail (N : ℕ) := ⋂ n : ℕ, ⋂ _ : N ≤ n, badLevel n
  let bad := ⋃ N : ℕ, badTail N
  have hMono : Monotone badTail := by
    intro n m hnm x hx
    simp only [badTail, mem_iInter] at hx ⊢
    exact fun j hj ↦ hx j (hnm.trans hj)
  have hbad : ν bad ≤ ν A / 2 := by
    unfold bad
    rw [hMono.measure_iUnion]
    apply iSup_le
    intro N
    have hsub : badTail N ⊆ badLevel N := fun x hx ↦
      mem_iInter.mp (mem_iInter.mp hx N) le_rfl
    have hn : ν (carpetCellBoundary N) = 0 := measure_mono_null (subset_iUnion _ N) hnull
    exact (measure_mono hsub).trans ((measure_bad_cell_ratio_le ν hn k α).trans_eq hαR)
  have hbadMeas : MeasurableSet bad :=
    MeasurableSet.iUnion fun _ ↦ MeasurableSet.iInter fun _ ↦
      MeasurableSet.iInter fun _ ↦ measurableSet_wordCellUnion _
  let Z (n : ℕ) := ⋃ w : Fin n → Fin 8, ⋃ _ : ν (range (wordMap (List.ofFn w))) = 0,
    range (wordMap (List.ofFn w))
  let Zall := ⋃ n, Z n
  have hZ : ν Zall = 0 := by
    apply measure_iUnion_null
    intro n
    apply measure_iUnion_null
    intro w
    exact measure_iUnion_null fun hz ↦ hz
  have hZmeas : MeasurableSet Zall :=
    MeasurableSet.iUnion fun _ ↦ MeasurableSet.iUnion fun _ ↦
      MeasurableSet.iUnion fun _ ↦ (measurableEmbedding_wordMap _).measurableSet_range
  let M := carpetAllCellBoundaries ∪ carpetOuterBoundary ∪ Zall
  have hM : ν M = 0 := measure_union_null (measure_union_null hnull hboundary) hZ
  let B := (A \ bad) \ M
  have hB : MeasurableSet B :=
    (hA.diff hbadMeas).diff ((measurableSet_carpetAllCellBoundaries.union
      measurableSet_carpetOuterBoundary).union hZmeas)
  have hposB : 0 < ν B := by
    rw [measure_sdiff_null hM]
    by_contra! h'
    have hz : ν (A \ bad) = 0 := nonpos_iff_eq_zero.mp h'
    have hs : A ⊆ (A \ bad) ∪ bad := subset_sdiff_union A bad
    have hle := (measure_mono (μ := ν) hs).trans (measure_union_le _ _)
    rw [hz, zero_add] at hle
    have hlt := ENNReal.half_lt_self hpos.ne' (measure_ne_top ν A)
    exact hlt.not_ge (hle.trans hbad)
  refine ⟨α, hα, B, sdiff_subset.trans sdiff_subset, hB, hposB, ?_⟩
  intro x hx N
  have hxbad : x ∉ bad := hx.1.2
  have hxboundary : x ∈ carpetOuterBoundaryᶜ := fun h ↦ hx.2 (Or.inl (Or.inr h))
  have hxAll : x ∉ carpetAllCellBoundaries := fun h ↦ hx.2 (Or.inl (Or.inl h))
  have hxZ : x ∉ Zall := fun h ↦ hx.2 (Or.inr h)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_carpetOuterBoundary.isOpen_compl x hxboundary
  have ht : Tendsto (fun n : ℕ ↦ ((k : ℝ) + 1) *
      ((1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_wordMap_radius.const_mul ((k : ℝ) + 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_lt_const hr)
  have hex : ∃ n ≥ max N N₀, x ∉ badLevel n := by
    by_contra! h
    exact hxbad (mem_iUnion.mpr ⟨max N N₀, by simpa only [badTail, mem_iInter] using h⟩)
  obtain ⟨n, hn, hnbad⟩ := hex
  obtain ⟨w, hw⟩ := exists_wordMap_range n x
  refine ⟨⟨n, w⟩, (le_max_left N N₀).trans hn, ⟨?_, ?_, ?_⟩, hw, hxAll⟩
  · apply pos_iff_ne_zero.mpr
    intro hz
    exact hxZ (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hz, hw⟩⟩⟩)
  · apply le_of_not_gt
    intro hlt
    exact hnbad (mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, hw⟩)
  · intro y hy
    obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
    apply hball
    rw [Metric.mem_ball, dist_comm]
    exact (dist_le_of_mem_cellNeighborhood hv hw hyv).trans_lt
      (hN₀ n ((le_max_right N N₀).trans hn))

end CarpetEnergy
