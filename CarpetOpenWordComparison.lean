import CarpetNeighborhoodMass

/-!
# Comparing measures on open sets by their cell masses
-/

open Filter Metric MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

theorem measure_open_le_of_wordCell_le (μ ν : Measure CarpetPoints) [IsFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] (hν : ∀ n, ν (carpetCellBoundary n) = 0)
    (h : ∀ w : List (Fin 8), μ (range (wordMap w)) ≤ ν (range (wordMap w)))
    {U : Set CarpetPoints} (hU : IsOpen U) : μ U ≤ ν U := by
  classical
  by_contra! hlt
  obtain ⟨C, hCU, hC, hmass⟩ := hU.measurableSet.exists_lt_isCompact_of_ne_top
    (measure_ne_top μ U) hlt
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_thickening_subset_open hU hCU
  obtain ⟨n, hn⟩ := (tendsto_wordMap_radius.eventually_lt_const hδ).exists
  let S := Finset.univ.filter (fun w : Fin n → Fin 8 ↦ range (wordMap (List.ofFn w)) ⊆ U)
  have hcover : C ⊆ wordCellUnion S := by
    intro x hx
    obtain ⟨w, hw⟩ := exists_wordMap_range n x
    have hs : w ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy ↦ hthick ?_⟩
      exact mem_thickening_iff.mpr ⟨x, hx, (wordMap_dist_le n w hy hw).trans_lt hn⟩
    exact mem_iUnion₂.mpr ⟨w, hs, hw⟩
  have hS : wordCellUnion S ⊆ U := by
    intro x hx
    obtain ⟨w, hw, hmem⟩ := mem_iUnion₂.mp hx
    exact (Finset.mem_filter.mp hw).2 hmem
  have hbound : μ C ≤ ν U := calc
    _ ≤ μ (wordCellUnion S) := measure_mono hcover
    _ ≤ ∑ w ∈ S, μ (range (wordMap (List.ofFn w))) := measure_biUnion_finset_le S _
    _ ≤ ∑ w ∈ S, ν (range (wordMap (List.ofFn w))) := Finset.sum_le_sum (fun w _ ↦ h _)
    _ = ν (wordCellUnion S) := (measure_wordCellUnion ν (hν n) S).symm
    _ ≤ _ := measure_mono hS
  exact hmass.not_ge hbound

end CarpetEnergy
