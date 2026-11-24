import CarpetRecurringGoodCells
import Mathlib.MeasureTheory.Measure.Support

/-!
# Selecting cells with nearly fixed directional densities

The directional densities are a measurable map into a countable product.
A point in the support of its pushforward over the recurring good set
has positive-mass neighborhoods specified by any finite set of
directions. Stopping among eligible cells concentrates any of those
neighborhoods at arbitrarily fine levels.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CarpetEnergy

theorem exists_directional_good_cells {I : Type*} [Countable I]
    (ν : Measure CarpetPoints) [IsFiniteMeasure ν] [ν.OuterRegular] [ν.InnerRegularCompactLTTop]
    (hnull : ν carpetAllCellBoundaries = 0) (hboundary : ν carpetOuterBoundary = 0)
    (A : Set CarpetPoints) (hA : MeasurableSet A) (hpos : 0 < ν A)
    (k : ℕ) (D : CarpetPoints → I → ℝ≥0∞) (hD : ∀ i, Measurable (fun x ↦ D x i))
    (L U : I → ℝ≥0∞) (hU : ∀ i, U i < ∞)
    (hbound : ∀ x ∈ A, ∀ i, L i ≤ D x i ∧ D x i ≤ U i) :
    ∃ α : ℝ≥0∞, 0 < α ∧ ∃ Θ : I → ℝ≥0∞, (∀ i, L i ≤ Θ i ∧ Θ i ≤ U i) ∧
      ∀ (J : Finset I) (ε : ℝ≥0∞), 0 < ε → ∀ M : ℕ,
        ∃ (C : Set CarpetPoints) (w : FiniteAddress),
          C ⊆ A ∧ MeasurableSet C ∧ M ≤ w.1 ∧
          (∀ x ∈ C, ∀ i ∈ J, D x i < Θ i + ε ∧ Θ i < D x i + ε) ∧
          0 < ν (range (wordMap (List.ofFn w.2))) ∧
          α * ν (wordCellUnion (cellNeighborhood w.2 k)) ≤ ν (range (wordMap (List.ofFn w.2))) ∧
          wordCellUnion (cellNeighborhood w.2 k) ⊆ carpetOuterBoundaryᶜ ∧
          ν (range (wordMap (List.ofFn w.2)) ∩ Cᶜ) ≤ ε * ν (range (wordMap (List.ofFn w.2))) := by
  obtain ⟨α, hα, B, hBA, hB, hposB, hrec⟩ :=
    exists_subset_recurring_good_cells ν hnull hboundary A hA hpos k
  let νD := (ν.restrict B).map D
  have hm : Measurable D := measurable_pi_iff.mpr hD
  have hνD : νD univ = ν B := by
    rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
  have hνD₀ : νD ≠ 0 := by
    intro h
    rw [h, zero_apply] at hνD
    exact hposB.ne' hνD.symm
  obtain ⟨Θ, hΘ⟩ := νD.nonempty_support hνD₀
  let K := Set.pi univ (fun i ↦ Icc (L i) (U i))
  have hK : IsClosed K := isClosed_set_pi (fun _ _ ↦ isClosed_Icc)
  have hνDK : νD Kᶜ = 0 := by
    rw [Measure.map_apply hm hK.isOpen_compl.measurableSet, Measure.restrict_apply
      (hm hK.isOpen_compl.measurableSet)]
    apply measure_mono_null (t := ∅) _ (measure_empty : ν ∅ = 0)
    intro x hx
    exact hx.1 (fun i _ ↦ hbound x (hBA hx.2) i)
  have hΘK : Θ ∈ K := by
    by_contra h
    exact (Measure.mem_support_iff_forall Θ |>.mp hΘ Kᶜ (hK.isOpen_compl.mem_nhds h)).ne' hνDK
  refine ⟨α, hα, Θ, fun i ↦ hΘK i (mem_univ _), fun J ε hε M ↦ ?_⟩
  let V : Set (I → ℝ≥0∞) := ⋂ i ∈ J, {y | y i < Θ i + ε ∧ Θ i < y i + ε}
  have hV : IsOpen V := by
    apply isOpen_biInter_finset
    intro i _
    exact (isOpen_lt (continuous_apply i) continuous_const).inter
      (isOpen_lt continuous_const ((show Continuous (fun y : I → ℝ≥0∞ ↦ y i) from continuous_apply i).add_const ε))
  have hΘV : Θ ∈ V := by
    apply mem_iInter₂.mpr
    intro i _
    have hfin := (hΘK i (mem_univ _)).2.trans_lt (hU i)
    exact ⟨ENNReal.lt_add_right hfin.ne hε.ne', ENNReal.lt_add_right hfin.ne hε.ne'⟩
  let C := B ∩ D ⁻¹' V
  have hC : MeasurableSet C := hB.inter (hm hV.measurableSet)
  have hposC : 0 < ν C := by
    have h := (Measure.mem_support_iff_forall Θ).mp hΘ V (hV.mem_nhds hΘV)
    rw [Measure.map_apply hm hV.measurableSet, Measure.restrict_apply (hm hV.measurableSet),
      inter_comm] at h
    exact h
  let G (w : FiniteAddress) : Prop :=
    0 < ν (range (wordMap (List.ofFn w.2))) ∧
      α * ν (wordCellUnion (cellNeighborhood w.2 k)) ≤ ν (range (wordMap (List.ofFn w.2))) ∧
      wordCellUnion (cellNeighborhood w.2 k) ⊆ carpetOuterBoundaryᶜ
  obtain ⟨w, hw, hG, hmass, hsmall⟩ := exists_good_cell_with_small_complement ν hnull C hC hposC
    G (fun x hx ↦ hrec x hx.1) ε hε M
  exact ⟨C, w, inter_subset_left.trans hBA, hC, hw, fun _ hx i hi ↦ mem_iInter₂.mp hx.2 i hi,
    hmass, hG.2.1, hG.2.2, hsmall⟩

end CarpetEnergy
