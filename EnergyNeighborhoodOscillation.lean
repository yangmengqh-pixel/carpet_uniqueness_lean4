import EnergyNeighborhoodHarnackEstimate
import EssentialOscillation

/-!
# Oscillation contraction on cell neighborhoods

The neighborhood Harnack inequality contracts the essential
oscillation from the radius-three neighborhood to the radius-two
neighborhood.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem ae_cellNeighborhood_shift_harnack {H : ℝ} (hHar : E.HasNeighborhoodHarnack H)
    {n : ℕ} (w : Fin n → Fin 8) (hw : Disjoint (wordCellUnion (cellNeighborhood w 3)) carpetOuterBoundary)
    (f : E.domain) (hf : E.MinimizesWithExterior (wordCellUnion (cellNeighborhood w 3)ᶜ) f)
    (c : ℝ) (hc : ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 3)),
      0 ≤ (f : CarpetLp p) x + c) :
    ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 2)),
      ∀ᵐ y ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 2)),
        (f : CarpetLp p) x + c ≤ H * ((f : CarpetLp p) y + c) := by
  let a : E.domain := ⟨constantLp p c, E.constant_mem c⟩
  let g := f + a
  have hcoe : (g : CarpetLp p) =ᵐ[carpetMeasure] fun x ↦ (f : CarpetLp p) x + c := by
    filter_upwards [Lp.coeFn_add (f : CarpetLp p) (a : CarpetLp p),
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c] with x hx ha
    have hx' : (g : CarpetLp p) x = (f : CarpetLp p) x + (a : CarpetLp p) x := hx
    have ha' : (a : CarpetLp p) x = c := ha
    rw [hx', ha']
  have hNonneg : ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 3)),
      0 ≤ (g : CarpetLp p) x := by
    filter_upwards [hc, hcoe.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hg
    rwa [hg]
  have hh := hHar n w hw g (MinimizesWithExterior.add_constant E hf c) hNonneg
  have hg := hcoe.filter_mono (ae_mono (Measure.restrict_le_self
    (s := wordCellUnion (cellNeighborhood w 2))))
  filter_upwards [hh, hg] with x hx hgx
  filter_upwards [hx, hg] with y hy hgy
  exact hgx ▸ hgy ▸ hy

set_option maxHeartbeats 1000000 in
/-- The single-step oscillation estimate used in Proposition 4.9. -/
theorem neighborhood_essOsc_le_of_harnack {H : ℝ} (hH : 1 ≤ H)
    (hHar : E.HasNeighborhoodHarnack H) {n : ℕ} (w : Fin n → Fin 8)
    (hw : Disjoint (wordCellUnion (cellNeighborhood w 3)) carpetOuterBoundary)
    (f : E.domain) (hf : E.MinimizesWithExterior (wordCellUnion (cellNeighborhood w 3)ᶜ) f)
    {a b : ℝ} (h : ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 3)),
      (f : CarpetLp p) x ∈ Icc a b) :
    let μ := carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 2))
    essSup (f : CarpetLp p) μ - essInf (f : CarpetLp p) μ ≤ ((H - 1) / (H + 1)) * (b - a) := by
  let V := wordCellUnion (cellNeighborhood w 2)
  let μ := carpetMeasure.restrict V
  have hmass : carpetMeasure V ≠ 0 := by
    have hs : range (wordMap (List.ofFn w)) ⊆ V :=
      fun _ hx ↦ mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨self_mem_cellNeighborhood w 2, hx⟩⟩
    have hle := measure_mono (μ := carpetMeasure) hs
    rw [carpetMeasure_range_wordMap] at hle
    exact ne_of_gt (lt_of_lt_of_le
      (pos_iff_ne_zero.mpr (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp)))) hle)
  have : NeZero μ := ⟨fun he ↦ hmass (by
    simpa only [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter, zero_apply] using
      congrArg (fun m : Measure CarpetPoints ↦ m univ) he)⟩
  have hV : V ⊆ wordCellUnion (cellNeighborhood w 3) :=
    wordCellUnion_mono (cellNeighborhood_subset_succ w)
  have hlo := E.ae_cellNeighborhood_shift_harnack hHar w hw f hf (-a)
    (h.mono fun x hx ↦ by linarith only [hx.1])
  have hneg := Lp.coeFn_neg (f : CarpetLp p)
  have hhi := E.ae_cellNeighborhood_shift_harnack hHar w hw (-f) (MinimizesWithExterior.neg E hf) b
    (by
      filter_upwards [h, hneg.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hx'
      have hn : ((-f : E.domain) : CarpetLp p) x = -((f : CarpetLp p) x) := hx'
      rw [hn]
      linarith only [hx.2])
  change essSup (f : CarpetLp p) μ - essInf (f : CarpetLp p) μ ≤ _
  apply essSup_sub_essInf_le_of_ae_harnack (μ := μ) (Lp.stronglyMeasurable _).measurable hH
    (h.filter_mono (ae_mono (Measure.restrict_mono hV le_rfl)))
  · simpa only [sub_eq_add_neg] using hlo
  · have hneg' := hneg.filter_mono (ae_mono (Measure.restrict_le_self (s := V)))
    filter_upwards [hhi, hneg'] with x hx nx
    filter_upwards [hx, hneg'] with y hy ny
    have nx' : ((-f : E.domain) : CarpetLp p) x = -((f : CarpetLp p) x) := nx
    have ny' : ((-f : E.domain) : CarpetLp p) y = -((f : CarpetLp p) y) := ny
    rw [nx', ny'] at hy
    simpa only [sub_eq_add_neg, add_comm b] using hy

end CarpetEnergy.SelfSimilarPEnergy
