import EnergyMorrey
import EnergyFoldingAmplification
import CarpetNeighborhoodRescaling
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Uniform compactness of graph-bounded families in the Morrey regime
-/

open Filter Function MeasureTheory Set
open scoped Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1000000 in
/-- When the renormalization factor exceeds one, every graph-bounded
continuous sequence has a uniformly converging subsequence. -/
theorem exists_uniform_subseq_of_graph_bounded_morrey (hρ : 1 < E.scalingFactor)
    (f : ℕ → E.continuousCore) {R : ℝ}
    (hR : ∀ n, E.graphSeminorm (E.continuousCoreToDomain (f n)) ≤ R) :
    ∃ (j : ℕ → ℕ) (u : C(CarpetPoints, ℝ)), StrictMono j ∧
      Tendsto (fun n ↦ (f (j n)).val) atTop (𝓝 u) := by
  classical
  have hp := zero_lt_one.trans E.one_lt_p
  have hρ₀ := zero_lt_one.trans hρ
  have hR0 : 0 ≤ R := (apply_nonneg E.graphSeminorm _).trans (hR 0)
  have henergy (k : ℕ) : (E.energy (E.continuousCoreToDomain (f k)) : ℝ) ≤ R ^ p := by
    let u := E.continuousCoreToDomain (f k)
    have hroot : E.rootSeminorm u ≤ R := (E.rootSeminorm_le_graphSeminorm u).trans (hR k)
    have he := Real.rpow_le_rpow (apply_nonneg E.rootSeminorm u) hroot hp.le
    rw [E.rootSeminorm_apply, Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'] at he
    exact he
  obtain ⟨D, hD, hDnorm⟩ := E.exists_uniform_norm_le_graphSeminorm hρ
  obtain ⟨C, hC, hosc⟩ := E.exists_cell_oscillation_bound hρ
  let e := ContinuousMap.isometryEquivBoundedOfCompact CarpetPoints ℝ
  let g (n : ℕ) := e (f n).val
  let A := range g
  have hvalues (v : BoundedContinuousFunction CarpetPoints ℝ) (x : CarpetPoints) (hv : v ∈ A) :
      v x ∈ Icc (-(D * R)) (D * R) := by
    obtain ⟨k, rfl⟩ := hv
    change (f k).val x ∈ Icc (-(D * R)) (D * R)
    apply abs_le.mp
    have hh : |(f k).val x| ≤ ‖(f k).val‖ := by
      rw [← Real.norm_eq_abs]
      exact (f k).val.norm_coe_le_norm x
    exact hh.trans ((hDnorm (f k).val (f k).property).trans
      (mul_le_mul_of_nonneg_left (hR k) hD.le))
  have hdec : Tendsto (fun n : ℕ ↦ (C * R ^ p) * E.scalingFactor⁻¹ ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hρ₀.le)
        (inv_lt_one_of_one_lt₀ hρ)).const_mul (C * R ^ p)
  have heq : Equicontinuous ((↑) : A → CarpetPoints → ℝ) := by
    intro x
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := eventually_atTop.mp
      (hdec.eventually_lt_const (Real.rpow_pos_of_pos hε p))
    let B := (Finset.univ : Finset (Fin n → Fin 8)).filter
      (fun w ↦ x ∉ range (wordMap (List.ofFn w)))
    let O := (wordCellUnion B)ᶜ
    have hx : x ∈ O := by
      intro hx
      obtain ⟨w, hw⟩ := mem_iUnion.mp hx
      obtain ⟨hB, hw⟩ := mem_iUnion.mp hw
      exact (Finset.mem_filter.mp hB).2 hw
    filter_upwards [(isClosed_wordCellUnion B).isOpen_compl.mem_nhds hx] with y hy
    rintro ⟨v, ⟨k, rfl⟩⟩
    obtain ⟨w, hw⟩ := exists_wordMap_range n y
    have hxw : x ∈ range (wordMap (List.ofFn w)) := by
      by_contra h
      exact hy (mem_iUnion.mpr ⟨w, mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hw⟩⟩)
    obtain ⟨a, ha⟩ := hxw
    obtain ⟨b, hb⟩ := hw
    change dist ((f k).val x) ((f k).val y) < ε
    rw [← ha, ← hb, Real.dist_eq]
    apply (Real.rpow_lt_rpow_iff (abs_nonneg _) hε.le hp).mp
    let u := E.continuousCoreToDomain (f k)
    have hmass : ((E.energyMeasure u) (range (wordMap (List.ofFn w)))).toReal ≤ R ^ p := by
      refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))).trans ?_
      rw [E.energyMeasure_univ, ENNReal.coe_toReal]
      exact henergy k
    have ho := hosc (f k).val (f k).property (List.ofFn w) a b
    rw [List.length_ofFn] at ho
    have ho' := ho.trans (mul_le_mul_of_nonneg_left hmass (by positivity :
      0 ≤ C * (E.scalingFactor ^ n)⁻¹))
    rw [← inv_pow, mul_right_comm] at ho'
    exact ho'.trans_lt (hn n le_rfl)
  have hc := BoundedContinuousFunction.arzela_ascoli (Icc (-(D * R)) (D * R)) isCompact_Icc A
    hvalues heq
  obtain ⟨u, _, j, hj, hlim⟩ := hc.tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n) : ∀ n, g n ∈ closure A)
  refine ⟨j, e.symm u, hj, ?_⟩
  have ht := (e.symm.isometry.continuous.tendsto u).comp hlim
  change Tendsto (fun n ↦ e.symm (e (f (j n)).val)) atTop (𝓝 (e.symm u)) at ht
  simpa only [Function.comp_apply, g, IsometryEquiv.symm_apply_apply] using ht

end CarpetEnergy.SelfSimilarPEnergy
