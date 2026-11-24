import EnergyLocalHarmonicCauchy
import EnergyBoundaryCovariance

/-!
# Graph convergence on an interior harmonic cell

Once harmonic profiles on a fixed neighborhood are uniformly Cauchy,
the central-cell pullbacks converge in the complete graph norm and
their uniform limit represents the graph limit.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1000000 in
theorem exists_graph_limit_of_uniform_cauchy_on_harmonic_cell
    {U : Set CarpetPoints} (hU : IsOpen U) (w : List (Fin 8))
    (hw : range (wordMap w) ⊆ U) (f : ℕ → E.continuousCore)
    (hharm : ∀ n, E.IsHarmonicOn U (f n)) {M : ℝ}
    (hM : ∀ n, E.rootSeminorm (E.continuousCoreToDomain (f n)) ≤ M)
    (hclose : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m →
      ∀ x ∈ range (wordMap w), |(f n).val x - (f m).val x| ≤ δ) :
    ∃ (g : E.domain) (u : C(CarpetPoints, ℝ)),
      continuousLp p u = (g : CarpetLp p) ∧
      Tendsto (fun n ↦ E.toGraph (E.pullbackWord w (E.continuousCoreToDomain (f n))))
        atTop (𝓝 (E.toGraph g)) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  let d (n : ℕ) := E.wordPullbackCore w (f n)
  let z (n : ℕ) : E.GraphDomain := E.toGraph (E.continuousCoreToDomain (d n))
  let V := range (wordMap w)
  have hV : IsClosed V := (isCompact_range (continuous_wordMap w)).isClosed
  have hmass := E.local_energy_cauchy_of_uniform_cauchy hU hV hw f hharm hM hclose
  have hLp (u : C(CarpetPoints, ℝ)) : ‖continuousLp p u‖ ≤ ‖u‖ := by
    apply norm_carpetLp_le_of_ae_bound _ (norm_nonneg _)
    filter_upwards [continuousLp_ae_eq p u] with x hx
    rw [hx]
    exact u.norm_coe_le_norm x
  have hfu : CauchySeq (fun n ↦ (d n).val) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hclose (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn m hm ↦ ?_⟩
    rw [dist_eq_norm]
    have hu : ‖(d n).val - (d m).val‖ ≤ ε / 2 := by
      apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
      intro x
      change ‖(f n).val (wordMap w x) - (f m).val (wordMap w x)‖ ≤ ε / 2
      rw [Real.norm_eq_abs]
      exact hN n m hn hm (wordMap w x) (mem_range_self x)
    exact hu.trans_lt (half_lt_self hε)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hfu
  have hgraph : CauchySeq z := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hp := zero_lt_one.trans E.one_lt_p
    let δ := ε / 3
    have hδ : 0 < δ := by positivity
    let c := E.scalingFactor ^ w.length
    have hc : 0 < c := pow_pos (E.isScalingFactor_scalingFactor.1) _
    obtain ⟨N, hN⟩ := hmass (c * δ ^ p) (mul_pos hc (Real.rpow_pos_of_pos hδ _))
    obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hfu δ hδ
    refine ⟨max N K, fun n hn m hm ↦ ?_⟩
    let v := E.continuousCoreToDomain (d n - d m)
    have hdist := hK n ((le_max_right _ _).trans hn) m ((le_max_right _ _).trans hm)
    rw [dist_eq_norm] at hdist
    have hvL : ‖(v : CarpetLp p)‖ ≤ δ :=
      (hLp ((d n).val - (d m).val)).trans hdist.le
    have hmul := hN n m ((le_max_left _ _).trans hn) ((le_max_left _ _).trans hm)
    have he : E.pullbackWord w (E.continuousCoreToDomain (f n - f m)) = v := by
      rw [← E.continuousCoreToDomain_wordPullbackCore, E.wordPullbackCore_sub]
    have hcell : (E.energyMeasure (E.continuousCoreToDomain (f n - f m))).real V =
        c * (E.energy v : ℝ) := by
      unfold Measure.real
      change (E.energyMeasure (E.continuousCoreToDomain (f n - f m)) (range (wordMap w))).toReal = _
      rw [E.energyMeasure_range_word, he, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal E.isScalingFactor_scalingFactor.1.le, ENNReal.coe_toReal]
    change (E.energyMeasure (E.continuousCoreToDomain (f n - f m))).real V < c * δ ^ p at hmul
    rw [hcell] at hmul
    have hvE := lt_of_mul_lt_mul_left hmul hc.le
    have htotal : (E.energy v : ℝ) + ‖(v : CarpetLp p)‖ ^ p < ε ^ p := by
      have hnorm := Real.rpow_le_rpow (norm_nonneg _) hvL hp.le
      have h₃ : (2 : ℝ) < (3 : ℝ) ^ p := (by norm_num : (2 : ℝ) < 3).trans_le
        (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) E.one_lt_p.le)
      have h₃δ := mul_lt_mul_of_pos_right h₃ (Real.rpow_pos_of_pos hδ p)
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hδ.le,
        show (3 : ℝ) * δ = ε by dsimp only [δ]; ring] at h₃δ
      linarith only [hvE, hnorm, h₃δ]
    rw [dist_eq_norm]
    have hv : z n - z m = E.toGraph v := by
      change E.toGraph (E.continuousCoreToDomain (d n) - E.continuousCoreToDomain (d m)) = _
      dsimp only [v]
      rw [map_sub]
    rw [hv, E.norm_toGraph, E.graphSeminorm_apply, energyGraphNorm]
    calc
      _ < (ε ^ p) ^ p⁻¹ := Real.rpow_lt_rpow
        (add_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)) htotal (inv_pos.mpr hp)
      _ = ε := Real.rpow_rpow_inv hε.le hp.ne'
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hgraph
  let g := E.graphToDomain y
  have hg : Tendsto (fun n ↦ continuousLp p (d n).val) atTop (𝓝 (g : CarpetLp p)) :=
    (E.graphInclusion.continuous.tendsto y).comp hy
  have hT : Continuous (continuousLpLinear p) := by
    let T := (continuousLpLinear p).mkContinuous 1 (fun v ↦ by rw [one_mul]; exact hLp v)
    exact T.continuous
  have hgu : Tendsto (fun n ↦ continuousLp p (d n).val) atTop (𝓝 (continuousLp p u)) :=
    (hT.tendsto u).comp hu
  refine ⟨g, u, tendsto_nhds_unique hgu hg, ?_⟩
  simpa only [z, d, g, toGraph, graphToDomain, E.continuousCoreToDomain_wordPullbackCore] using hy

end CarpetEnergy.SelfSimilarPEnergy
