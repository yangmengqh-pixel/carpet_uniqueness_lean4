import CarpetNeighborhoodMass
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Riemann sums for boundary-null measures on the carpet
-/

open Filter MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

/-- Word-cell Riemann sums converge for each continuous integrand
when all cell overlaps are null. The sample points can be any fixed
profile point transported into each cell. -/
theorem tendsto_wordCell_riemannSum (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (hμ : ∀ n, μ (carpetCellBoundary n) = 0) (φ : C(CarpetPoints, ℝ)) (z : CarpetPoints) :
    Tendsto (fun n : ℕ ↦ ∑ w : Fin n → Fin 8,
      φ (wordMap (List.ofFn w) z) * μ.real (range (wordMap (List.ofFn w))))
      atTop (𝓝 (∫ x, φ x ∂μ)) := by
  have hφ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous φ.continuous)
  have hdiam : Tendsto (fun n : ℕ ↦ (1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_const
        (diam (univ : Set CarpetPoints))
  have hφint : Integrable φ μ :=
    φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let a := ε / (μ.real univ + 1)
  have ha : 0 < a := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hsmall⟩ := hφ a ha
  filter_upwards [hdiam.eventually_lt_const hδ] with n hn
  let K (w : Fin n → Fin 8) := range (wordMap (List.ofFn w))
  let ν (w : Fin n → Fin 8) := μ.restrict (K w)
  let t (w : Fin n → Fin 8) := φ (wordMap (List.ofFn w) z)
  have hm (w : Fin n → Fin 8) : MeasurableSet (K w) := (measurableEmbedding_wordMap _).measurableSet_range
  have hsplit : μ = Measure.sum ν := by
    ext A hA
    rw [Measure.sum_apply _ hA, tsum_fintype]
    simp only [ν, Measure.restrict_apply hA, inter_comm A]
    rw [← measure_wordCellUnion_inter μ (hμ n) Finset.univ hA, wordCellUnion_univ, univ_inter]
  have hInt : ∫ x, φ x ∂μ = ∑ w : Fin n → Fin 8, ∫ x, φ x ∂ν w := by
    have h := integral_sum_measure (hsplit ▸ hφint)
    rw [tsum_fintype] at h
    exact hsplit.symm ▸ h
  have hmass : ∑ w : Fin n → Fin 8, μ.real (K w) = μ.real univ := by
    have h := measure_wordCellUnion μ (hμ n) Finset.univ
    rw [wordCellUnion_univ] at h
    unfold Measure.real
    rw [h, ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
  have hlocal (w : Fin n → Fin 8) :
      ‖t w * μ.real (K w) - ∫ x, φ x ∂ν w‖ ≤ a * μ.real (K w) := by
    have hconst : (∫ _ : CarpetPoints, t w ∂ν w) = t w * μ.real (K w) := by
      rw [integral_const, Measure.real, show ν w univ = μ (K w) by
        change μ.restrict (K w) univ = μ (K w)
        rw [Measure.restrict_apply MeasurableSet.univ, univ_inter], smul_eq_mul, mul_comm]
      rfl
    rw [← hconst, ← integral_sub (integrable_const _) hφint.restrict]
    have h := norm_integral_le_of_norm_le_const (μ := ν w) (C := a)
      (f := fun x ↦ t w - φ x) (by
        apply (ae_restrict_iff' (hm w)).mpr
        exact Eventually.of_forall fun x hx ↦ by
          rw [Real.norm_eq_abs, ← Real.dist_eq]
          exact (hsmall ((wordMap_dist_le n w (mem_range_self z) hx).trans_lt hn)).le)
    exact h.trans_eq (by
      simp only [Measure.real, ν, Measure.restrict_apply MeasurableSet.univ, univ_inter])
  have htotal : ‖(∑ w : Fin n → Fin 8, t w * μ.real (K w)) - ∫ x, φ x ∂μ‖ ≤ a * μ.real univ := by
    rw [hInt, ← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun w _ ↦ hlocal w).trans_eq
      (by rw [← Finset.mul_sum, hmass]))
  have haε : a * μ.real univ < ε := by
    dsimp only [a]
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ (by positivity : 0 < μ.real univ + 1)).mpr (by linarith)
  rw [dist_eq_norm]
  exact htotal.trans_lt haε

end CarpetEnergy
