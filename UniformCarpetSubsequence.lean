import CarpetMeasure
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Uniform subsequences of equicontinuous carpet profiles
-/

open Filter Function Set
open scoped Topology

namespace CarpetEnergy

theorem exists_uniform_subseq_of_equicontinuous_carpet_sequence
    (f : ℕ → C(CarpetPoints, ℝ)) {B : ℝ} (hB : ∀ k x, |f k x| ≤ B)
    (hmod : ∀ ε > (0 : ℝ), ∃ r > (0 : ℝ), ∀ k x y, dist x y < r →
      |f k x - f k y| ≤ ε) :
    ∃ (j : ℕ → ℕ) (u : C(CarpetPoints, ℝ)), StrictMono j ∧
      Tendsto (fun n ↦ f (j n)) atTop (𝓝 u) := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact CarpetPoints ℝ
  let g (n : ℕ) := e (f n)
  let A := range g
  have hvalues (v : BoundedContinuousFunction CarpetPoints ℝ) (x : CarpetPoints) (hv : v ∈ A) :
      v x ∈ Icc (-B) B := by
    obtain ⟨k, rfl⟩ := hv
    exact abs_le.mp (hB k x)
  have heq : Equicontinuous ((↑) : A → CarpetPoints → ℝ) := by
    intro x
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    obtain ⟨r, hr, h⟩ := hmod (ε / 2) (half_pos hε)
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    rintro ⟨v, ⟨k, rfl⟩⟩
    change dist (f k x) (f k y) < ε
    rw [Real.dist_eq]
    exact (h k x y (dist_comm y x ▸ hy)).trans_lt (half_lt_self hε)
  have hc := BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc A hvalues heq
  obtain ⟨u, _, j, hj, hlim⟩ := hc.tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n) : ∀ n, g n ∈ closure A)
  refine ⟨j, e.symm u, hj, ?_⟩
  have ht := (e.symm.isometry.continuous.tendsto u).comp hlim
  change Tendsto (fun n ↦ e.symm (e (f (j n)))) atTop (𝓝 (e.symm u)) at ht
  simpa only [IsometryEquiv.symm_apply_apply] using ht

end CarpetEnergy
