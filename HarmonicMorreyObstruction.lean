import EnergyImageArea
import EnergyFullSupport
import CarpetGoodCells
import PlanarDistributionRows
import Mathlib.MeasureTheory.Measure.Support

/-!
# The Morrey contradiction for planar pushforwards

A continuous finite-energy pair has a Haar-null image when the scale
is larger than one. A nonzero measure supported on that image cannot
satisfy the planar distributional bounds.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A nonnegative interior finite-energy cutoff has positive weighted
mass for any nonzero measure giving the exterior boundary zero mass. -/
theorem exists_positive_interior_weight (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (hμ : 0 < μ univ) (hnull : μ carpetOuterBoundary = 0) :
    ∃ u : C(CarpetPoints, ℝ), continuousLp p u ∈ E.domain ∧
      tsupport (u : CarpetPoints → ℝ) ⊆ carpetOuterBoundaryᶜ ∧
      (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧
      0 < (μ.withDensity fun x ↦ ENNReal.ofReal (u x ^ p)) univ := by
  have hpos : 0 < μ carpetOuterBoundaryᶜ := by
    rw [measure_compl measurableSet_carpetOuterBoundary (measure_ne_top _ _), hnull, tsub_zero]
    exact hμ
  obtain ⟨x, hx, hxSupp⟩ := Measure.nonempty_inter_support_of_pos hpos
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_carpetOuterBoundary.isOpen_compl x hx
  obtain ⟨u, hu, hux, huz, hb⟩ := E.exists_continuous_cutoff x (half_pos hr)
  have hs : support (u : CarpetPoints → ℝ) ⊆ ball x (r / 2) := fun y hy ↦
    not_not.mp (fun h ↦ hy (huz y h))
  have hts : tsupport (u : CarpetPoints → ℝ) ⊆ carpetOuterBoundaryᶜ :=
    ((closure_minimal (hs.trans ball_subset_closedBall) isClosed_closedBall).trans
      (closedBall_subset_ball (half_lt_self hr))).trans hball
  let B := {y | (1 / 2 : ℝ) < u y}
  have hB : IsOpen B := isOpen_lt continuous_const u.continuous
  have hxB : x ∈ B := by change (1 / 2 : ℝ) < u x; rw [hux]; norm_num
  have hμB := (Measure.mem_support_iff_forall x).mp hxSupp B (hB.mem_nhds hxB)
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  refine ⟨u, hu, hts, hb, ?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hc : 0 < ENNReal.ofReal ((1 / 2 : ℝ) ^ p) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  apply (ENNReal.mul_pos hc.ne' hμB.ne').trans_le
  calc
    _ = ∫⁻ y in B, ENNReal.ofReal ((1 / 2 : ℝ) ^ p) ∂μ := by rw [setLIntegral_const]
    _ ≤ ∫⁻ y in B, ENNReal.ofReal (u y ^ p) ∂μ := by
      apply lintegral_mono_ae
      apply (ae_restrict_iff' hB.measurableSet).mpr
      exact Eventually.of_forall fun y hy ↦ ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (by norm_num) (show (1 / 2 : ℝ) ≤ u y from hy.le) hp.le)
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- A nonzero measure pushed forward by a finite-energy pair cannot
have bounded distributional derivatives in the Morrey case. -/
theorem not_hasBoundedDistributionalGradient_map_pair (hρ : 1 < E.scalingFactor)
    (f g : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain) (hg : continuousLp p g ∈ E.domain)
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (hμ : 0 < μ univ)
    (C : ℝ) (hC : 0 ≤ C) :
    ¬ HasBoundedDistributionalGradient (μ.map fun x ↦ (![f x, g x] : Fin 2 → ℝ)) C := by
  let H (x : CarpetPoints) : Fin 2 → ℝ := ![f x, g x]
  have hH : Continuous H := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact f.continuous
    · exact g.continuous
  intro hgrad
  let ν := μ.map H
  have hac : ν ≪ volume := absoluteContinuous_of_boundedDistributionalGradient ν volume hC hgrad
  have hzero := hac (E.volume_range_pair_eq_zero hρ f g hf hg)
  change ν (range H) = 0 at hzero
  have hMeas : MeasurableSet (range H) := (isCompact_range hH).isClosed.measurableSet
  rw [Measure.map_apply hH.measurable hMeas, preimage_range] at hzero
  exact hμ.ne' hzero

end CarpetEnergy.SelfSimilarPEnergy
