import UpperDensityBallCover
import EnergyPlanarBallMoments
import EnergyWeightedCapacityNonconcentration
import SmoothCutoffFamily
import PlanarLowerDensity

/-!
# Unweighted cutoffs on compact subsets of the unbounded upper-density set
-/

open Filter Function Metric MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 4600000 in
/-- The local upper bound needed in the planar argument fails only on
a set whose compact subsets admit arbitrarily small smooth unweighted
Sobolev tests. -/
theorem hasSmallUnweightedCutoffsOnCompacts_unboundedUpperBallDensity
    {p : ℝ} (hp : 1 < p) (μ : Measure PlanarCoordinates) [IsFiniteMeasure μ] :
    HasSmallWeightedCutoffsOnCompacts p volume (UnboundedUpperBallDensity μ (2 - p)) := by
  intro K hKB hK ε hε
  have hp₀ := zero_lt_one.trans hp
  obtain ⟨D, hD, hcut⟩ := exists_planar_ball_cutoffs
  obtain ⟨A, hA, hcombine⟩ := exists_smooth_cutoff_family (V := PlanarCoordinates) hp
  let M := max 36 (A * (36 * D ^ p))
  have hM : 0 < M := (by norm_num : (0 : ℝ) < 36).trans_le (le_max_left _ _)
  obtain ⟨m, z, r, hr, hcover, hcost⟩ := exists_small_finite_cover_of_unbounded_density
    μ hK hKB (div_pos hε hM) (show (0 : ℝ) < 1 by norm_num)
  choose f hf h01 hsmall hlarge hbound using fun j : Fin m ↦ hcut (z j) (r j) (hr j).1
  obtain ⟨g, hg, hg01, hg1, hg0, hgb⟩ := hcombine f hf h01
  let S (j : Fin m) := ball (z j) (3 * r j)
  let C (j : Fin m) := closedBall (z j) (3 * r j)
  have hC : IsCompact (⋃ j, C j) := isCompact_iUnion fun _ ↦ isCompact_closedBall _ _
  have hS : MeasurableSet (⋃ j, S j) := MeasurableSet.iUnion (fun j ↦ isOpen_ball.measurableSet)
  have hfin : volume (⋃ j, S j) ≠ ∞ :=
    ne_of_lt ((measure_mono (iUnion_mono (fun _ ↦ ball_subset_closedBall))).trans_lt hC.measure_lt_top)
  have hvanish (x : PlanarCoordinates) (hx : x ∉ ⋃ j, S j) : g x = 0 :=
    hg0 x (fun j ↦ (hlarge j x (fun hxj ↦ hx (mem_iUnion.mpr ⟨j, hxj⟩))).1)
  have hcs : HasCompactSupport g := by
    refine HasCompactSupport.of_support_subset_isCompact hC (fun x hx ↦ ?_)
    by_contra hout
    exact hx (hvanish x (fun h ↦ hout (iUnion_mono (fun _ ↦ ball_subset_closedBall) h)))
  refine ⟨g, hg, hcs, hg01, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    exact hg1 x ⟨j, hsmall j x hj⟩
  · have hcg : Continuous (fun x ↦ |g x| ^ p) :=
      hg.continuous.abs.rpow_const (fun _ ↦ Or.inr hp₀.le)
    have hIg : Integrable (fun x ↦ |g x| ^ p) volume := hcg.integrable_of_hasCompactSupport (by
      apply hcs.mono'
      intro x hx
      by_contra h
      have hzero : g x = 0 := notMem_support.mp (fun hx' ↦ h (subset_tsupport g hx'))
      exact hx (by change |g x| ^ p = 0; rw [hzero, abs_zero, Real.zero_rpow hp₀.ne']))
    have hgvol := integral_le_mul_measure_of_vanishes hS hfin hIg
      (M := 1) (fun x ↦ by
        rw [abs_of_nonneg (hg01 x).1, ← Real.one_rpow p]
        exact Real.rpow_le_rpow (hg01 x).1 (hg01 x).2 hp₀.le)
      (fun x hx ↦ by rw [hvanish x hx, abs_zero, Real.zero_rpow hp₀.ne'])
    have hm : volume.real (⋃ j, S j) ≤ ∑ j, 36 * (r j) ^ (2 - p) := by
      have he := measure_iUnion_fintype_le (μ := (volume : Measure PlanarCoordinates)) S
      have hball (j : Fin m) : volume (S j) = ENNReal.ofReal (36 * (r j) ^ (2 : ℕ)) := by
        dsimp only [S]
        rw [planar_volume_ball _ (mul_nonneg (by norm_num) (hr j).1.le)]
        congr 1
        ring
      simp only [hball] at he
      have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun _ _ ↦ ENNReal.ofReal_ne_top)) he
      rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.ofReal_ne_top)] at hreal
      refine hreal.trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 36 * (r j) ^ (2 : ℕ)),
        ← Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hr j).1 (hr j).2.le (by norm_num; linarith)) (by norm_num)
    rw [one_mul] at hgvol
    refine hgvol.trans (hm.trans ?_)
    rw [← Finset.mul_sum]
    exact (mul_le_mul (le_max_left _ _) hcost (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg
      (hr j).1.le _) hM.le).trans_eq (mul_div_cancel₀ _ hM.ne')
  · intro i
    let e : PlanarCoordinates := Pi.single i 1
    let F (j : Fin m) (x : PlanarCoordinates) := |fderiv ℝ (f j) x e| ^ p
    have hJ (j : Fin m) : Integrable (F j) volume := by
      have hc : Continuous (F j) := (((hf j).continuous_fderiv (by norm_num)).clm_apply
        continuous_const).abs.rpow_const (fun _ ↦ Or.inr hp₀.le)
      apply hc.integrable_of_hasCompactSupport
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (z j) (3 * r j)) ?_
      intro x hx
      exact ball_subset_closedBall (show x ∈ S j from by
        by_contra h
        exact hx (by dsimp only [F]; rw [(hlarge j x h).2, zero_apply, abs_zero, Real.zero_rpow hp₀.ne']))
    have hj (j : Fin m) : (∫ x, F j x ∂volume) ≤ (36 * D ^ p) * (r j) ^ (2 - p) := by
      have hfinj : volume (S j) ≠ ∞ := ne_of_lt
        ((measure_mono (ball_subset_closedBall (x := z j) (ε := 3 * r j))).trans_lt
          (isCompact_closedBall _ _).measure_lt_top)
      have hi := integral_le_mul_measure_of_vanishes isOpen_ball.measurableSet hfinj (hJ j)
        (fun x ↦ Real.rpow_le_rpow (abs_nonneg _) (hbound j x i) hp₀.le)
        (fun x hx ↦ by dsimp only [F]; rw [(hlarge j x hx).2, zero_apply, abs_zero, Real.zero_rpow hp₀.ne'])
      apply hi.trans_eq
      have hrad : 0 ≤ r j := (hr j).1.le
      have h3r : 0 ≤ (3 : ℝ) * r j := mul_nonneg (by norm_num) hrad
      have h4 : 0 ≤ (4 : ℝ) * (3 * r j) ^ (2 : ℕ) := by positivity
      rw [Measure.real, planar_volume_ball (z j) h3r, ENNReal.toReal_ofReal h4]
      rw [Real.div_rpow hD.le hrad, Real.rpow_sub (hr j).1, Real.rpow_two]
      ring
    have hcg : Continuous (fun x ↦ |fderiv ℝ g x e| ^ p) :=
      ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).abs.rpow_const
        (fun _ ↦ Or.inr hp₀.le)
    have hI : Integrable (fun x ↦ |fderiv ℝ g x e| ^ p) volume :=
      hcg.integrable_of_hasCompactSupport (by
        apply (hcs.fderiv_apply ℝ e).mono'
        intro x hx
        by_contra h
        let Fg (x : PlanarCoordinates) := fderiv ℝ g x e
        have hzero : Fg x = 0 := notMem_support.mp (fun hx' ↦ h (subset_tsupport Fg hx'))
        change fderiv ℝ g x e = 0 at hzero
        exact hx (by change |fderiv ℝ g x e| ^ p = 0; rw [hzero, abs_zero, Real.zero_rpow hp₀.ne']))
    have hmajor : Integrable (fun x ↦ A * ∑ j, F j x) volume :=
      (integrable_finsetSum Finset.univ (fun j _ ↦ hJ j)).const_mul A
    have hcomp := integral_mono hI hmajor (fun x ↦ hgb x e)
    rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ hJ j)] at hcomp
    refine hcomp.trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hj j)) hA.le).trans ?_)
    rw [← Finset.mul_sum, ← mul_assoc]
    exact (mul_le_mul (le_max_right _ _) hcost (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg
      (hr j).1.le _) hM.le).trans_eq (mul_div_cancel₀ _ hM.ne')

end CarpetEnergy
