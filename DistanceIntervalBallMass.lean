import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# A mass lower bound from a set spanning a distance interval
-/

open Filter Function Metric MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace CarpetEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]

set_option maxHeartbeats 2300000 in
/-- When every point of a set has a small ball with mass at least
proportional to its radius, spanning a distance interval gives a lower
bound on the mass of an open neighborhood containing those balls. -/
theorem measureReal_le_from_distance_interval
    (μ : Measure X) [IsFiniteMeasure μ] (o : X) {S U : Set X}
    {a b c R : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hspan : Icc a b ⊆ (fun x : X ↦ dist x o) '' S)
    (hball : ∀ x ∈ S, ∃ r ∈ Ioc 0 R, ball x r ⊆ U ∧ c * r ≤ μ.real (ball x r)) :
    c * (b - a) / 10 ≤ μ.real U := by
  classical
  choose r hrad hsub ht using fun x : S ↦ hball x.val x.property
  obtain ⟨A, _, hdisj, hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (univ : Set S) Subtype.val r R (fun x _ ↦ (hrad x).2) 5 (by norm_num)
  have hCount : A.Countable := hdisj.countable_of_isOpen (fun _ _ ↦ isOpen_ball)
    (fun x _ ↦ ⟨x.val, mem_ball_self (hrad x).1⟩)
  let : Countable A := hCount.to_subtype
  let B (x : A) := ball x.val.val (r x.val)
  let C (x : A) := ball (dist x.val.val o) (5 * r x.val)
  have hdisj' : Pairwise (Disjoint on B) := by
    intro x y h
    exact hdisj x.property y.property (fun he ↦ h (Subtype.ext he))
  have hI : Icc a b ⊆ ⋃ x : A, C x := by
    intro t ht'
    obtain ⟨x, hx, rfl⟩ := hspan ht'
    obtain ⟨y, hy, hyx⟩ := hcover ⟨x, hx⟩ (mem_univ _)
    have hxy := mem_ball.mp (hyx (mem_ball_self (hrad ⟨x, hx⟩).1))
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball.mpr ((dist_dist_dist_le_left _ _ _).trans_lt hxy)⟩
  have hC (x : A) : volume (C x) = ENNReal.ofReal (10 * r x.val) := by
    dsimp only [C]
    rw [Real.volume_ball]
    congr 1
    ring
  have hLen : ENNReal.ofReal (b - a) ≤ ∑' x : A, ENNReal.ofReal (10 * r x.val) := by
    rw [← Real.volume_Icc]
    exact (measure_mono (μ := volume) hI).trans (by simpa only [hC] using measure_iUnion_le (μ := volume) C)
  have hcost (x : A) : ENNReal.ofReal c * ENNReal.ofReal (10 * r x.val) ≤ 10 * μ (B x) := by
    have he : ENNReal.ofReal (c * r x.val) ≤ μ (B x) := by
      have hh := ENNReal.ofReal_le_ofReal (ht x.val)
      simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)] using hh
    have h := mul_le_mul' (by rfl : (10 : ℝ≥0∞) ≤ 10) he
    rw [← ENNReal.ofReal_mul hc.le]
    calc
      _ = ENNReal.ofReal (10 * (c * r x.val)) := by congr 1; ring
      _ ≤ _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10), ENNReal.ofReal_ofNat]; exact h
  have hU : (⋃ x : A, B x) ⊆ U := iUnion_subset fun x ↦ hsub x.val
  have hMass : ENNReal.ofReal (c * (b - a)) ≤ 10 * μ U := by
    rw [ENNReal.ofReal_mul hc.le]
    calc
      _ ≤ ENNReal.ofReal c * ∑' x : A, ENNReal.ofReal (10 * r x.val) := mul_le_mul' le_rfl hLen
      _ = ∑' x : A, ENNReal.ofReal c * ENNReal.ofReal (10 * r x.val) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' x : A, 10 * μ (B x) := tsum_le_tsum hcost
      _ = 10 * μ (⋃ x : A, B x) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdisj' (fun _ ↦ isOpen_ball.measurableSet)]
      _ ≤ _ := mul_le_mul' le_rfl (measure_mono hU)
  have hfin : (10 : ℝ≥0∞) * μ U ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)
  have h := ENNReal.toReal_mono hfin hMass
  rw [ENNReal.toReal_ofReal (mul_nonneg hc.le (sub_nonneg.mpr hab)),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 10)).mpr (h.trans_eq (mul_comm _ _))

end CarpetEnergy
