import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic

/-!
# The scalar cutoff for weighted Sobolev capacity

The cutoff in Section 8 cancels large values of the Sobolev weight.
The two-point estimate retains both denominators and is used to bound
the commutator with mollification.
-/

open Filter Function Set
open scoped NNReal Topology

namespace CarpetEnergy

/-- The scalar cutoff in equations (8.4)–(8.7). -/
noncomputable def weightCutoff (C s : ℝ) : ℝ :=
  max (1 - C / (max s 0 + 1)) 0

theorem weightCutoff_of_nonneg (C : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    weightCutoff C s = max (1 - C / (s + 1)) 0 := by
  rw [weightCutoff, max_eq_left hs]

theorem weightCutoff_nonneg (C s : ℝ) : 0 ≤ weightCutoff C s := le_max_right _ _

theorem weightCutoff_le_one {C : ℝ} (hC : 0 ≤ C) (s : ℝ) : weightCutoff C s ≤ 1 := by
  apply max_le _ zero_le_one
  exact sub_le_self _ (div_nonneg hC (by positivity))

theorem weightCutoff_eq_zero_of_le {C s : ℝ} (hC : 1 ≤ C) (hs : s ≤ C - 1) :
    weightCutoff C s = 0 := by
  apply max_eq_right
  apply sub_nonpos.mpr
  have hden : 0 < max s 0 + 1 := by positivity
  apply (le_div_iff₀ hden).mpr
  rw [one_mul]
  have hmax : max s 0 ≤ C - 1 := max_le hs (sub_nonneg.mpr hC)
  linarith

theorem weightCutoff_zero {C : ℝ} (hC : 1 ≤ C) : weightCutoff C 0 = 0 :=
  weightCutoff_eq_zero_of_le hC (sub_nonneg.mpr hC)

theorem weightCutoff_eq_of_gt {C s : ℝ} (hC : 1 ≤ C) (hs : C - 1 < s) :
    weightCutoff C s = 1 - C / (s + 1) := by
  rw [weightCutoff_of_nonneg C (le_of_lt (by linarith : 0 < s))]
  apply max_eq_left
  exact sub_nonneg.mpr ((div_le_one (by linarith : 0 < s + 1)).mpr (by linarith))

theorem weightCutoff_weighted_complement_le (C : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (s + 1) * (1 - weightCutoff C s) ≤ C := by
  have hp : 0 < s + 1 := by positivity
  rw [weightCutoff_of_nonneg C hs]
  have h : 1 - max (1 - C / (s + 1)) 0 ≤ C / (s + 1) := by
    linarith only [le_max_left (1 - C / (s + 1)) 0]
  exact (mul_le_mul_of_nonneg_left h hp.le).trans_eq (by field_simp)

theorem weightCutoff_le_indicator {C s : ℝ} (hC : 1 ≤ C) :
    weightCutoff C s ≤ Set.indicator {t : ℝ | C - 1 < t} (fun _ ↦ (1 : ℝ)) s := by
  by_cases hs : C - 1 < s
  · rw [indicator_of_mem hs]
    exact weightCutoff_le_one (zero_le_one.trans hC) s
  · rw [indicator_of_notMem hs, weightCutoff_eq_zero_of_le hC (le_of_not_gt hs)]

/-- The reciprocal cutoff depends only on the part of the weight above
the threshold. -/
theorem weightCutoff_eq_tail_div {C s : ℝ} (hC : 1 ≤ C) (hs : 0 ≤ s) :
    weightCutoff C s = max (s - (C - 1)) 0 / (C + max (s - (C - 1)) 0) := by
  by_cases h : C - 1 < s
  · rw [weightCutoff_eq_of_gt hC h, max_eq_left (sub_nonneg.mpr h.le)]
    have he : C + (s - (C - 1)) = s + 1 := by ring
    rw [he]
    field_simp
    ring
  · rw [weightCutoff_eq_zero_of_le hC (not_lt.mp h), max_eq_right (sub_nonpos.mpr (not_lt.mp h)), zero_div]

/-- For the mollification estimate the weighted cutoff increment can
be controlled by the increment of the upper tail of the weight. -/
theorem weightCutoff_weighted_abs_sub_le_tail {C s t : ℝ} (hC : 1 ≤ C)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s + 1) * |weightCutoff C t - weightCutoff C s| ≤
      |max (t - (C - 1)) 0 - max (s - (C - 1)) 0| := by
  let a := max (s - (C - 1)) 0
  let b := max (t - (C - 1)) 0
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  have ha : 0 ≤ a := le_max_right _ _
  have hb : 0 ≤ b := le_max_right _ _
  have hsa : s + 1 ≤ C + a := by
    have he : s - (C - 1) ≤ a := le_max_left _ _
    linarith
  have hpa := add_pos_of_pos_of_nonneg hC₀ ha
  have hpb := add_pos_of_pos_of_nonneg hC₀ hb
  rw [weightCutoff_eq_tail_div hC hs, weightCutoff_eq_tail_div hC ht]
  change (s + 1) * |b / (C + b) - a / (C + a)| ≤ |b - a|
  have hquot : b / (C + b) - a / (C + a) =
      C * (b - a) / ((C + b) * (C + a)) := by
    field_simp [hpa.ne', hpb.ne']
    ring
  rw [hquot, abs_div, abs_mul, abs_of_pos hC₀, abs_of_pos (mul_pos hpb hpa), ← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos hpb hpa)).mpr
  have hM : (s + 1) * C ≤ (C + b) * (C + a) :=
    (mul_le_mul hsa (le_add_of_nonneg_right hb) hC₀.le hpa.le).trans_eq (mul_comm _ _)
  calc
    (s + 1) * (C * |b - a|) = ((s + 1) * C) * |b - a| := by ring
    _ ≤ ((C + b) * (C + a)) * |b - a| := mul_le_mul_of_nonneg_right hM (abs_nonneg _)
    _ = _ := mul_comm _ _

theorem weightCutoff_weighted_abs_sub_le {C s t : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (t + 1) * (s + 1) * |weightCutoff C t - weightCutoff C s| ≤ C * |t - s| := by
  have hs₀ : 0 < s + 1 := by positivity
  have ht₀ : 0 < t + 1 := by positivity
  rw [weightCutoff_of_nonneg C hs, weightCutoff_of_nonneg C ht]
  have h := abs_max_sub_max_le_abs (1 - C / (t + 1)) (1 - C / (s + 1)) 0
  apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
  have he : 1 - C / (t + 1) - (1 - C / (s + 1)) =
      (C * (t - s)) / ((t + 1) * (s + 1)) := by field_simp; ring
  rw [he, abs_div, abs_mul, abs_of_nonneg hC, abs_of_pos (mul_pos ht₀ hs₀)]
  field_simp

theorem lipschitzWith_weightCutoff {C : ℝ} (hC : 0 ≤ C) :
    LipschitzWith C.toNNReal (weightCutoff C) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro s t
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC]
  let a := max s 0
  let b := max t 0
  have ha : 0 ≤ a := le_max_right _ _
  have hb : 0 ≤ b := le_max_right _ _
  have he (x : ℝ) : weightCutoff C (max x 0) = weightCutoff C x := by
    rw [weightCutoff_of_nonneg C (le_max_right x 0), weightCutoff]
  rw [← he s, ← he t]
  have h₁ : 1 ≤ (a + 1) * (b + 1) := by nlinarith [mul_nonneg ha hb]
  have hd : |weightCutoff C a - weightCutoff C b| ≤
      (a + 1) * (b + 1) * |weightCutoff C a - weightCutoff C b| := by
    exact (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right h₁ (abs_nonneg _))
  exact hd.trans ((weightCutoff_weighted_abs_sub_le hC hb ha).trans
    (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs s t 0) hC))

theorem hasDerivAt_weightCutoff_below {C s : ℝ} (hC : 1 ≤ C) (hs : s < C - 1) :
    HasDerivAt (weightCutoff C) 0 s := by
  refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hs] with t ht
  exact weightCutoff_eq_zero_of_le hC ht.le

theorem hasDerivAt_weightCutoff_above {C s : ℝ} (hC : 1 ≤ C) (hs : C - 1 < s) :
    HasDerivAt (weightCutoff C) (C / (s + 1) ^ 2) s := by
  have hden : s + 1 ≠ 0 := by linarith
  have hd : HasDerivAt (fun t : ℝ ↦ t + 1) 1 s := by
    simpa only [id_eq] using (hasDerivAt_id s).add_const 1
  have h := (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_const s C).div hd hden)
  have he : 0 - (0 * (s + 1) - C * 1) / (s + 1) ^ 2 = C / (s + 1) ^ 2 := by ring
  rw [he] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact weightCutoff_eq_of_gt hC ht

theorem weightCutoff_weighted_deriv_le {C s : ℝ} (hC : 1 ≤ C) (hs : C - 1 < s) :
    (s + 1) * deriv (weightCutoff C) s ≤ 1 := by
  have hs₀ : 0 < s + 1 := by linarith
  rw [(hasDerivAt_weightCutoff_above hC hs).deriv]
  have he : (s + 1) * (C / (s + 1) ^ 2) = C / (s + 1) := by field_simp
  rw [he]
  exact (div_le_one hs₀).mpr (by linarith)

end CarpetEnergy
