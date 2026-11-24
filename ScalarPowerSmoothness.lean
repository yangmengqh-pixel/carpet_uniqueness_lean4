import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform symmetric increment of a scalar p-power

A single modulus controls each edge contribution to the discrete
energies, including edges where the first difference vanishes.
-/

open Set

namespace CarpetEnergy

private theorem exists_nonneg_symmetric_increment_of_continuous_deriv
    (F D : ℝ → ℝ) (hD : Continuous D)
    (hderiv : ∀ x, HasDerivAt F (D x) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x y t : ℝ,
      |x| ≤ 1 → |y| ≤ 1 → 0 ≤ t → t < δ →
      F (x + t * y) + F (x - t * y) - 2 * F x ≤ ε * t := by
  let J := Icc (-2 : ℝ) 2
  have hJ : IsCompact J := isCompact_Icc
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hJ.uniformContinuousOn_of_continuous hD.continuousOn) ε hε
  let δ := min 1 (r / 2)
  have hδ : 0 < δ := lt_min one_pos (half_pos hr)
  refine ⟨δ, hδ, fun x y t hx hy ht htδ ↦ ?_⟩
  let G (s : ℝ) := F (x + s * y) + F (x - s * y) - 2 * F x
  let DG (s : ℝ) := (D (x + s * y) - D (x - s * y)) * y
  have hG (s : ℝ) (_ : s ∈ Icc 0 t) : HasDerivWithinAt G (DG s) (Icc 0 t) s := by
    have h₁ : HasDerivAt (fun s : ℝ ↦ x + s * y) y s := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id s).mul_const y).const_add x
    have h₂ : HasDerivAt (fun s : ℝ ↦ x - s * y) (-y) s := by
      have h := (hasDerivAt_const s x).sub ((hasDerivAt_id s).mul_const y)
      rw [one_mul, zero_sub] at h
      exact h
    have h₁' := (hderiv (x + s * y)).comp s h₁
    have h₂' := (hderiv (x - s * y)).comp s h₂
    have h := (h₁'.add h₂').sub_const (2 * F x)
    have he : D (x + s * y) * y + D (x - s * y) * -y = DG s := by
      dsimp only [DG]
      ring
    rw [he] at h
    exact h.hasDerivWithinAt
  have hb (s : ℝ) (hs : s ∈ Ico 0 t) : ‖DG s‖ ≤ ε := by
    have hst : s < δ := hs.2.trans htδ
    have hsu : s < 1 := hst.trans_le (min_le_left _ _)
    have hsy : |s * y| ≤ s := by
      rw [abs_mul, abs_of_nonneg hs.1]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hy hs.1
    have hplus : x + s * y ∈ J := by
      apply abs_le.mp
      exact (abs_add_le _ _).trans (by linarith only [hx, hsy, hsu])
    have hminus : x - s * y ∈ J := by
      apply abs_le.mp
      exact (abs_sub _ _).trans (by linarith only [hx, hsy, hsu])
    have hdist : dist (x + s * y) (x - s * y) < r := by
      rw [Real.dist_eq, show x + s * y - (x - s * y) = 2 * (s * y) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hsr := hst.trans_le (min_le_right 1 (r / 2))
      linarith only [hsy, hsr]
    have hh := hmod _ hplus _ hminus hdist
    rw [Real.dist_eq] at hh
    change ‖(D (x + s * y) - D (x - s * y)) * y‖ ≤ ε
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |D (x + s * y) - D (x - s * y)| * 1 :=
        mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ ≤ ε := by simpa only [mul_one] using hh.le
  have he := norm_image_sub_le_of_norm_deriv_le_segment' hG hb t (right_mem_Icc.mpr ht)
  have h0 : G 0 = 0 := by simp only [G, zero_mul, add_zero, sub_zero]; ring
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at he
  exact (le_abs_self _).trans he

/-- The two-sided excess of the scalar power is uniformly small
relative to the energy of the base and direction. -/
theorem exists_abs_rpow_symmetric_increment {p : ℝ} (hp : 1 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x y t : ℝ, |t| < δ →
      |x + t * y| ^ p + |x - t * y| ^ p - 2 * |x| ^ p ≤
        ε * |t| * (|x| ^ p + |y| ^ p) := by
  let F (x : ℝ) := |x| ^ p
  have hF : ContDiff ℝ 1 F := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow (E := ℝ) hp)
  obtain ⟨δ, hδ, h⟩ := exists_nonneg_symmetric_increment_of_continuous_deriv
    F (deriv F) (contDiff_one_iff_deriv.mp hF).2
    (fun x ↦ ((contDiff_one_iff_deriv.mp hF).1 x).hasDerivAt) hε
  refine ⟨δ, hδ, fun x y t ht ↦ ?_⟩
  let a := max |x| |y|
  have ha : 0 ≤ a := (abs_nonneg x).trans (le_max_left ..)
  rcases ha.eq_or_lt with ha0 | ha'
  · have hx : x = 0 := abs_eq_zero.mp (le_antisymm ((le_max_left _ _).trans ha0.symm.le) (abs_nonneg _))
    have hy : y = 0 := abs_eq_zero.mp (le_antisymm ((le_max_right _ _).trans ha0.symm.le) (abs_nonneg _))
    simp [hx, hy, Real.zero_rpow (zero_lt_one.trans hp).ne']
  have hx : |x / a| ≤ 1 := by
    rw [abs_div, abs_of_pos ha', div_le_one ha']
    exact le_max_left _ _
  have hy : |y / a| ≤ 1 := by
    rw [abs_div, abs_of_pos ha', div_le_one ha']
    exact le_max_right _ _
  have hh := h (x / a) (y / a) |t| hx hy (abs_nonneg t) ht
  have ht' : F (x / a + t * (y / a)) + F (x / a - t * (y / a)) - 2 * F (x / a) ≤ ε * |t| := by
    rcases le_or_gt 0 t with hpos | hneg
    · simpa only [abs_of_nonneg hpos] using hh
    · rw [abs_of_neg hneg, neg_mul, ← sub_eq_add_neg, sub_neg_eq_add,
        add_comm (F (x / a - t * (y / a)))] at hh
      simpa only [abs_of_neg hneg] using hh
  have hscaled := mul_le_mul_of_nonneg_left ht' (Real.rpow_nonneg ha p)
  have hmul (z : ℝ) : a ^ p * F (z / a) = F z := by
    dsimp only [F]
    rw [abs_div, abs_of_pos ha', Real.div_rpow (abs_nonneg _) ha]
    exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos ha' p).ne'
  rw [show x / a + t * (y / a) = (x + t * y) / a by ring,
    show x / a - t * (y / a) = (x - t * y) / a by ring,
    mul_sub, mul_add, hmul, hmul, mul_left_comm (a ^ p) 2, hmul] at hscaled
  have hsum : a ^ p ≤ |x| ^ p + |y| ^ p := by
    rcases le_total |x| |y| with h | h
    · dsimp only [a]
      rw [max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
    · dsimp only [a]
      rw [max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
  have hd := mul_le_mul_of_nonneg_left hsum (mul_nonneg hε.le (abs_nonneg t))
  change F _ + F _ - 2 * F _ ≤ _
  rw [mul_comm (a ^ p)] at hscaled
  exact hscaled.trans hd

end CarpetEnergy
