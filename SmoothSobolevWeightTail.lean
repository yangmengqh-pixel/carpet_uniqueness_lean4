import SmoothCutoffFamily

/-!
# A smooth upper-tail truncation and its reciprocal cutoff
-/

open Filter
open scoped Topology

namespace CarpetEnergy

/-- Smooth upper tails have a derivative budget confined to the tail.
The reciprocal cutoff has uniformly controlled weighted increments
in terms of that same tail. -/
theorem exists_smooth_tail_weight_cutoffs :
    ∃ D > (0 : ℝ), ∀ c ≥ (0 : ℝ), ∃ T F : ℝ → ℝ,
      ContDiff ℝ 1 T ∧ (∀ t, 0 ≤ T t) ∧ (∀ t ≤ c, T t = 0 ∧ deriv T t = 0) ∧
      (∀ t, |deriv T t| ≤ D) ∧
      ContDiff ℝ 1 F ∧ (∀ t, 0 ≤ F t ∧ F t ≤ 1) ∧ (∀ t ≤ c, F t = 0) ∧
      (∀ t ≥ 0, (t + 1) * (1 - F t) ≤ c + 2) ∧
      ∀ s ≥ 0, ∀ t ≥ 0, (s + 1) * |F t - F s| ≤ |T t - T s| := by
  obtain ⟨D, hD, hd⟩ := exists_deriv_bound_smoothTransition
  have hθ : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hder0 (x : ℝ) (hx : x < 0 ∨ 1 < x) : deriv Real.smoothTransition x = 0 := by
    rcases hx with hx | hx
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
        (gt_mem_nhds hx).mono (fun _ ht ↦ Real.smoothTransition.zero_of_nonpos ht.le)
      rw [he.deriv_eq, deriv_const]
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) :=
        (lt_mem_nhds hx).mono (fun _ ht ↦ Real.smoothTransition.one_of_one_le ht.le)
      rw [he.deriv_eq, deriv_const]
  refine ⟨1 + D, add_pos one_pos hD, fun c hc ↦ ?_⟩
  let A (t : ℝ) := t - c
  let T (t : ℝ) := A t * Real.smoothTransition (A t)
  let b := c + 2
  let F (t : ℝ) := T t / (b + T t)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hA : ContDiff ℝ 1 A := contDiff_id.sub contDiff_const
  have hT : ContDiff ℝ 1 T := hA.mul (hθ.comp hA)
  have hTd (t : ℝ) : deriv T t =
      Real.smoothTransition (A t) + A t * deriv Real.smoothTransition (A t) := by
    have hAd : HasDerivAt A 1 t := (hasDerivAt_id t).sub_const c
    have hθd := ((hθ.differentiable (by norm_num) (A t)).hasDerivAt).comp t hAd
    have hh := hAd.mul hθd
    change HasDerivAt T _ t at hh
    rw [hh.deriv, one_mul, mul_one]
    rfl
  have hT₀ (t : ℝ) : 0 ≤ T t := by
    by_cases ht : 0 ≤ A t
    · exact mul_nonneg ht (Real.smoothTransition.nonneg _)
    · simp only [T, Real.smoothTransition.zero_of_nonpos (le_of_not_ge ht), mul_zero, le_rfl]
  have hTB (t : ℝ) : t + 1 ≤ b + T t := by
    by_cases ht : 1 ≤ A t
    · dsimp only [T, b]
      rw [Real.smoothTransition.one_of_one_le ht, mul_one]
      dsimp only [A]
      linarith
    · have ht' : t + 1 ≤ b := by dsimp only [A, b] at *; linarith
      exact ht'.trans (le_add_of_nonneg_right (hT₀ t))
  have hden (t : ℝ) : 0 < b + T t := add_pos_of_pos_of_nonneg hb (hT₀ t)
  have hF : ContDiff ℝ 1 F := hT.div (contDiff_const.add hT) (fun t ↦ (hden t).ne')
  have hzero (t : ℝ) (ht : t ≤ c) : T t = 0 ∧ deriv T t = 0 := by
    have hAt : A t ≤ 0 := sub_nonpos.mpr ht
    refine ⟨by simp only [T, Real.smoothTransition.zero_of_nonpos hAt, mul_zero], ?_⟩
    rw [hTd, Real.smoothTransition.zero_of_nonpos hAt, zero_add]
    rcases hAt.eq_or_lt with he | he
    · rw [he, zero_mul]
    · rw [hder0 _ (Or.inl he), mul_zero]
  have hbd (t : ℝ) : |deriv T t| ≤ 1 + D := by
    by_cases ht : 0 ≤ A t ∧ A t ≤ 1
    · rw [hTd]
      apply (abs_add_le _ _).trans
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _), abs_mul, abs_of_nonneg ht.1]
      exact add_le_add (Real.smoothTransition.le_one _) (by
        apply (mul_le_mul ht.2 (hd _) (abs_nonneg _) zero_le_one).trans_eq
        rw [one_mul])
    · have he : A t < 0 ∨ 1 < A t := (not_and_or.mp ht).imp lt_of_not_ge lt_of_not_ge
      rw [hTd, hder0 _ he, mul_zero, add_zero, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact (Real.smoothTransition.le_one _).trans (le_add_of_nonneg_right hD.le)
  refine ⟨T, F, hT, hT₀, hzero, hbd, hF, fun t ↦
    ⟨div_nonneg (hT₀ t) (hden t).le, (div_le_one (hden t)).mpr (le_add_of_nonneg_left hb.le)⟩,
    fun t ht ↦ by dsimp only [F]; rw [(hzero t ht).1, zero_div], ?_, ?_⟩
  · intro t ht
    have he : 1 - F t = b / (b + T t) := by dsimp only [F]; field_simp [(hden t).ne']; ring
    rw [he, ← mul_div_assoc]
    exact (div_le_iff₀ (hden t)).mpr
      ((mul_le_mul_of_nonneg_right (hTB t) hb.le).trans_eq (mul_comm _ _))
  · intro s hs t ht
    have hh : F t - F s = b * (T t - T s) / ((b + T t) * (b + T s)) := by
      dsimp only [F]
      field_simp [(hden s).ne', (hden t).ne']
      ring
    rw [hh, abs_div, abs_mul, abs_of_pos hb, abs_of_pos (mul_pos (hden t) (hden s)), ← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos (hden t) (hden s))).mpr
    have hp : (s + 1) * b ≤ (b + T t) * (b + T s) :=
      (mul_le_mul (hTB s) (le_add_of_nonneg_right (hT₀ t)) hb.le (hden s).le).trans_eq (mul_comm _ _)
    calc
      (s + 1) * (b * |T t - T s|) = ((s + 1) * b) * |T t - T s| := by ring
      _ ≤ ((b + T t) * (b + T s)) * |T t - T s| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
      _ = _ := mul_comm _ _

end CarpetEnergy
