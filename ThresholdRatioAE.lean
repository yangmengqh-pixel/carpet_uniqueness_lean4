import EnergyVanishing

/-!
# Almost-everywhere comparison from positive excess thresholds
-/

open Filter Function MeasureTheory Set

namespace CarpetEnergy

private theorem ae_integral_pos_of_posPart {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, 0 < g x → 0 < ∫ y, max (g y) 0 ∂μ := by
  by_cases hI : 0 < ∫ y, max (g y) 0 ∂μ
  · exact Eventually.of_forall fun _ _ ↦ hI
  have hzero : μ (support (fun y ↦ max (g y) 0)) = 0 := by
    by_contra hne
    exact hI ((integral_pos_iff_support_of_nonneg (fun y ↦ le_max_right (g y) 0)
      hg.pos_part).mpr (pos_iff_ne_zero.mpr hne))
  have hae : ∀ᵐ x ∂μ, x ∉ support (fun y ↦ max (g y) 0) := ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hzero)
  exact hae.mono fun x hx hxg ↦ False.elim (hx (mem_support.mpr ((hxg.trans_le (le_max_left _ _)).ne')))

/-- If positive lower and upper excess can coexist only for bounded
threshold ratios, the same comparison holds for almost all pairs. -/
theorem ae_pair_le_of_integral_threshold_ratio {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : Integrable f μ) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x)
    {H : ℝ} (hH : 1 ≤ H)
    (hratio : ∀ a b : ℝ, 0 ≤ a → a < b →
      0 < (∫ y, max (a - f y) 0 ∂μ) → 0 < (∫ y, max (f y - b) 0 ∂μ) → b ≤ H * a) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, f x ≤ H * f y := by
  have hupper (b : ℚ) : ∀ᵐ x ∂μ, (b : ℝ) < f x → 0 < ∫ z, max (f z - b) 0 ∂μ := by
    simpa only [Pi.sub_apply, sub_pos] using ae_integral_pos_of_posPart (hf.sub (integrable_const (b : ℝ)))
  have hlower (a : ℚ) : ∀ᵐ y ∂μ, f y < (a : ℝ) → 0 < ∫ z, max (a - f z) 0 ∂μ := by
    simpa only [Pi.sub_apply, sub_pos] using ae_integral_pos_of_posPart ((integrable_const (a : ℝ)).sub hf)
  filter_upwards [ae_all_iff.mpr hupper] with x hx
  filter_upwards [ae_all_iff.mpr hlower, hf₀] with y hy hy₀
  by_contra! h
  have hH₀ := zero_lt_one.trans_le hH
  obtain ⟨a, ha, hau⟩ := exists_rat_btwn ((lt_div_iff₀ hH₀).mpr (by rwa [mul_comm] : f y * H < f x))
  have ha₀ := hy₀.trans ha.le
  have hb' : H * (a : ℝ) < f x := by
    have hh := (lt_div_iff₀ hH₀).mp hau
    rwa [mul_comm] at hh
  obtain ⟨b, hb, hbu⟩ := exists_rat_btwn hb'
  have hab : (a : ℝ) < b := (le_mul_of_one_le_left ha₀ hH).trans_lt hb
  exact hb.not_ge (hratio a b ha₀ hab (hy a ha) (hx b hbu))

end CarpetEnergy
