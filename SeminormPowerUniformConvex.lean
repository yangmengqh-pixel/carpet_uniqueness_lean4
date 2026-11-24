import ScalarPowerMidpoint

/-!
# The p-power midpoint deficit implies uniform convexity
-/

namespace CarpetEnergy

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

theorem uniformConvexSpace_of_power_midpoint (S : Seminorm ℝ X) {p : ℝ} (hp : 1 < p)
    (h : ∀ ε > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ f g : X,
      S (f - g) ^ p + C * S ((1 / 2 : ℝ) • (f + g)) ^ p ≤
        (ε + C / 2) * (S f ^ p + S g ^ p)) :
    letI := S.toAddGroupSeminorm.toSeminormedAddCommGroup
    UniformConvexSpace X := by
  let : SeminormedAddCommGroup X := S.toAddGroupSeminorm.toSeminormedAddCommGroup
  have hp₀ := zero_lt_one.trans hp
  refine ⟨fun {ε} hε ↦ ?_⟩
  let a := ε ^ p / 4
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hε _) (by norm_num)
  obtain ⟨C, hC, hgap⟩ := h a ha
  let q := max (1 - ε ^ p / (2 * (C + 1))) 0
  have hq : 0 ≤ q := le_max_right _ _
  have hq1 : q < 1 := max_lt
    (sub_lt_self _ (div_pos (Real.rpow_pos_of_pos hε _) (by positivity))) zero_lt_one
  have hqpow : q ^ p⁻¹ < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 (inv_pos.mpr hp₀)
  refine ⟨2 * (1 - q ^ p⁻¹), by positivity, fun {x} hx {y} hy hxy ↦ ?_⟩
  change S x = 1 at hx
  change S y = 1 at hy
  change ε ≤ S (x - y) at hxy
  change S (x + y) ≤ _
  let m := (1 / 2 : ℝ) • (x + y)
  have hm : S m = (1 / 2 : ℝ) * S (x + y) := by
    dsimp only [m]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  have hm1 : S m ≤ 1 := by
    have hxy := S.add_le' x y
    change S (x + y) ≤ S x + S y at hxy
    rw [hx, hy] at hxy
    linarith only [hm, hxy]
  have hm1p : S m ^ p ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (apply_nonneg S _) hm1 hp₀.le
  have hd := Real.rpow_le_rpow hε.le hxy hp₀.le
  have hmain := hgap x y
  change S (x - y) ^ p + C * S m ^ p ≤ _ at hmain
  rw [hx, hy, Real.one_rpow] at hmain
  have hb : ε ^ p / 2 ≤ (C + 1) * (1 - S m ^ p) := by
    dsimp only [a] at hmain
    linarith only [hd, hmain, hm1p]
  have hxq : S m ^ p ≤ q := by
    apply le_trans _ (le_max_left _ _)
    have hpos : 0 < 2 * (C + 1) := by positivity
    have hh : ε ^ p / (2 * (C + 1)) ≤ 1 - S m ^ p := by
      apply (div_le_iff₀ hpos).mpr
      nlinarith only [hb]
    linarith only [hh]
  have hfin := Real.rpow_le_rpow (Real.rpow_nonneg (apply_nonneg S _) _) hxq (inv_nonneg.mpr hp₀.le)
  rw [Real.rpow_rpow_inv (apply_nonneg S _) hp₀.ne'] at hfin
  linarith only [hm, hfin]

end CarpetEnergy
