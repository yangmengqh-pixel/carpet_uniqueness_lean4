import SmoothMollification

/-!
# Comparing arbitrary small radii with the mollifier sequence
-/

namespace CarpetEnergy

theorem exists_mollifier_half_radius_bracket {r : ℝ} (hr : 0 < r) (hR : r ≤ 1 / 2) :
    ∃ n : ℕ, r ≤ (1 / ((n : ℝ) + 1)) / 2 ∧ 1 / ((n : ℝ) + 1) ≤ 4 * r := by
  let a := 1 / (2 * r)
  have ha : 0 ≤ a := div_nonneg zero_le_one (by positivity)
  have ha1 : 1 ≤ a := (le_div_iff₀ (by positivity : 0 < 2 * r)).mpr (by linarith)
  let N := ⌊a⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff ha).mpr (by exact_mod_cast ha1)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hN1
  have hNle : (N : ℝ) ≤ a := Nat.floor_le ha
  have halt : a < (N : ℝ) + 1 := Nat.lt_floor_add_one a
  let n := N - 1
  have he : (n : ℝ) + 1 = (N : ℝ) := by
    dsimp only [n]
    rw [Nat.cast_sub hN, Nat.cast_one, sub_add_cancel]
  refine ⟨n, ?_, ?_⟩
  · rw [he]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (le_div_iff₀ hNpos).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * r)).mp hNle
    linarith only [show r * 2 * (N : ℝ) = (N : ℝ) * (2 * r) by ring, hh]
  · rw [he]
    apply (div_le_iff₀ hNpos).mpr
    have hh : a ≤ 2 * (N : ℝ) := halt.le.trans (by linarith)
    have h := (div_le_iff₀ (by positivity : 0 < 2 * r)).mp hh
    linarith only [show 4 * r * (N : ℝ) = 2 * (N : ℝ) * (2 * r) by ring, h]

end CarpetEnergy
