import CarpetHausdorff
import EnergyLinearBoundaryProfile

/-!
# Lower bounds on the p-walk dimension

The coordinate interpolants are opposite-side capacity competitors.
Self-similarity gives their energy as a geometric progression, so the
positive capacity rules out a progression with ratio below one.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The renormalization factor is at least the scale of the coordinate energies. -/
theorem three_rpow_div_eight_le_scalingFactor :
    (3 : ℝ) ^ p / 8 ≤ E.scalingFactor := by
  obtain ⟨P⟩ := E.exists_zeroCornerProfile
  choose g hg hG using P.exists_coordinate_interp
  let d : E.domain := ⟨continuousLp p P.toContinuousMap, P.mem_kernel.choose⟩
  let q := 8 * E.scalingFactor / (3 : ℝ) ^ p
  have hρ := E.isScalingFactor_scalingFactor.1
  have h3 : 0 < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  by_contra! hlt
  have hq : q < 1 := (div_lt_one h3).mpr (by linarith)
  have hL : 0 ≤ q := div_nonneg (mul_nonneg (by norm_num) hρ.le) h3.le
  have hl : Tendsto (fun n : ℕ ↦ q ^ n * (E.energy d : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hL hq).mul_const (E.energy d : ℝ)
  have hc (n : ℕ) : E.leftRightCapacity ≤ q ^ n * (E.energy d : ℝ) := by
    have hb (x : CarpetPoints) : 0 ≤ g n x ∧ g n x ≤ 1 := by
      obtain ⟨w, z, rfl⟩ := exists_wordMap_range n x
      have hf : 0 < (3 : ℝ) ^ n := by positivity
      have hh := gridCoordinate_lt (List.ofFn w) 0
      rw [List.length_ofFn] at hh
      have hi : (gridCoordinate (List.ofFn w) 0 : ℝ) + 1 ≤ (3 : ℝ) ^ n := by
        exact_mod_cast Nat.succ_le_of_lt hh
      rw [hG n]
      exact ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) (P.bounds z).1) hf.le,
        (div_le_one hf).mpr ((add_le_add_right (P.bounds z).2 _).trans hi)⟩
    let u : E.LeftRightProfile := ⟨g n, (hg n).choose,
      E.coordinate_interp_side P n (g n) (hG n) 0,
      E.coordinate_interp_side P n (g n) (hG n) 1, hb⟩
    apply (E.leftRightCapacity_le_energy u).trans_eq
    rw [E.energy_eq_sum_words n]
    let k := ((3 : ℝ) ^ n)⁻¹
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hcell (w : Fin n → Fin 8) :
        (E.energy (E.pullbackWord (List.ofFn w) (u.toDomain E)) : ℝ) = k ^ p * (E.energy d : ℝ) := by
      let c := (gridCoordinate (List.ofFn w) 0 : ℝ) / (3 : ℝ) ^ n
      let z := k • P.toContinuousMap + ContinuousMap.const CarpetPoints c
      have hz (x : CarpetPoints) : g n (wordMap (List.ofFn w) x) = z x := by
        rw [hG n]
        change (_ + P.toContinuousMap x) / (3 : ℝ) ^ n = k * P.toContinuousMap x + c
        dsimp only [k, c]
        rw [add_div, div_eq_mul_inv (P.toContinuousMap x), mul_comm (P.toContinuousMap x), add_comm]
      have he := continuousLp_interpolate_word_eq (g n) (hg n).choose z _ hz
      have hfun : E.pullbackWord (List.ofFn w) (u.toDomain E) =
          k • d + ⟨constantLp p c, E.constant_mem c⟩ := by
        apply Subtype.ext
        change ((E.pullbackWord (List.ofFn w) ⟨continuousLp p (g n), (hg n).choose⟩ :
          E.domain) : CarpetLp p) = _
        rw [← he]
        change continuousLpLinear p z = _
        dsimp only [z]
        rw [map_add, map_smul]
        congr 1
      rw [hfun, E.add_constant, E.smul_energy, abs_of_nonneg hk]
    simp only [hcell, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hkp : k ^ p = (((3 : ℝ) ^ p) ^ n)⁻¹ := by
      have h3₀ : 0 ≤ (3 : ℝ) := by norm_num
      dsimp only [k]
      rw [Real.inv_rpow (pow_nonneg h3₀ _), ← Real.rpow_natCast_mul h3₀,
        mul_comm (n : ℝ), Real.rpow_mul_natCast h3₀]
    have hq' : q ^ n = (8 : ℝ) ^ n * E.scalingFactor ^ n * (((3 : ℝ) ^ p) ^ n)⁻¹ := by
      dsimp only [q]
      rw [div_pow, mul_pow, div_eq_mul_inv]
    rw [hkp, hq']
    let a := E.scalingFactor ^ n
    let b := (8 : ℝ) ^ n
    let c := (((3 : ℝ) ^ p) ^ n)⁻¹
    let e := (E.energy d : ℝ)
    change a * (b * (c * e)) = b * a * c * e
    ring
  exact E.leftRightCapacity_pos.not_ge
    (le_of_tendsto_of_tendsto tendsto_const_nhds hl (Eventually.of_forall hc))

/-- The walk dimension associated to the scale in Definition 2.1. -/
noncomputable def walkDimension : ℝ := Real.log (8 * E.scalingFactor) / Real.log 3

theorem le_walkDimension : p ≤ E.walkDimension := by
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  unfold walkDimension
  apply (le_div_iff₀ h3).mpr
  have hρ : (3 : ℝ) ^ p ≤ 8 * E.scalingFactor := by
    linarith [(div_le_iff₀ (show 0 < (8 : ℝ) by norm_num)).mp E.three_rpow_div_eight_le_scalingFactor]
  have h := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) p) hρ
  rwa [Real.log_rpow (by norm_num)] at h

theorem half_carpetDimension_lt_walkDimension : carpetSimilarityDimension / 2 < E.walkDimension := by
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hd : carpetSimilarityDimension < 2 := by
    unfold carpetSimilarityDimension
    apply (div_lt_iff₀ h3).mpr
    have h := Real.log_lt_log (by norm_num : 0 < (8 : ℝ)) (by norm_num : (8 : ℝ) < 3 ^ (2 : ℕ))
    rw [Real.log_pow] at h
    simpa only [Nat.cast_ofNat] using h
  exact (show carpetSimilarityDimension / 2 < p by linarith [E.one_lt_p]).trans_le E.le_walkDimension

end CarpetEnergy.SelfSimilarPEnergy
