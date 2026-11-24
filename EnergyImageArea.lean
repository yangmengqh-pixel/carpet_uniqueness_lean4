import EnergyMorrey
import EnergyImageAreaScalar
import CarpetNeighborhoodMass
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Null planar images in the Morrey case

Cover the range of a pair of continuous domain functions by one
coordinate rectangle per cell. The word oscillation estimate and the
finite sum inequalities give a geometric decay of the total area.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem pow_rpow_eq_rpow_pow (r : ℝ) (hr : 0 ≤ r) (n : ℕ) (s : ℝ) :
    (r ^ n) ^ s = (r ^ s) ^ n := by
  rw [← Real.rpow_natCast_mul hr, mul_comm (n : ℝ), Real.rpow_mul_natCast hr]

/-- In the case `ρ > 1`, the image of the carpet under any pair of
continuous energy-domain functions has planar Lebesgue measure zero. -/
theorem volume_range_pair_eq_zero (hρ : 1 < E.scalingFactor)
    (f g : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain)
    (hg : continuousLp p g ∈ E.domain) :
    volume (range fun x : CarpetPoints ↦ (![f x, g x] : Fin 2 → ℝ)) = 0 := by
  classical
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hρ₀ : 0 < E.scalingFactor := zero_lt_one.trans hρ
  obtain ⟨C, hC, hosc⟩ := E.exists_cell_oscillation_bound hρ
  let u : E.domain := ⟨continuousLp p f, hf⟩
  let v : E.domain := ⟨continuousLp p g, hg⟩
  let ν := E.energyMeasure u + E.energyMeasure v
  let M := (ν univ).toReal
  let H (x : CarpetPoints) := (![f x, g x] : Fin 2 → ℝ)
  let q := 2 / p
  have hq : 0 < q := div_pos zero_lt_two hp
  let r := (E.scalingFactor⁻¹) ^ q
  have hr₀ : 0 ≤ r := Real.rpow_nonneg (inv_nonneg.mpr hρ₀.le) _
  have hr₁ : r < 1 := Real.rpow_lt_one (inv_nonneg.mpr hρ₀.le) (inv_lt_one_of_one_lt₀ hρ) hq
  let σ := max r (8 / 9 : ℝ)
  have hσ₀ : 0 ≤ σ := hr₀.trans (le_max_left _ _)
  have hσ₁ : σ < 1 := max_lt hr₁ (by norm_num)
  let B := 4 * C ^ q * M ^ q
  have hB : 0 ≤ B := by dsimp only [B, M]; positivity
  have hb (n : ℕ) : volume (range H) ≤ ENNReal.ofReal (B * σ ^ n) := by
    let W := Fin n → Fin 8
    let K (w : W) := range (wordMap (List.ofFn w))
    let m (w : W) := (ν (K w)).toReal
    have hm (w : W) : 0 ≤ m w := ENNReal.toReal_nonneg
    have hν : ν (carpetCellBoundary n) = 0 := by
      dsimp only [ν]
      rw [add_apply, E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero,
        E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero, add_zero]
    have hM : ∑ w : W, m w = M := by
      have h := measure_wordCellUnion ν hν (Finset.univ : Finset W)
      rw [wordCellUnion_univ] at h
      dsimp only [M, m]
      rw [h, ENNReal.toReal_sum (fun w _ ↦ measure_ne_top ν (K w))]
    let a := C * (E.scalingFactor ^ n)⁻¹
    have ha : 0 ≤ a := mul_nonneg hC.le (inv_nonneg.mpr (pow_nonneg hρ₀.le _))
    let R (w : W) := (a * m w) ^ p⁻¹
    have hR (w : W) : 0 ≤ R w := Real.rpow_nonneg (mul_nonneg ha (hm w)) _
    let P (w : W) := H (wordMap (List.ofFn w) (bottomPoint 0))
    let L (w : W) (j : Fin 2) := P w j - R w
    let U (w : W) (j : Fin 2) := P w j + R w
    have hcover : range H ⊆ ⋃ w : W, Icc (L w) (U w) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨w, y, rfl⟩ := exists_wordMap_range n x
      refine mem_iUnion.mpr ⟨w, ?_⟩
      have hs (j : Fin 2) : |H (wordMap (List.ofFn w) y) j - P w j| ≤ R w := by
        have hle₁ : (E.energyMeasure u (K w)).toReal ≤ m w :=
          ENNReal.toReal_mono (measure_ne_top ν (K w)) (by dsimp only [ν]; simp [add_apply])
        have hle₂ : (E.energyMeasure v (K w)).toReal ≤ m w :=
          ENNReal.toReal_mono (measure_ne_top ν (K w)) (by dsimp only [ν]; simp [add_apply])
        have hbound : |H (wordMap (List.ofFn w) y) j - P w j| ^ p ≤ a * m w := by
          fin_cases j
          · have hh := hosc f hf (List.ofFn w) y (bottomPoint 0)
            rw [List.length_ofFn] at hh
            exact hh.trans (mul_le_mul_of_nonneg_left hle₁ ha)
          · have hh := hosc g hg (List.ofFn w) y (bottomPoint 0)
            rw [List.length_ofFn] at hh
            exact hh.trans (mul_le_mul_of_nonneg_left hle₂ ha)
        have hh := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) hbound
          (inv_nonneg.mpr hp.le)
        rw [Real.rpow_rpow_inv (abs_nonneg _) hp.ne'] at hh
        exact hh
      refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
      · change P w j - R w ≤ H (wordMap (List.ofFn w) y) j
        linarith [(abs_le.mp (hs j)).1]
      · change H (wordMap (List.ofFn w) y) j ≤ P w j + R w
        linarith [(abs_le.mp (hs j)).2]
    have harea (w : W) : volume (Icc (L w) (U w)) =
        ENNReal.ofReal (4 * a ^ q * m w ^ q) := by
      rw [Real.volume_Icc_pi, Fin.prod_univ_two]
      have hlen (j : Fin 2) : U w j - L w j = 2 * R w := by dsimp [L, U]; ring
      rw [hlen, hlen, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (hR w))]
      congr 1
      have hs : R w * R w = a ^ q * m w ^ q := by
        dsimp only [R, q]
        rw [← Real.rpow_add' (mul_nonneg ha (hm w)) (by positivity : p⁻¹ + p⁻¹ ≠ 0)]
        rw [show p⁻¹ + p⁻¹ = 2 / p by ring, Real.mul_rpow ha (hm w)]
      calc
        _ = 4 * (R w * R w) := by ring
        _ = _ := by rw [hs]; ring
    have hgeom : ∑ w : W, 4 * a ^ q * m w ^ q ≤ B * σ ^ n := by
      have hpow : a ^ q = C ^ q * r ^ n := by
        dsimp only [a, r]
        rw [Real.mul_rpow hC.le (inv_nonneg.mpr (pow_nonneg hρ₀.le _)), ← inv_pow,
          pow_rpow_eq_rpow_pow _ (inv_nonneg.mpr hρ₀.le)]
      rw [← Finset.mul_sum, hpow]
      rcases le_total 1 q with h₁ | h₂
      · have h := sum_rpow_le_rpow_sum_of_one_le (Finset.univ : Finset W) m hm h₁
        rw [hM] at h
        have hrσ : r ^ n ≤ σ ^ n := pow_le_pow_left₀ hr₀ (le_max_left _ _) _
        calc
          _ ≤ 4 * (C ^ q * r ^ n) * M ^ q :=
            mul_le_mul_of_nonneg_left h (by positivity)
          _ = B * r ^ n := by dsimp only [B]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hrσ hB
      · have h := sum_rpow_le_card_mul_rpow_sum_of_le_one (Finset.univ : Finset W)
          ⟨fun _ ↦ 0, Finset.mem_univ _⟩ m hm hq.le h₂
        rw [hM] at h
        have hcard : ((Finset.univ : Finset W).card : ℝ) = (8 : ℝ) ^ n := by
          simp only [W, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
        rw [hcard, pow_rpow_eq_rpow_pow _ (by norm_num : (0 : ℝ) ≤ 8)] at h
        have hp₂ : 2 ≤ p := (div_le_one hp).mp h₂
        have hscale : r * (8 : ℝ) ^ (1 - q) ≤ (8 / 9 : ℝ) := E.image_area_ratio_le hp₂
        have hscale' : (r * (8 : ℝ) ^ (1 - q)) ^ n ≤ σ ^ n :=
          pow_le_pow_left₀ (mul_nonneg hr₀ (Real.rpow_nonneg (by norm_num) _))
            (hscale.trans (le_max_right _ _)) _
        calc
          _ ≤ 4 * (C ^ q * r ^ n) * (((8 : ℝ) ^ (1 - q)) ^ n * M ^ q) :=
            mul_le_mul_of_nonneg_left h (by positivity)
          _ = B * (r * (8 : ℝ) ^ (1 - q)) ^ n := by rw [mul_pow]; dsimp only [B]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hscale' hB
    calc
      _ ≤ volume (⋃ w : W, Icc (L w) (U w)) := measure_mono hcover
      _ ≤ ∑' w : W, volume (Icc (L w) (U w)) := measure_iUnion_le _
      _ = ENNReal.ofReal (∑ w : W, 4 * a ^ q * m w ^ q) := by
        rw [tsum_fintype]
        calc
          _ = ∑ w : W, ENNReal.ofReal (4 * a ^ q * m w ^ q) :=
            Finset.sum_congr rfl (fun w _ ↦ harea w)
          _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun w _ ↦
            mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg ha _)) (Real.rpow_nonneg (hm w) _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hgeom
  have hfinite : volume (range H) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb 0)
  have hl : Tendsto (fun n : ℕ ↦ B * σ ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hσ₀ hσ₁).const_mul B
  have hz : (volume (range H)).toReal ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hl (Eventually.of_forall fun n ↦ by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb n)
      rw [ENNReal.toReal_ofReal (mul_nonneg hB (pow_nonneg hσ₀ _))] at h
      exact h)
  change volume (range H) = 0
  rw [← ENNReal.ofReal_toReal hfinite, hz.antisymm ENNReal.toReal_nonneg, ENNReal.ofReal_zero]

end CarpetEnergy.SelfSimilarPEnergy
