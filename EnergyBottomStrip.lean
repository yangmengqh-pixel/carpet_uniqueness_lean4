import CarpetHorizontalRows

/-!
# Corrections supported in the bottom strip

A continuous domain function vanishing on the other three sides can be
copied, with horizontal length scaling, into the bottom cells. The
number of these cells gives a summable energy estimate.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem card_bottom_words_le (n : ℕ) :
    Fintype.card {w : Fin n → Fin 8 // gridCoordinate (List.ofFn w) 1 = 0} ≤ 3 ^ n := by
  let W := {w : Fin n → Fin 8 // gridCoordinate (List.ofFn w) 1 = 0}
  let F (w : W) : Fin (3 ^ n) := ⟨gridCoordinate (List.ofFn w.val) 0,
    by simpa only [List.length_ofFn] using gridCoordinate_lt (List.ofFn w.val) 0⟩
  have hF : Injective F := by
    intro w v h
    apply Subtype.ext
    apply List.ofFn_injective
    apply gridCoordinate_injective_of_length (by simp)
    intro j
    fin_cases j
    · exact congrArg (fun k : Fin (3 ^ n) ↦ k.val) h
    · exact w.property.trans v.property.symm
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective F hF

private theorem bottom_cell_pieces_agree
    (δ : C(CarpetPoints, ℝ))
    (hδ : ∀ x : CarpetPoints, (x : Plane) 0 = 0 ∨ (x : Plane) 0 = 1 ∨ (x : Plane) 1 = 1 → δ x = 0)
    (n : ℕ) (w v : Fin n → Fin 8) (x y : CarpetPoints)
    (he : wordMap (List.ofFn w) x = wordMap (List.ofFn v) y) :
    (if gridCoordinate (List.ofFn w) 1 = 0 then ((3 : ℝ) ^ n)⁻¹ * δ x else 0) =
      if gridCoordinate (List.ofFn v) 1 = 0 then ((3 : ℝ) ^ n)⁻¹ * δ y else 0 := by
  have hl : (List.ofFn w).length = (List.ofFn v).length := by simp
  have hxy := (wordMap_eq_iff_grid_coordinate hl x y).mp he
  by_cases hw : gridCoordinate (List.ofFn w) 1 = 0
  · rw [ite_eq_left hw]
    by_cases hv : gridCoordinate (List.ofFn v) 1 = 0
    · rw [ite_eq_left hv]
      by_cases h₀ : gridCoordinate (List.ofFn w) 0 = gridCoordinate (List.ofFn v) 0
      · have h : w = v := List.ofFn_injective (gridCoordinate_injective_of_length hl
          (by intro j; fin_cases j; exact h₀; exact hw.trans hv.symm))
        subst v
        rw [(measurableEmbedding_wordMap (List.ofFn w)).injective he]
      · obtain ⟨a, b, ha, hb, _⟩ := overlap_coord_endpoints
          (carpet_coord_mem_Icc x 0) (carpet_coord_mem_Icc y 0) (hxy 0) h₀
        have hside (c : Fin 2) (z : CarpetPoints) (hz : (z : Plane) 0 = c.val) :
            δ z = 0 := by
          fin_cases c
          · exact hδ z (Or.inl hz)
          · exact hδ z (Or.inr (Or.inl hz))
        rw [hside a x ha, hside b y hb]
    · rw [ite_eq_right hv]
      have h := hxy 1
      rw [hw, Nat.cast_zero, zero_add] at h
      have h1 : (1 : ℝ) ≤ gridCoordinate (List.ofFn v) 1 := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hv
      have hb := carpet_coord_mem_Icc y 1
      have hx : (x : Plane) 1 = 1 := by linarith [(carpet_coord_mem_Icc x 1).2, hb.1]
      rw [hδ x (Or.inr (Or.inr hx)), mul_zero]
  · rw [ite_eq_right hw]
    by_cases hv : gridCoordinate (List.ofFn v) 1 = 0
    · rw [ite_eq_left hv]
      have h := hxy 1
      rw [hv, Nat.cast_zero, zero_add] at h
      have h1 : (1 : ℝ) ≤ gridCoordinate (List.ofFn w) 1 := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hw
      have hb := carpet_coord_mem_Icc x 1
      have hy : (y : Plane) 1 = 1 := by linarith [(carpet_coord_mem_Icc y 1).2, hb.1]
      rw [hδ y (Or.inr (Or.inr hy)), mul_zero]
    · rw [ite_eq_right hv]

/-- Place scaled copies of a correction into the bottom row of a word level. -/
theorem exists_bottom_strip_correction (δ : C(CarpetPoints, ℝ))
    (hδ : continuousLp p δ ∈ E.domain)
    (hside : ∀ x : CarpetPoints, (x : Plane) 0 = 0 ∨ (x : Plane) 0 = 1 ∨ (x : Plane) 1 = 1 → δ x = 0)
    (n : ℕ) :
    ∃ (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain),
      (∀ (w : Fin n → Fin 8) x, u (wordMap (List.ofFn w) x) =
        if gridCoordinate (List.ofFn w) 1 = 0 then ((3 : ℝ) ^ n)⁻¹ * δ x else 0) ∧
      ‖u‖ ≤ ((3 : ℝ) ^ n)⁻¹ * ‖δ‖ ∧
      (E.energy ⟨continuousLp p u, hu⟩ : ℝ) ≤
        (E.scalingFactor * (3 : ℝ) ^ (1 - p)) ^ n * (E.energy ⟨continuousLp p δ, hδ⟩ : ℝ) := by
  classical
  let Q := E.zeroComponent
  let a := ((3 : ℝ) ^ n)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let G (w : Fin n → Fin 8) := if gridCoordinate (List.ofFn w) 1 = 0 then a • δ else
    ContinuousMap.const CarpetPoints (0 : ℝ)
  have hG (w : Fin n → Fin 8) : G w ∈ Q.continuousKernel := by
    by_cases hw : gridCoordinate (List.ofFn w) 1 = 0
    · have hm : δ ∈ Q.continuousKernel := ⟨hδ, rfl⟩
      simpa only [G, ite_eq_left hw] using Q.continuousKernel_smul a hm
    · simpa only [G, ite_eq_right hw] using Q.continuousKernel_const 0
  have hG_apply (w : Fin n → Fin 8) (x : CarpetPoints) :
      G w x = if gridCoordinate (List.ofFn w) 1 = 0 then a * δ x else 0 := by
    by_cases h : gridCoordinate (List.ofFn w) 1 = 0 <;> simp [G, h]
  obtain ⟨u, ⟨hu, _⟩, hcell⟩ := Q.exists_continuousKernel_cellwise n G hG
    (fun w v x y he ↦ by
      rw [hG_apply, hG_apply]
      exact bottom_cell_pieces_agree δ hside n w v x y he)
  refine ⟨u, hu, fun w x ↦ (hcell w x).trans (hG_apply w x), ?_, ?_⟩
  · apply (ContinuousMap.norm_le u (mul_nonneg ha (norm_nonneg _))).mpr
    intro z
    obtain ⟨w, x, rfl⟩ := exists_wordMap_range n z
    rw [hcell, hG_apply]
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using δ.norm_coe_le_norm x) ha
    · rw [norm_zero]
      exact mul_nonneg ha (norm_nonneg _)
  let g : E.domain := ⟨continuousLp p u, hu⟩
  let d : E.domain := ⟨continuousLp p δ, hδ⟩
  let s := (E.energy d : ℝ)
  let B := Finset.univ.filter fun w : Fin n → Fin 8 ↦ gridCoordinate (List.ofFn w) 1 = 0
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hrpow (f : E.domain) : E.rootSeminorm f ^ p = (E.energy f : ℝ) := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'
  have hpiece (w : Fin n → Fin 8) :
      (E.energy (E.pullbackWord (List.ofFn w) g) : ℝ) =
        if w ∈ B then a ^ p * s else 0 := by
    have he := continuousLp_interpolate_word_eq u hu (G w) (List.ofFn w) (hcell w)
    by_cases hw : gridCoordinate (List.ofFn w) 1 = 0
    · have hf : E.pullbackWord (List.ofFn w) g = a • d := by
        apply Subtype.ext
        rw [← he, show G w = a • δ from ite_eq_left hw]
        exact (continuousLpLinear p).map_smul a δ
      have hwB : w ∈ B := by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hw
      rw [ite_eq_left hwB, hf, ← hrpow (a • d), map_smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg ha, Real.mul_rpow ha (apply_nonneg _ _), hrpow d]
    · have hf : E.pullbackWord (List.ofFn w) g = ⟨constantLp p 0, E.constant_mem 0⟩ := by
        apply Subtype.ext
        rw [← he, show G w = ContinuousMap.const _ 0 from ite_eq_right hw]
        apply Lp.ext
        exact (continuousLp_ae_eq p _).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure 0).symm
      have hz := (E.zero_iff_constant ⟨constantLp p 0, E.constant_mem 0⟩).2 ⟨0, rfl⟩
      have hwB : w ∉ B := by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hw
      rw [ite_eq_right hwB, hf, hz, NNReal.coe_zero]
  have hcard : B.card ≤ 3 ^ n := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun w ↦ by simp [B]))).trans_le
      (card_bottom_words_le n)
  have hcard' : (B.card : ℝ) ≤ (3 : ℝ) ^ n := by exact_mod_cast hcard
  have hρ := E.isScalingFactor_scalingFactor.1
  change (E.energy g : ℝ) ≤ _
  calc
    _ = E.scalingFactor ^ n * ∑ w : Fin n → Fin 8, (E.energy (E.pullbackWord (List.ofFn w) g) : ℝ) :=
      E.energy_eq_sum_words n g
    _ = E.scalingFactor ^ n * ((B.card : ℝ) * (a ^ p * s)) := by
      simp only [hpiece, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
    _ ≤ E.scalingFactor ^ n * ((3 : ℝ) ^ n * (a ^ p * s)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcard' (mul_nonneg (Real.rpow_nonneg ha _) (NNReal.coe_nonneg _)))
        (pow_nonneg hρ.le _)
    _ = _ := by
      have h3 : 0 < (3 : ℝ) := by norm_num
      have ht : 0 < (3 : ℝ) ^ n := pow_pos h3 _
      have h : (3 : ℝ) ^ n * a ^ p = ((3 : ℝ) ^ (1 - p)) ^ n := by
        have ha' : a ^ p = ((3 : ℝ) ^ n) ^ (-p) :=
          (Real.inv_rpow ht.le _).trans (Real.rpow_neg ht.le _).symm
        calc
          _ = ((3 : ℝ) ^ n) ^ (1 : ℝ) * ((3 : ℝ) ^ n) ^ (-p) := by rw [Real.rpow_one, ha']
          _ = ((3 : ℝ) ^ n) ^ (1 - p) := (Real.rpow_add ht 1 (-p)).symm
          _ = _ := by
            rw [← Real.rpow_natCast_mul h3.le, mul_comm (n : ℝ), Real.rpow_mul_natCast h3.le]
      change E.scalingFactor ^ n * ((3 : ℝ) ^ n * (a ^ p * s)) =
        (E.scalingFactor * (3 : ℝ) ^ (1 - p)) ^ n * s
      rw [mul_pow, ← h]
      ring

end CarpetEnergy.SelfSimilarPEnergy
