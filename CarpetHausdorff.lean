import CarpetGrid
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Hausdorff normalization of the carpet measure

The natural cell probability agrees with Hausdorff measure at the
similarity dimension after normalization.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy

/-- The similarity dimension of the eight maps of ratio one third. -/
noncomputable def carpetSimilarityDimension : ℝ := Real.log 8 / Real.log 3

theorem carpetSimilarityDimension_pos : 0 < carpetSimilarityDimension :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

theorem real_three_rpow_carpetSimilarityDimension :
    (3 : ℝ) ^ carpetSimilarityDimension = 8 := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  have he : Real.log 3 * carpetSimilarityDimension = Real.log 8 := by
    unfold carpetSimilarityDimension
    rw [mul_div_cancel₀ (Real.log 8) (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne']
  rw [he, Real.exp_log (by norm_num)]

private theorem three_rpow_carpetSimilarityDimension :
    (3 : ℝ≥0∞) ^ carpetSimilarityDimension = 8 := by
  have h := congrArg ENNReal.ofReal real_three_rpow_carpetSimilarityDimension
  rwa [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    carpetSimilarityDimension_pos.le, ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat] at h

private theorem ternary_radius_rpow_dimension (n : ℕ) :
    ((3⁻¹ : ℝ≥0∞) ^ n) ^ carpetSimilarityDimension = ((8 : ℝ≥0∞)⁻¹) ^ n := by
  rw [← ENNReal.rpow_natCast_mul, mul_comm (n : ℝ), ENNReal.rpow_mul_natCast,
    ENNReal.inv_rpow, three_rpow_carpetSimilarityDimension]

theorem ofReal_ternary_radius (n : ℕ) :
    ENNReal.ofReal ((1 / 3 : ℝ) ^ n) = (3⁻¹ : ℝ≥0∞) ^ n := by
  rw [ENNReal.ofReal_pow (by norm_num)]
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

private theorem cell_lipschitz (i : Fin 8) : LipschitzWith (3⁻¹ : ℝ≥0) (cellMap i) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    change dist (cellSimilarity i x) (cellSimilarity i y) ≤ _ * dist (x : Plane) (y : Plane)
    rw [dist_cellSimilarity]
    norm_num

private theorem cell_antilipschitz (i : Fin 8) : AntilipschitzWith (3 : ℝ≥0) (cellMap i) :=
  AntilipschitzWith.of_le_mul_dist fun x y ↦ by
    change dist (x : Plane) (y : Plane) ≤ (3 : ℝ) * dist (cellSimilarity i x) (cellSimilarity i y)
    rw [dist_cellSimilarity]
    linarith

private theorem hausdorffMeasure_image_cellMap (i : Fin 8) (A : Set CarpetPoints) :
    μH[carpetSimilarityDimension] (cellMap i '' A) =
      (8 : ℝ≥0∞)⁻¹ * μH[carpetSimilarityDimension] A := by
  have hl := (cell_lipschitz i).hausdorffMeasure_image_le carpetSimilarityDimension_pos.le A
  rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat, ENNReal.inv_rpow,
    three_rpow_carpetSimilarityDimension] at hl
  refine le_antisymm hl ?_
  have ha := (cell_antilipschitz i).le_hausdorffMeasure_image carpetSimilarityDimension_pos.le A
  rw [ENNReal.coe_ofNat, three_rpow_carpetSimilarityDimension] at ha
  calc
    _ ≤ (8 : ℝ≥0∞)⁻¹ * (8 * μH[carpetSimilarityDimension] (cellMap i '' A)) :=
      mul_le_mul' le_rfl ha
    _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem hausdorffMeasure_range_wordMap (w : List (Fin 8)) :
    μH[carpetSimilarityDimension] (range (wordMap w)) =
      ((8 : ℝ≥0∞)⁻¹) ^ w.length * μH[carpetSimilarityDimension] (univ : Set CarpetPoints) := by
  induction w with
  | nil => simp [wordMap]
  | cons i w ih =>
    rw [wordMap, range_comp, hausdorffMeasure_image_cellMap, ih, List.length_cons, pow_succ', mul_assoc]

/-- At the similarity dimension the total Hausdorff mass is finite. -/
theorem hausdorffMeasure_carpet_ne_top :
    μH[carpetSimilarityDimension] (univ : Set CarpetPoints) ≠ ∞ := by
  let K (n : ℕ) (w : Fin n → Fin 8) := range (wordMap (List.ofFn w))
  let D := ENNReal.ofReal (diam (univ : Set CarpetPoints))
  let r (n : ℕ) := (3⁻¹ : ℝ≥0∞) ^ n * D
  have hr : Tendsto r atTop (𝓝 0) := by
    have ht := ENNReal.continuous_ofReal.tendsto _ |>.comp tendsto_wordMap_radius
    have he (n : ℕ) : ENNReal.ofReal ((1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints)) = r n := by
      rw [ENNReal.ofReal_mul (by positivity), ofReal_ternary_radius]
    simpa only [Function.comp_def, he, ENNReal.ofReal_zero] using ht
  have hK (n : ℕ) (w : Fin n → Fin 8) : ediam (K n w) ≤ r n := by
    have h := ediam_le_of_forall_dist_le (fun _ hx _ hy ↦ wordMap_dist_le n w hx hy)
    simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 / 3) ^ n), ofReal_ternary_radius]
      using h
  have hcover (n : ℕ) : (univ : Set CarpetPoints) ⊆ ⋃ w, K n w := fun x _ ↦
    mem_iUnion.mpr (exists_wordMap_range n x)
  have hH := Measure.hausdorffMeasure_le_liminf_sum carpetSimilarityDimension univ r hr K
    (Eventually.of_forall hK) (Eventually.of_forall hcover)
  have hcost (n : ℕ) : (∑ w, ediam (K n w) ^ carpetSimilarityDimension) ≤ D ^ carpetSimilarityDimension := by
    calc
      _ ≤ ∑ _ : Fin n → Fin 8, (r n) ^ carpetSimilarityDimension :=
        Finset.sum_le_sum fun w _ ↦ ENNReal.rpow_le_rpow (hK n w) carpetSimilarityDimension_pos.le
      _ = _ := by
        change (∑ _ : Fin n → Fin 8, ((3⁻¹ : ℝ≥0∞) ^ n * D) ^ carpetSimilarityDimension) = _
        rw [ENNReal.mul_rpow_of_nonneg _ _ carpetSimilarityDimension_pos.le, ternary_radius_rpow_dimension]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc]
        rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
  have hlim : liminf (fun n ↦ ∑ w, ediam (K n w) ^ carpetSimilarityDimension) atTop ≤
      liminf (fun _ : ℕ ↦ D ^ carpetSimilarityDimension) atTop :=
    Filter.liminf_le_liminf (Eventually.of_forall hcost)
  have hf : μH[carpetSimilarityDimension] (univ : Set CarpetPoints) ≤ D ^ carpetSimilarityDimension :=
    hH.trans (by simpa using hlim)
  exact ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg carpetSimilarityDimension_pos.le ENNReal.ofReal_ne_top) hf

theorem exists_consecutive_ternary_bounds {d : ℝ≥0∞} (hd : d ≠ 0) (hle : d ≤ 1) :
    ∃ n : ℕ, (3⁻¹ : ℝ≥0∞) ^ (n + 1) < d ∧ d ≤ (3⁻¹ : ℝ≥0∞) ^ n := by
  have hex : ∃ n : ℕ, (3⁻¹ : ℝ≥0∞) ^ n < d := by
    by_contra! h
    apply hd
    exact ENNReal.eq_zero_of_le_mul_pow (ε := 1) (by norm_num : (3⁻¹ : ℝ≥0∞) < 1)
      (fun n ↦ by simpa only [ENNReal.coe_one, one_mul] using h n)
  let k := Nat.find hex
  have hk : (3⁻¹ : ℝ≥0∞) ^ k < d := Nat.find_spec hex
  have hk₀ : k ≠ 0 := by
    intro h
    rw [h, pow_zero] at hk
    exact hk.not_ge hle
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk₀
  refine ⟨n, ?_, ?_⟩
  · rwa [hn] at hk
  have hnot : ¬ (3⁻¹ : ℝ≥0∞) ^ n < d := Nat.find_min hex (show n < k by omega)
  exact le_of_not_gt hnot

private theorem carpetMeasure_eq_zero_of_ediam_eq_zero {A : Set CarpetPoints} (hA : ediam A = 0) :
    carpetMeasure A = 0 := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact measure_empty
  have he : A.Subsingleton := ediam_eq_zero_iff.mp hA
  exact measure_mono_null (fun y hy ↦ by
    change (y : Plane) 0 = (x : Plane) 0
    rw [he hy hx]) (carpetMeasure_coordinateLevel 0 ((x : Plane) 0))

/-- A diameter bound for the cell probability at the similarity dimension. -/
theorem carpetMeasure_le_ediam_rpow (A : Set CarpetPoints) (hA : ediam A ≤ 1) :
    carpetMeasure A ≤ 200 * ediam A ^ carpetSimilarityDimension := by
  by_cases he : ediam A = 0
  · rw [carpetMeasure_eq_zero_of_ediam_eq_zero he]
    exact bot_le
  obtain ⟨n, hl, hu⟩ := exists_consecutive_ternary_bounds he hA
  have h := carpetMeasure_le_of_small_ediam A n (by rwa [ofReal_ternary_radius])
  calc
    _ ≤ 25 * ((8 : ℝ≥0∞)⁻¹) ^ n := h
    _ = 200 * ((8 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
      have hc : (200 : ℝ≥0∞) * 8⁻¹ = 25 := by
        rw [show (200 : ℝ≥0∞) = 25 * 8 by norm_num, mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
      rw [pow_succ', ← mul_assoc, hc]
    _ ≤ _ := by
      rw [← ternary_radius_rpow_dimension]
      exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hl.le carpetSimilarityDimension_pos.le)

/-- The Hausdorff measure at the similarity dimension is nonzero. -/
theorem hausdorffMeasure_carpet_ne_zero :
    μH[carpetSimilarityDimension] (univ : Set CarpetPoints) ≠ 0 := by
  let ν := (200 : ℝ≥0∞)⁻¹ • carpetMeasure
  have hle : ν ≤ μH[carpetSimilarityDimension] := by
    apply Measure.le_hausdorffMeasure carpetSimilarityDimension ν 1 one_pos
    intro A hA
    change ((200 : ℝ≥0∞)⁻¹ • carpetMeasure) A ≤ _
    rw [smul_apply, smul_eq_mul]
    calc
      _ ≤ (200 : ℝ≥0∞)⁻¹ * (200 * ediam A ^ carpetSimilarityDimension) :=
        mul_le_mul' le_rfl (carpetMeasure_le_ediam_rpow A hA)
      _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hν : ν univ = (200 : ℝ≥0∞)⁻¹ := by
    change ((200 : ℝ≥0∞)⁻¹ • carpetMeasure) univ = _
    rw [smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ((by norm_num : (0 : ℝ≥0∞) < 200⁻¹).trans_le (hν ▸ hle univ)).ne'

/-- The cell probability is normalized Hausdorff measure at the similarity dimension. -/
theorem carpetMeasure_eq_normalized_hausdorffMeasure :
    carpetMeasure =
      (μH[carpetSimilarityDimension] (univ : Set CarpetPoints))⁻¹ • μH[carpetSimilarityDimension] := by
  symm
  apply eq_carpetMeasure_of_cell_masses
  intro w
  rw [smul_apply, smul_eq_mul, hausdorffMeasure_range_wordMap]
  let M := μH[carpetSimilarityDimension] (univ : Set CarpetPoints)
  calc
    _ = M⁻¹ * M * ((8 : ℝ≥0∞)⁻¹) ^ w.length := by change M⁻¹ * (_ * M) = _; ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hausdorffMeasure_carpet_ne_zero hausdorffMeasure_carpet_ne_top,
      one_mul]

/-- The Euclidean Hausdorff dimension of the standard carpet. -/
theorem dimH_carpet : dimH (carpet : Set Plane) = ENNReal.ofReal carpetSimilarityDimension := by
  let d : ℝ≥0 := ⟨carpetSimilarityDimension, carpetSimilarityDimension_pos.le⟩
  have hp : dimH (univ : Set CarpetPoints) = (d : ℝ≥0∞) :=
    dimH_of_hausdorffMeasure_ne_zero_ne_top hausdorffMeasure_carpet_ne_zero hausdorffMeasure_carpet_ne_top
  have he : (Subtype.val : CarpetPoints → Plane) '' (univ : Set CarpetPoints) = (carpet : Set Plane) := by
    rw [image_univ, Subtype.range_coe]
  rw [← he, (show Isometry (Subtype.val : CarpetPoints → Plane) from isometry_subtypeVal).dimH_image,
    hp]
  exact (ENNReal.ofReal_coe_nnreal).symm

end CarpetEnergy
