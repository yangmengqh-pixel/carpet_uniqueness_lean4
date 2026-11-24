import EnergyNeighborhoodPoincare
import EnergyImageAreaScalar
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Step functions on a carpet level
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

/-- The cellwise constant function with values given by a list of level values.
The sum specifies values even on the measure-zero overlap. -/
noncomputable def wordStep {n : ℕ} (a : (Fin n → Fin 8) → ℝ) (x : CarpetPoints) : ℝ :=
  ∑ w, (range (wordMap (List.ofFn w))).indicator (fun _ ↦ a w) x

theorem wordStep_eq_of_mem {n : ℕ} (a : (Fin n → Fin 8) → ℝ)
    {x : CarpetPoints} {w : Fin n → Fin 8} (hw : x ∈ range (wordMap (List.ofFn w)))
    (hx : x ∉ carpetCellBoundary n) : wordStep a x = a w := by
  classical
  unfold wordStep
  rw [Finset.sum_eq_single w, indicator_of_mem hw]
  · intro v _ hne
    apply indicator_of_notMem
    exact fun hv ↦ hx (inter_word_subset_cellBoundary hne ⟨hv, hw⟩)
  · simp

theorem ae_notMem_carpetCellBoundary (n : ℕ) :
    ∀ᵐ x ∂carpetMeasure, x ∉ carpetCellBoundary n := by
  exact measure_eq_zero_iff_ae_notMem.mp (carpetMeasure_carpetCellBoundary_eq_zero n)

theorem memLp_wordStep {n : ℕ} (a : (Fin n → Fin 8) → ℝ) (q : ℝ≥0∞) :
    MemLp (wordStep a) q carpetMeasure := by
  classical
  have h (w : Fin n → Fin 8) :
      MemLp ((range (wordMap (List.ofFn w))).indicator (fun _ ↦ a w)) q carpetMeasure :=
    memLp_indicator_const q (measurableEmbedding_wordMap _).measurableSet_range.nullMeasurableSet
      (a w) (Or.inr (measure_ne_top _ _))
  change MemLp (fun x ↦ ∑ w, (range (wordMap (List.ofFn w))).indicator (fun _ ↦ a w) x)
    q carpetMeasure
  exact memLp_finsetSum Finset.univ (fun w _ ↦ h w)

theorem integral_abs_wordStep_rpow {n : ℕ} (a : (Fin n → Fin 8) → ℝ)
    {q : ℝ} (hq : 0 < q) :
    (∫ x, |wordStep a x| ^ q ∂carpetMeasure) =
      ((8 : ℝ)⁻¹) ^ n * ∑ w, |a w| ^ q := by
  let V (w : Fin n → Fin 8) := range (wordMap (List.ofFn w))
  have hsum := measure_restrict_wordCellUnion_eq_sum carpetMeasure
    (carpetMeasure_carpetCellBoundary_eq_zero n) (Finset.univ : Finset (Fin n → Fin 8))
  rw [wordCellUnion_univ, Measure.restrict_univ] at hsum
  have hInt : Integrable (fun x ↦ |wordStep a x| ^ q) carpetMeasure := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using
      (memLp_wordStep a (ENNReal.ofReal q)).integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
  calc
    _ = ∑ w : Fin n → Fin 8, ∫ x in V w, |wordStep a x| ^ q ∂carpetMeasure := by
      conv_lhs => rw [hsum]
      exact integral_finsetSum_measure (fun _ _ ↦ hInt.restrict)
    _ = ((8 : ℝ)⁻¹) ^ n * ∑ w, |a w| ^ q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      have hAE : ∀ᵐ x ∂carpetMeasure.restrict (V w), wordStep a x = a w := by
        filter_upwards [ae_restrict_of_ae (ae_notMem_carpetCellBoundary n),
          ae_restrict_mem (measurableEmbedding_wordMap (List.ofFn w)).measurableSet_range]
          with x hx hV
        exact wordStep_eq_of_mem a hV hx
      rw [integral_congr_ae (hAE.mono (fun x hx ↦ by rw [hx])), integral_const,
        Measure.real, Measure.restrict_apply_univ]
      dsimp only [V]
      rw [carpetMeasure_range_wordMap, ENNReal.toReal_pow, ENNReal.toReal_inv,
        ENNReal.toReal_ofNat, List.length_ofFn, smul_eq_mul]

theorem lpNorm_wordStep_le {n : ℕ} (a : (Fin n → Fin 8) → ℝ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    lpNorm (wordStep a) (ENNReal.ofReal q) carpetMeasure ≤
      (((8 : ℝ)⁻¹) ^ n) ^ q⁻¹ * (∑ w, |a w| ^ p) ^ p⁻¹ := by
  have hq := hp.trans_le hpq
  rw [lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    (memLp_wordStep a (ENNReal.ofReal q)).aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
  simp only [Real.norm_eq_abs]
  rw [integral_abs_wordStep_rpow a hq, Real.mul_rpow (by positivity) (Finset.sum_nonneg
    fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  let M := ∑ w, |a w| ^ p
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have h₁ : 1 ≤ q / p := (le_div_iff₀ hp).mpr (by simpa using hpq)
  have hpow (x : ℝ) (hx : 0 ≤ x) : (x ^ p) ^ (q / p) = x ^ q := by
    rw [← Real.rpow_mul hx, show p * (q / p) = q by field_simp]
  have hsum : (∑ w, |a w| ^ q) ≤ M ^ (q / p) := by
    have hh := sum_rpow_le_rpow_sum_of_one_le (Finset.univ : Finset (Fin n → Fin 8))
      (fun w ↦ |a w| ^ p) (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) h₁
    simpa only [hpow _ (abs_nonneg _), M] using hh
  calc
    _ ≤ (M ^ (q / p)) ^ q⁻¹ := Real.rpow_le_rpow (by positivity) hsum (inv_nonneg.mpr hq.le)
    _ = _ := by
      rw [← Real.rpow_mul hM, div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hq.ne', one_mul]

end CarpetEnergy
