import EnergyStationaryVariation
import FiniteEnergyHolder

/-!
# Hölder bounds on weighted cell first variations
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem rootSeminorm_rpow_eq_energy (f : E.domain) :
    (E.rootSeminorm f) ^ p = (E.energy f : ℝ) := by
  rw [E.rootSeminorm_apply]
  exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) (zero_lt_one.trans E.one_lt_p).ne'

theorem rootSeminorm_rpow_conj {q : ℝ} (hpq : p.HolderConjugate q) (f : E.domain) :
    (E.rootSeminorm f) ^ (p - 1) = (E.energy f : ℝ) ^ q⁻¹ := by
  rw [E.rootSeminorm_apply, ← Real.rpow_mul (NNReal.coe_nonneg _), ← hpq.div_conj_eq_sub_one]
  congr 1
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hpq.ne_zero, one_mul]

theorem energyMeasure_real_word (f : E.domain) (w : List (Fin 8)) :
    (E.energyMeasure f).real (range (wordMap w)) =
      E.scalingFactor ^ w.length * (E.energy (E.pullbackWord w f) : ℝ) := by
  rw [Measure.real, E.energyMeasure_range_word, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal E.isScalingFactor_scalingFactor.1.le, ENNReal.coe_toReal]

theorem sum_energyMeasure_real_word (f : E.domain) (n : ℕ) :
    (∑ w : Fin n → Fin 8, (E.energyMeasure f).real (range (wordMap (List.ofFn w)))) =
      (E.energy f : ℝ) := by
  simp only [E.energyMeasure_real_word, List.length_ofFn, ← Finset.mul_sum,
    ← E.energy_eq_sum_words n f]

theorem abs_scaled_word_variation_le {q : ℝ} (hpq : p.HolderConjugate q)
    (h : E.HasLinearFirstVariations) (w : List (Fin 8)) (f g : E.domain) :
    E.scalingFactor ^ w.length *
      |E.variation h (E.pullbackWord w f) (E.pullbackWord w g)| ≤
      (E.energyMeasure f).real (range (wordMap w)) ^ q⁻¹ *
        (E.energyMeasure g).real (range (wordMap w)) ^ p⁻¹ := by
  have hρ : 0 ≤ E.scalingFactor ^ w.length := pow_nonneg E.isScalingFactor_scalingFactor.1.le _
  have h' := E.abs_variation_le h (E.pullbackWord w f) (E.pullbackWord w g)
  rw [E.rootSeminorm_rpow_conj hpq, E.rootSeminorm_apply] at h'
  exact (mul_le_mul_of_nonneg_left h' hρ).trans_eq (by
    rw [E.energyMeasure_real_word, E.energyMeasure_real_word]
    exact weighted_root_product_eq_mass_product hpq hρ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

/-- A uniformly valid estimate for weighted first variations on all cells
at one level. -/
theorem abs_word_variation_sum_le {q : ℝ} (hpq : p.HolderConjugate q)
    (h : E.HasLinearFirstVariations) (n : ℕ) (f g : E.domain)
    (c : (Fin n → Fin 8) → ℝ) :
    |E.scalingFactor ^ n * ∑ w : Fin n → Fin 8,
      c w * E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) g)| ≤
      (∑ w : Fin n → Fin 8, |c w| ^ q * (E.energyMeasure f).real (range (wordMap (List.ofFn w)))) ^ q⁻¹ *
        (E.energy g : ℝ) ^ p⁻¹ := by
  let a (w : Fin n → Fin 8) := (E.energyMeasure f).real (range (wordMap (List.ofFn w)))
  let b (w : Fin n → Fin 8) := (E.energyMeasure g).real (range (wordMap (List.ofFn w)))
  let L (w : Fin n → Fin 8) :=
    E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) g)
  let r := E.scalingFactor ^ n
  have hr : 0 ≤ r := pow_nonneg E.isScalingFactor_scalingFactor.1.le _
  change |r * ∑ w, c w * L w| ≤ (∑ w, |c w| ^ q * a w) ^ q⁻¹ * (E.energy g : ℝ) ^ p⁻¹
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ w, |r * (c w * L w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, |c w| * a w ^ q⁻¹ * b w ^ p⁻¹ := by
      apply Finset.sum_le_sum
      intro w _
      have he := E.abs_scaled_word_variation_le hpq h (List.ofFn w) f g
      rw [List.length_ofFn] at he
      simp only [abs_mul, abs_of_nonneg hr]
      have hh := mul_le_mul_of_nonneg_left he (abs_nonneg (c w))
      nlinarith only [hh]
    _ ≤ _ := by
      rw [← E.sum_energyMeasure_real_word g n]
      exact sum_abs_mul_mass_rpow_le hpq a b c (fun _ ↦ measureReal_nonneg)
        (fun _ ↦ measureReal_nonneg)

/-- The coefficient may instead be placed in the direction budget,
with exponent p. -/
theorem abs_word_variation_sum_le_direction_weight {q : ℝ} (hpq : p.HolderConjugate q)
    (h : E.HasLinearFirstVariations) (n : ℕ) (f g : E.domain)
    (c : (Fin n → Fin 8) → ℝ) :
    |E.scalingFactor ^ n * ∑ w : Fin n → Fin 8,
      c w * E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) g)| ≤
      (E.energy f : ℝ) ^ q⁻¹ *
        (∑ w : Fin n → Fin 8, |c w| ^ p * (E.energyMeasure g).real (range (wordMap (List.ofFn w)))) ^ p⁻¹ := by
  let a (w : Fin n → Fin 8) := (E.energyMeasure f).real (range (wordMap (List.ofFn w)))
  let b (w : Fin n → Fin 8) := (E.energyMeasure g).real (range (wordMap (List.ofFn w)))
  let L (w : Fin n → Fin 8) :=
    E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) g)
  let r := E.scalingFactor ^ n
  have hr : 0 ≤ r := pow_nonneg E.isScalingFactor_scalingFactor.1.le _
  change |r * ∑ w, c w * L w| ≤ (E.energy f : ℝ) ^ q⁻¹ * (∑ w, |c w| ^ p * b w) ^ p⁻¹
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ w, |r * (c w * L w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, |c w| * b w ^ p⁻¹ * a w ^ q⁻¹ := by
      apply Finset.sum_le_sum
      intro w _
      have he := E.abs_scaled_word_variation_le hpq h (List.ofFn w) f g
      rw [List.length_ofFn] at he
      simp only [abs_mul, abs_of_nonneg hr]
      have hh := mul_le_mul_of_nonneg_left he (abs_nonneg (c w))
      nlinarith only [hh]
    _ ≤ _ := by
      rw [mul_comm, ← E.sum_energyMeasure_real_word f n]
      exact sum_abs_mul_mass_rpow_le hpq.symm b a c (fun _ ↦ measureReal_nonneg)
        (fun _ ↦ measureReal_nonneg)

end CarpetEnergy.SelfSimilarPEnergy
