import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Dyadic layer sums

The lower and upper bounds for a dyadic layer sum are obtained by taking
the first level below the input and bounding the remaining geometric tail.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

/-- The n-th decreasing dyadic level below a fixed radius. -/
noncomputable def dyadicLevel (M : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  M * (2⁻¹ : ℝ≥0∞) ^ n

theorem dyadicLevel_ne_zero {M : ℝ≥0∞} (hM : M ≠ 0) (n : ℕ) :
    dyadicLevel M n ≠ 0 :=
  mul_ne_zero hM (pow_ne_zero _ (by norm_num))

theorem dyadicLevel_succ_mul_two (M : ℝ≥0∞) (n : ℕ) :
    2 * dyadicLevel M (n + 1) = dyadicLevel M n := by
  unfold dyadicLevel
  rw [pow_succ', show (2 : ℝ≥0∞) * (M * (2⁻¹ * (2⁻¹ : ℝ≥0∞) ^ n)) =
    ((2 : ℝ≥0∞) * 2⁻¹) * (M * (2⁻¹ : ℝ≥0∞) ^ n) by ac_rfl,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- A dyadic layer contributes the p-th power of its level when that level is reached. -/
noncomputable def dyadicLayer (p : ℝ) (M x : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  if dyadicLevel M n ≤ x then (dyadicLevel M n) ^ p else 0

private theorem tsum_eq_tsum_tail_of_zero (f : ℕ → ℝ≥0∞) (k : ℕ)
    (h : ∀ i < k, f i = 0) : (∑' n, f n) = ∑' n, f (n + k) := by
  have hsum : (∑ i ∈ Finset.range k, f i) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ h i (Finset.mem_range.mp hi)
  have hsumm : Summable (fun n ↦ f (n + k)) := CompleteLattice.summable
  have htail := Summable.sum_add_tsum_nat_add' (f := f) (k := k) hsumm
  rw [hsum, zero_add] at htail
  exact htail.symm

private theorem dyadicLayer_tail_le {p : ℝ} (hp : 1 ≤ p) {M x : ℝ≥0∞}
    (k : ℕ) (hk : dyadicLevel M k ≤ x) (n : ℕ) :
    dyadicLayer p M x (n + k) ≤ x ^ p * (2⁻¹ : ℝ≥0∞) ^ n := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hq : (2⁻¹ : ℝ≥0∞) ^ p ≤ 2⁻¹ := by
    have h := ENNReal.rpow_le_rpow_of_exponent_ge (by norm_num : (2⁻¹ : ℝ≥0∞) ≤ 1) hp
    rwa [ENNReal.rpow_one] at h
  have hprod : dyadicLevel M (n + k) = dyadicLevel M k * (2⁻¹ : ℝ≥0∞) ^ n := by
    unfold dyadicLevel
    rw [pow_add]
    ac_rfl
  calc
    _ ≤ dyadicLevel M (n + k) ^ p := by
      unfold dyadicLayer
      split_ifs
      · exact le_rfl
      · exact bot_le
    _ = dyadicLevel M k ^ p * ((2⁻¹ : ℝ≥0∞) ^ p) ^ n := by
      rw [hprod, ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_natCast_mul,
        mul_comm (n : ℝ) p, ENNReal.rpow_mul_natCast]
    _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow hk hp0) (pow_le_pow_left' hq _)

/-- Pointwise comparison between the p-th power and the dyadic layer sum. -/
theorem dyadicLayer_bounds {p : ℝ} (hp : 1 ≤ p)
    {M x : ℝ≥0∞} (hM : M ≠ 0) (hMt : M ≠ ∞) (hxM : x ≤ M) :
    x ^ p ≤ (2 : ℝ≥0∞) ^ p * ∑' n, dyadicLayer p M x n ∧
      (∑' n, dyadicLayer p M x n) ≤ 2 * x ^ p := by
  classical
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  rcases eq_or_ne x 0 with rfl | hx
  · have hz (n : ℕ) : dyadicLayer p M 0 n = 0 :=
      ite_eq_right (not_le_of_gt (dyadicLevel_ne_zero hM n).pos)
    simp only [hz, tsum_zero, ENNReal.zero_rpow_of_pos hp0, mul_zero, le_rfl, and_self]
  have hhit : ∃ n, dyadicLevel M n ≤ x := by
    by_contra! h
    lift M to NNReal using hMt
    exact hx (ENNReal.eq_zero_of_le_mul_pow (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)
      (fun n ↦ (h n).le))
  let k := Nat.find hhit
  have hk : dyadicLevel M k ≤ x := Nat.find_spec hhit
  have hbefore (i : ℕ) (hi : i < k) : x < dyadicLevel M i := lt_of_not_ge (Nat.find_min hhit hi)
  have hxk : x ≤ 2 * dyadicLevel M k := by
    cases hk0 : k with
    | zero =>
      rw [dyadicLevel, pow_zero, mul_one, two_mul]
      exact hxM.trans (le_add_of_nonneg_right bot_le)
    | succ i =>
      rw [dyadicLevel_succ_mul_two]
      exact (hbefore i (by omega)).le
  constructor
  · calc
      x ^ p ≤ (2 * dyadicLevel M k) ^ p := ENNReal.rpow_le_rpow hxk hp0.le
      _ = (2 : ℝ≥0∞) ^ p * dyadicLayer p M x k := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, dyadicLayer, ite_eq_left hk]
      _ ≤ _ := mul_le_mul' le_rfl (le_tsum _ k)
  · have hcut (i : ℕ) (hi : i < k) : dyadicLayer p M x i = 0 :=
      ite_eq_right (hbefore i hi).not_ge
    calc
      (∑' n, dyadicLayer p M x n) = ∑' n, dyadicLayer p M x (n + k) :=
        tsum_eq_tsum_tail_of_zero (dyadicLayer p M x) k hcut
      _ ≤ ∑' n : ℕ, x ^ p * (2⁻¹ : ℝ≥0∞) ^ n := tsum_le_tsum (dyadicLayer_tail_le hp k hk)
      _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, mul_comm]

/-- Integrating the dyadic estimates compares the p-th moment with the
weighted sum of the masses of the upper level sets. -/
theorem dyadicLayerMass_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : X → ℝ≥0∞) (hu : Measurable u)
    {p : ℝ} (hp : 1 ≤ p) {M : ℝ≥0∞} (hM : M ≠ 0) (hMt : M ≠ ∞)
    (hsup : ∀ᵐ x ∂μ, u x ≤ M) :
    let J := ∫⁻ x, u x ^ p ∂μ
    let S := ∑' n, (dyadicLevel M n) ^ p * μ {x | dyadicLevel M n ≤ u x}
    J ≤ (2 : ℝ≥0∞) ^ p * S ∧ S ≤ 2 * J := by
  let A (n : ℕ) : Set X := {x | dyadicLevel M n ≤ u x}
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le measurable_const hu
  let f (n : ℕ) (x : X) := dyadicLayer p M (u x) n
  have hf (n : ℕ) : f n = (A n).indicator (fun _ ↦ (dyadicLevel M n) ^ p) := by
    funext x
    by_cases hx : x ∈ A n
    · exact (ite_eq_left hx).trans (indicator_of_mem hx (fun _ : X ↦ dyadicLevel M n ^ p)).symm
    · exact (ite_eq_right hx).trans (indicator_of_notMem hx (fun _ : X ↦ dyadicLevel M n ^ p)).symm
  have hmeas (n : ℕ) : AEMeasurable (f n) μ := by
    rw [hf]
    exact (measurable_const.indicator (hA n)).aemeasurable
  have hJ : (∫⁻ x, ∑' n, f n x ∂μ) = ∑' n, (dyadicLevel M n) ^ p * μ (A n) := by
    rw [lintegral_tsum hmeas]
    congr with n
    rw [hf, lintegral_indicator_const (hA n)]
  change (∫⁻ x, u x ^ p ∂μ) ≤ (2 : ℝ≥0∞) ^ p * (∑' n, _ * μ (A n)) ∧
    (∑' n, _ * μ (A n)) ≤ 2 * (∫⁻ x, u x ^ p ∂μ)
  rw [← hJ]
  constructor
  · rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans hp) (by norm_num))]
    apply lintegral_mono_ae
    exact hsup.mono fun _ hx ↦ (dyadicLayer_bounds hp hM hMt hx).1
  · rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    apply lintegral_mono_ae
    exact hsup.mono fun _ hx ↦ (dyadicLayer_bounds hp hM hMt hx).2

end CarpetEnergy
