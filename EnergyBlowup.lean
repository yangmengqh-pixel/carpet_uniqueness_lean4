import AddressStopping
import CarpetAddressMeasure
import CarpetCapacity

/-!
# Growing a small plateau by pullback

The first-crossing partition controls the mass of the plateau after pullback.
Selecting a cylinder using the two finite budgets controls the mass of the
positive set and the energy at the same time.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

/-- Two nonnegative budgets admit a simultaneous bound at an index of positive weight. -/
theorem exists_simultaneous_bounds {ι : Type*} [Countable ι]
    (x y z : ι → ℝ≥0∞) {X C e : ℝ≥0∞}
    (hX : X ≠ 0) (hXt : X ≠ ∞) (hC : C ≠ 0) (hCt : C ≠ ∞) (het : e ≠ ∞)
    (hx : (∑' i, x i) = X) (hy : (∑' i, y i) ≤ C * X) (hz : (∑' i, z i) ≤ e) :
    ∃ i, x i ≠ 0 ∧ y i ≤ 4 * C * x i ∧ X * z i ≤ 4 * e * x i := by
  by_contra! h
  rcases eq_or_ne e 0 with rfl | he
  · have hz0 (i : ι) : z i = 0 := nonpos_iff_eq_zero.mp ((le_tsum z i).trans hz)
    have hy' (i : ι) : 4 * C * x i ≤ y i := by
      by_cases hxi : x i = 0
      · simp only [hxi, mul_zero, zero_le]
      by_contra! hh
      have hn := h i hxi hh.le
      simp only [hz0, mul_zero, zero_mul, lt_irrefl] at hn
    have hS := tsum_le_tsum hy'
    rw [ENNReal.tsum_mul_left, hx] at hS
    have hb : 0 < C * X := by positivity
    have ht : C * X ≠ ∞ := ENNReal.mul_ne_top hCt hXt
    have hgt : (1 : ℝ≥0∞) * (C * X) < 4 * (C * X) :=
      ENNReal.mul_lt_mul_left hb.ne' ht (by norm_num)
    rw [one_mul, ← mul_assoc] at hgt
    exact hgt.not_ge (hS.trans hy)
  · have hcomp (i : ι) : (4 * C * e) * x i ≤ e * y i + (C * X) * z i := by
      by_cases hxi : x i = 0
      · simp only [hxi, mul_zero, zero_le]
      by_cases hyi : y i ≤ 4 * C * x i
      · have hzi := (h i hxi hyi).le
        calc
          _ = C * (4 * e * x i) := by ac_rfl
          _ ≤ C * (X * z i) := mul_le_mul' le_rfl hzi
          _ ≤ _ := by rw [← mul_assoc]; exact le_add_of_nonneg_left bot_le
      · calc
          _ = e * (4 * C * x i) := by ac_rfl
          _ ≤ e * y i := mul_le_mul' le_rfl (lt_of_not_ge hyi).le
          _ ≤ _ := le_add_of_nonneg_right bot_le
    have hS := tsum_le_tsum hcomp
    rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_left, hx] at hS
    let b := C * X * e
    have hb : 0 < b := (mul_ne_zero (mul_ne_zero hC hX) he).pos
    have hbt : b ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hCt hXt) het
    have hle : 4 * b ≤ 2 * b := by
      calc
        _ = 4 * C * e * X := by dsimp only [b]; ac_rfl
        _ ≤ _ := hS
        _ ≤ e * (C * X) + (C * X) * e := add_le_add (mul_le_mul' le_rfl hy) (mul_le_mul' le_rfl hz)
        _ = _ := by dsimp only [b]; rw [mul_comm e, two_mul]
    exact (ENNReal.mul_lt_mul_left hb.ne' hbt (by norm_num : (2 : ℝ≥0∞) < 4)).not_ge hle

private theorem firstCrossing_mass_le (A : Set Addresses) {δ : ℝ≥0}
    (hsmall : addressMeasure A < δ)
    (w : firstCrossingAddresses addressMeasure A δ) :
    addressMeasure (A ∩ addressCylinder w.val.2) ≤
      8 * (δ : ℝ≥0∞) * addressMeasure (addressCylinder w.val.2) := by
  obtain ⟨⟨n, v⟩, hw⟩ := w
  have hn : n ≠ 0 := by
    rintro rfl
    have hle := hw.1
    rw [addressCylinder_zero, measure_univ, mul_one, inter_univ] at hle
    exact hsmall.not_ge hle
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let s : Addresses := fun k ↦ if h : k < m + 1 then v ⟨k, h⟩ else 0
  have hs : s ∈ addressCylinder v := by
    change addressPrefix (m + 1) s = v
    funext k
    change s k.val = v k
    exact dite_eq_left k.isLt
  have hparent := hw.2 s hs m (Nat.lt_succ_self m)
  have hsub : addressCylinder v ⊆ addressCylinder (addressPrefix m s) := by
    intro t ht
    change addressPrefix (m + 1) t = v at ht
    change addressPrefix m t = addressPrefix m s
    funext k
    exact congrFun (ht.trans (show addressPrefix (m + 1) s = v from hs).symm) k.castSucc
  calc
    _ ≤ addressMeasure (A ∩ addressCylinder (addressPrefix m s)) :=
      measure_mono (inter_subset_inter_right _ hsub)
    _ ≤ (δ : ℝ≥0∞) * addressMeasure (addressCylinder (addressPrefix m s)) := hparent.le
    _ = _ := by
      rw [addressMeasure_cylinder, addressMeasure_cylinder, pow_succ', ← mul_assoc]
      have h8 : (8 : ℝ≥0∞) * (8 : ℝ≥0∞)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [show (8 : ℝ≥0∞) * δ * (8 : ℝ≥0∞)⁻¹ = δ by
        rw [mul_comm (8 : ℝ≥0∞) (δ : ℝ≥0∞), mul_assoc, h8, mul_one]]

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The pullback estimates of Lemma 3.5. The energy estimate is written after
multiplication by the positive mass of the original plateau. -/
theorem exists_word_of_small_plateau
    (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain)
    {δ C : ℝ≥0} (hδ₁ : δ < 1) (hC : 1 ≤ C)
    (hpos : carpetMeasure {x | u x = 1} ≠ 0)
    (hsmall : carpetMeasure {x | u x = 1} < δ)
    (hsupp : carpetMeasure {x | 0 < u x} ≤ (C : ℝ≥0∞) * carpetMeasure {x | u x = 1}) :
    ∃ (n : ℕ) (w : Fin n → Fin 8),
      (δ : ℝ≥0∞) ≤ carpetMeasure (wordMap (List.ofFn w) ⁻¹' {x | u x = 1}) ∧
      carpetMeasure (wordMap (List.ofFn w) ⁻¹' {x | 0 < u x}) ≤ 32 * (C : ℝ≥0∞) * δ ∧
      carpetMeasure {x | u x = 1} *
        (E.energy (E.pullbackWord (List.ofFn w) ⟨continuousLp p u, hu⟩) : ℝ≥0∞) ≤
          32 * (δ : ℝ≥0∞) * (E.energy ⟨continuousLp p u, hu⟩ : ℝ≥0∞) := by
  let A : Set CarpetPoints := {x | u x = 1}
  let B : Set CarpetPoints := {x | 0 < u x}
  have hA : MeasurableSet A := measurableSet_eq_fun u.continuous.measurable measurable_const
  have hB : MeasurableSet B := measurableSet_lt measurable_const u.continuous.measurable
  let P := addressMeasure
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let ν := E.symbolicEnergyMeasure f
  let A' := coding ⁻¹' A
  let B' := coding ⁻¹' B
  let W := firstCrossingAddresses P A' δ
  let K (w : W) := addressCylinder w.val.2
  have hK (w : W) : MeasurableSet (K w) := measurableSet_addressCylinder _
  have hd : Pairwise (Disjoint on K) := pairwise_disjoint_firstCrossingAddresses P A' δ
  have hA' : MeasurableSet A' := continuous_coding.measurable hA
  have hB' : MeasurableSet B' := continuous_coding.measurable hB
  have hmA : P A' = carpetMeasure A := (Measure.map_apply continuous_coding.measurable hA).symm
  have hmB : P B' = carpetMeasure B := (Measure.map_apply continuous_coding.measurable hB).symm
  have sum_inter (D : Set Addresses) (hD : MeasurableSet D) :
      (∑' w, P (D ∩ K w)) = P (D ∩ ⋃ w, K w) := by
    rw [inter_iUnion, measure_iUnion
      (fun i j hij ↦ (hd hij).mono inter_subset_right inter_subset_right)
      (fun w ↦ hD.inter (hK w))]
  have hsuma : (∑' w, P (A' ∩ K w)) = P A' := by
    rw [sum_inter A' hA']
    have hh := measure_inter_add_sdiff (μ := P) A' (MeasurableSet.iUnion hK)
    rw [measure_sdiff_firstCrossingAddresses_eq_zero P hδ₁, add_zero] at hh
    exact hh
  have hsumb : (∑' w, P (B' ∩ K w)) ≤ (C : ℝ≥0∞) * P A' := by
    rw [sum_inter B' hB', hmA]
    exact (measure_mono inter_subset_left).trans (hmB.symm ▸ hsupp)
  have hsumν : (∑' w, ν (K w)) ≤ (E.energy f : ℝ≥0∞) := by
    rw [← measure_iUnion hd hK, ← E.symbolicEnergyMeasure_univ]
    exact measure_mono (subset_univ _)
  obtain ⟨w, -, hwB, hwν⟩ := exists_simultaneous_bounds
    (fun w ↦ P (A' ∩ K w)) (fun w ↦ P (B' ∩ K w)) (fun w ↦ ν (K w))
    (hmA.symm ▸ hpos) (measure_ne_top _ _) (by exact_mod_cast (zero_lt_one.trans_le hC).ne')
    ENNReal.coe_ne_top ENNReal.coe_ne_top hsuma hsumb hsumν
  let F := wordMap (List.ofFn w.val.2)
  let k := P (K w)
  let r := ENNReal.ofReal E.scalingFactor ^ w.val.1
  have hk : k = ((8 : ℝ≥0∞)⁻¹) ^ w.val.1 := addressMeasure_cylinder _
  have hk0 : k ≠ 0 := by rw [hk]; exact pow_ne_zero _ (by norm_num)
  have hr0 : r ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1).ne'
  have hrt : r ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hkr : k ≤ r := by
    rw [hk]
    have hb : ((8 : ℝ≥0∞)⁻¹) ≤ ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
        ENNReal.ofReal_ofNat, one_div, ENNReal.inv_le_inv]
      norm_num
    exact pow_le_pow_left' (hb.trans (ENNReal.ofReal_le_ofReal E.half_le_scalingFactor)) _
  have hmassA : P (A' ∩ K w) = k * carpetMeasure (F ⁻¹' A) :=
    addressMeasure_inter_preimage_coding_cylinder _ hA
  have hmassB : P (B' ∩ K w) = k * carpetMeasure (F ⁻¹' B) :=
    addressMeasure_inter_preimage_coding_cylinder _ hB
  have hupper : P (A' ∩ K w) ≤ 8 * (δ : ℝ≥0∞) * k :=
    firstCrossing_mass_le A' (hmA.symm ▸ hsmall) w
  have hlow := w.property.1
  change (δ : ℝ≥0∞) * k ≤ P (A' ∩ K w) at hlow
  rw [hmassA, mul_comm (δ : ℝ≥0∞) k] at hlow
  have hlow' := (ENNReal.mul_le_mul_iff_right hk0 (measure_ne_top P (K w))).mp hlow
  have hB' : carpetMeasure (F ⁻¹' B) ≤ 32 * (C : ℝ≥0∞) * δ := by
    apply (ENNReal.mul_le_mul_iff_right hk0 (measure_ne_top P (K w))).mp
    rw [← hmassB]
    calc
      _ ≤ _ := hwB
      _ ≤ 4 * (C : ℝ≥0∞) * (8 * (δ : ℝ≥0∞) * k) := mul_le_mul' le_rfl hupper
      _ = _ := by ring
  have hz (w : W) : ν (K w) =
      ENNReal.ofReal E.scalingFactor ^ w.val.1 *
        (E.energy (E.pullbackWord (List.ofFn w.val.2) f) : ℝ≥0∞) :=
    E.symbolicEnergyMeasure_cylinder f w.val.2
  rw [hz w, hmA] at hwν
  have hE' : carpetMeasure A * (E.energy (E.pullbackWord (List.ofFn w.val.2) f) : ℝ≥0∞) ≤
      32 * (δ : ℝ≥0∞) * (E.energy f : ℝ≥0∞) := by
    apply (ENNReal.mul_le_mul_iff_right hr0 hrt).mp
    calc
      _ = carpetMeasure A * (r * (E.energy (E.pullbackWord (List.ofFn w.val.2) f) : ℝ≥0∞)) := by ac_rfl
      _ ≤ _ := hwν
      _ ≤ 4 * (E.energy f : ℝ≥0∞) * (8 * (δ : ℝ≥0∞) * k) := mul_le_mul' le_rfl hupper
      _ = k * (32 * (δ : ℝ≥0∞) * (E.energy f : ℝ≥0∞)) := by ring
      _ ≤ _ := mul_le_mul' hkr le_rfl
  exact ⟨w.val.1, w.val.2, hlow', hB', hE'⟩

end CarpetEnergy.SelfSimilarPEnergy
