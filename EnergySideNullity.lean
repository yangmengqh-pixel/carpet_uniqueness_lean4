import CarpetCellBoundaries
import EnergyLinearBoundaryProfile

/-!
# Nullity of a side with an affine trace

A locally affine trace is compared to a fixed coordinate profile using
level-set locality. The cells meeting the side number at most `3^n`,
and their total scaled mass tends to zero.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy

/-- A side of the outer square, viewed as a subset of the carpet. -/
def carpetSide (j a : Fin 2) : Set CarpetPoints := {x | (x : Plane) j = (a.val : ℝ)}

theorem measurableSet_carpetSide (j a : Fin 2) : MeasurableSet (carpetSide j a) :=
  measurableSet_eq_fun
    (((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) j).comp continuous_subtypeVal).measurable)
    measurable_const

/-- At most one cell per column or row meets a given side at a given level. -/
theorem card_words_fixed_gridCoord_le (n : ℕ) (j : Fin 2) (k : ℕ) :
    Fintype.card {w : Fin n → Fin 8 // gridCoordinate (List.ofFn w) j = k} ≤ 3 ^ n := by
  let W := {w : Fin n → Fin 8 // gridCoordinate (List.ofFn w) j = k}
  let F (w : W) : Fin (3 ^ n) := ⟨gridCoordinate (List.ofFn w.val) (1 - j),
    by simpa only [List.length_ofFn] using gridCoordinate_lt (List.ofFn w.val) (1 - j)⟩
  have hF : Injective F := by
    intro w v h
    apply Subtype.ext
    apply List.ofFn_injective
    apply gridCoordinate_injective_of_length (by simp)
    intro a
    have hcase : ∀ a j : Fin 2, a = j ∨ a = 1 - j := by decide
    have e := hcase a j
    rcases e with rfl | rfl
    · exact w.property.trans v.property.symm
    · exact congrArg (fun t : Fin (3 ^ n) ↦ t.val) h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective F hF

namespace SelfSimilarPEnergy

open SelfSimilarComponent SelfSimilarComponent.CornerProfile

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem side_mass_of_word_le
    (f v : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain)
    (hv : continuousLp p v ∈ E.domain) (j a : Fin 2) (b c : ℝ)
    (htrace : ∀ x ∈ carpetSide j a, f x = b * (x : Plane) (1 - j) + c)
    (hvtrace : ∀ x ∈ carpetSide j a, v x = (x : Plane) (1 - j))
    (n : ℕ) (w : Fin n → Fin 8) :
    (E.energyMeasure (E.pullbackWord (List.ofFn w) ⟨continuousLp p f, hf⟩)
      (wordMap (List.ofFn w) ⁻¹' carpetSide j a)).toReal ≤
      (|b| / (3 : ℝ) ^ n) ^ p * (E.energy ⟨continuousLp p v, hv⟩ : ℝ) := by
  let A := wordMap (List.ofFn w) ⁻¹' carpetSide j a
  have hA : MeasurableSet A :=
    (measurableSet_carpetSide j a).preimage (continuous_wordMap _).measurable
  let f' := f.comp ⟨wordMap (List.ofFn w), continuous_wordMap _⟩
  have he : continuousLp p f' =
      (E.pullbackWord (List.ofFn w) ⟨continuousLp p f, hf⟩ : CarpetLp p) :=
    continuousLp_interpolate_word_eq f hf f' _ (fun _ ↦ rfl)
  have hf' : continuousLp p f' ∈ E.domain := he.symm ▸ (E.pullbackWord _ ⟨_, hf⟩).property
  have he' : (⟨continuousLp p f', hf'⟩ : E.domain) =
      E.pullbackWord (List.ofFn w) ⟨continuousLp p f, hf⟩ := Subtype.ext he
  let t := (b / (3 : ℝ) ^ n) • v
  let v' : E.domain := ⟨continuousLp p v, hv⟩
  have ht' : continuousLp p t = ((b / (3 : ℝ) ^ n) • v' : E.domain).val :=
    (continuousLpLinear p).map_smul _ _
  have ht : continuousLp p t ∈ E.domain := ht'.symm ▸ ((b / (3 : ℝ) ^ n) • v' : E.domain).property
  have ht'' : (⟨continuousLp p t, ht⟩ : E.domain) = (b / (3 : ℝ) ^ n) • v' := Subtype.ext ht'
  have h3 : 0 < (3 : ℝ) ^ n := by positivity
  have hl : ∀ x ∈ A, f' x - t x = b * (gridCoordinate (List.ofFn w) (1 - j) : ℝ) / (3 : ℝ) ^ n + c := by
    intro x hx
    have hs : (x : Plane) j = a.val := (wordMap_preimage_side w j a x hx).1
    have hcoord := wordMap_scaled_coord (List.ofFn w) x (1 - j)
    rw [List.length_ofFn] at hcoord
    have hp : (wordMap (List.ofFn w) x : Plane) (1 - j) =
        ((gridCoordinate (List.ofFn w) (1 - j) : ℝ) + (x : Plane) (1 - j)) / (3 : ℝ) ^ n :=
      (eq_div_iff h3.ne').mpr (by rw [mul_comm]; exact hcoord)
    change f (wordMap (List.ofFn w) x) - b / (3 : ℝ) ^ n * v x = _
    rw [htrace _ hx, hvtrace x hs, hp]
    ring
  rw [← he', E.energyMeasure_apply_eq_of_sub_constant hA f' t hf' ht hl, ht'', E.energyMeasure_smul]
  rw [smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _),
    abs_div, abs_of_pos h3]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (div_nonneg (abs_nonneg _) h3.le) _)
  rw [← ENNReal.coe_toReal (E.energy v'), ← E.energyMeasure_univ]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))

/-- An affine trace on an outer side gives that side zero energy mass. -/
theorem energyMeasure_carpetSide_eq_zero_of_affine
    (f v : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain)
    (hv : continuousLp p v ∈ E.domain) (j a : Fin 2) (b c : ℝ)
    (htrace : ∀ x ∈ carpetSide j a, f x = b * (x : Plane) (1 - j) + c)
    (hvtrace : ∀ x ∈ carpetSide j a, v x = (x : Plane) (1 - j)) :
    E.energyMeasure ⟨continuousLp p f, hf⟩ (carpetSide j a) = 0 := by
  classical
  let F : E.domain := ⟨continuousLp p f, hf⟩
  let S := carpetSide j a
  have hS := measurableSet_carpetSide j a
  let m := (E.energyMeasure F S).toReal
  let B := |b| ^ p * (E.energy ⟨continuousLp p v, hv⟩ : ℝ)
  let r := E.scalingFactor * (3 : ℝ) ^ (1 - p)
  have hρ := E.isScalingFactor_scalingFactor.1
  have hr : 0 ≤ r := mul_nonneg hρ.le (Real.rpow_nonneg (by norm_num) _)
  have hlim : Tendsto (fun n : ℕ ↦ r ^ n * B) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr E.scalingFactor_mul_three_rpow_lt_one).mul_const B
  have hb (n : ℕ) : m ≤ r ^ n * B := by
    let N := (3 ^ n - 1) * a.val
    let W := Fin n → Fin 8
    let A (w : W) := wordMap (List.ofFn w) ⁻¹' S
    let g (w : W) := E.pullbackWord (List.ofFn w) F
    let d := (|b| / (3 : ℝ) ^ n) ^ p * (E.energy ⟨continuousLp p v, hv⟩ : ℝ)
    let T := Finset.univ.filter (fun w : W ↦ gridCoordinate (List.ofFn w) j = N)
    have hT : (T.card : ℝ) ≤ (3 : ℝ) ^ n := by
      have hc : T.card ≤ 3 ^ n := by
        rw [← Fintype.card_coe]
        exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun w ↦ by simp [T]))).trans_le
          (card_words_fixed_gridCoord_le n j N)
      exact_mod_cast hc
    have hw (w : W) : (E.energyMeasure (g w) (A w)).toReal ≤ if w ∈ T then d else 0 := by
      by_cases h : w ∈ T
      · rw [ite_eq_left h]
        exact E.side_mass_of_word_le f v hf hv j a b c htrace hvtrace n w
      · have he : A w = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          apply h
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          have h' := (wordMap_preimage_side w j a x hx).2
          have hn : 1 ≤ 3 ^ n := Nat.one_le_pow n 3 (by decide)
          unfold N
          exact_mod_cast h'
        rw [ite_eq_right h, he, measure_empty, ENNReal.toReal_zero]
    have ht (w : W) : (ENNReal.ofReal E.scalingFactor ^ n *
        E.energyMeasure (g w) (A w)) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
    have hm : m = E.scalingFactor ^ n * ∑ w : W, (E.energyMeasure (g w) (A w)).toReal := by
      dsimp only [m]
      rw [E.energyMeasure_eq_sum_words n F, Measure.sum_apply _ hS, tsum_fintype, ENNReal.toReal_sum]
      · simp only [smul_apply, smul_eq_mul, Measure.map_apply (continuous_wordMap _).measurable hS,
          ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le, Finset.mul_sum, A, g, S]; rfl
      · intro w _
        rw [smul_apply, smul_eq_mul, Measure.map_apply (continuous_wordMap _).measurable hS]
        exact ht w
    have hd : 0 ≤ d := by dsimp [d]; positivity
    calc
      m = _ := hm
      _ ≤ E.scalingFactor ^ n * ∑ w : W, if w ∈ T then d else 0 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ ↦ hw w)) (pow_nonneg hρ.le _)
      _ = E.scalingFactor ^ n * ((T.card : ℝ) * d) := by
        simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul]
      _ ≤ E.scalingFactor ^ n * ((3 : ℝ) ^ n * d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT hd) (pow_nonneg hρ.le _)
      _ = _ := by
        have h3 : 0 ≤ (3 : ℝ) := by norm_num
        have h3n : 0 < (3 : ℝ) ^ n := by positivity
        have hpow : (3 : ℝ) ^ n / ((3 : ℝ) ^ n) ^ p = ((3 : ℝ) ^ (1 - p)) ^ n := by
          have hh := Real.rpow_sub h3n (1 : ℝ) p
          rw [Real.rpow_one] at hh
          rw [← hh, ← Real.rpow_natCast_mul h3, mul_comm (n : ℝ), Real.rpow_mul_natCast h3]
        dsimp only [r, d, B]
        rw [mul_pow, Real.div_rpow (abs_nonneg _) h3n.le, ← hpow]
        ring
  have hz : m = 0 := le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hb)) ENNReal.toReal_nonneg
  change E.energyMeasure F S = 0
  rw [← ENNReal.ofReal_toReal (measure_ne_top (E.energyMeasure F) S)]
  change ENNReal.ofReal m = 0
  rw [hz, ENNReal.ofReal_zero]

end SelfSimilarPEnergy
end CarpetEnergy
