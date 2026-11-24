import EnergyNormalizedPair

/-!
# Energy measures of normalized pairs

The shared normalization turns the total pair measure of a word
into a probability. Rational combinations transform by the same
factor, since subtracting a cell mean only changes a constant.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private noncomputable def constants : ℝ →ₗ[ℝ] E.domain where
  toFun a := ⟨constantLp p a, E.constant_mem a⟩
  map_add' a b := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (a + b),
      Lp.coeFn_add (constantLp p a) (constantLp p b),
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a,
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure b] with x h₁ h₂ h₃ h₄
    change constantLp p (a + b) x = (constantLp p a + constantLp p b) x
    change constantLp p (a + b) x = a + b at h₁
    change constantLp p a x = a at h₃
    change constantLp p b x = b at h₄
    rw [h₁, h₂, Pi.add_apply, h₃, h₄]
  map_smul' a b := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (a * b),
      Lp.coeFn_smul a (constantLp p b), Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure b] with x h₁ h₂ h₃
    change constantLp p (a * b) x = (a • constantLp p b) x
    change constantLp p (a * b) x = a * b at h₁
    change constantLp p b x = b at h₃
    rw [h₁, h₂, Pi.smul_apply, h₃, smul_eq_mul]

theorem energyMeasure_normalizedPairWordPullback_rat (w : List (Fin 8)) (f g : E.domain) (a b : ℚ) :
    let v := E.normalizedPairWordPullback w f g
    E.energyMeasure (a • v.1 + b • v.2) =
      ENNReal.ofReal (|E.pairWordScale w f g| ^ p) •
        E.energyMeasure (E.pullbackWord w (a • f + b • g)) := by
  let t := E.pairWordScale w f g
  let u := E.pullbackWord w f
  let v := E.pullbackWord w g
  let c := -E.wordMean w f
  let d := -E.wordMean w g
  have h₁ : a • (t • (u + E.constants c)) + b • (t • (v + E.constants d)) =
      t • ((a • u + b • v) + E.constants ((a : ℝ) • c + (b : ℝ) • d)) := by
    rw [← Rat.cast_smul_eq_qsmul ℝ a, ← Rat.cast_smul_eq_qsmul ℝ b,
      ← Rat.cast_smul_eq_qsmul ℝ a, ← Rat.cast_smul_eq_qsmul ℝ b,
      map_add, map_smul, map_smul]
    module
  change E.energyMeasure (a • (t • (u + E.constants c)) + b • (t • (v + E.constants d))) = _
  rw [h₁, E.energyMeasure_smul]
  rw [show E.constants ((a : ℝ) • c + (b : ℝ) • d) =
    ⟨constantLp p ((a : ℝ) • c + (b : ℝ) • d), E.constant_mem _⟩ from rfl, E.energyMeasure_add_constant]
  rw [E.pullbackWord_add, ← Rat.cast_smul_eq_qsmul ℝ a f, ← Rat.cast_smul_eq_qsmul ℝ b g,
    E.pullbackWord_smul, E.pullbackWord_smul, Rat.cast_smul_eq_qsmul, Rat.cast_smul_eq_qsmul]

theorem energyMeasure_normalizedPairWordPullback_image (w : List (Fin 8)) (f g : E.domain)
    (a b : ℚ) (A : Set CarpetPoints)
    (h : 0 < (E.energyMeasure f + E.energyMeasure g) (range (wordMap w))) :
    let v := E.normalizedPairWordPullback w f g
    E.energyMeasure (a • v.1 + b • v.2) A =
      ((E.energyMeasure f + E.energyMeasure g) (range (wordMap w)))⁻¹ *
        E.energyMeasure (a • f + b • g) (wordMap w '' A) := by
  let s := ENNReal.ofReal E.scalingFactor ^ w.length
  let e : ℝ≥0 := E.energy (E.pullbackWord w f) + E.energy (E.pullbackWord w g)
  let m := (E.energyMeasure f + E.energyMeasure g) (range (wordMap w))
  have hs₀ : s ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1).ne'
  have hs₁ : s ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have he : m = s * (e : ℝ≥0∞) := by
    change (E.energyMeasure f + E.energyMeasure g) (range (wordMap w)) = _
    rw [add_apply, E.energyMeasure_range_word, E.energyMeasure_range_word, ENNReal.coe_add, mul_add]
  change 0 < m at h
  have he₀ : e ≠ 0 := by
    intro hz
    rw [he, hz, ENNReal.coe_zero, mul_zero] at h
    exact (lt_irrefl _) h
  have hpos : (0 : ℝ) < e := by exact_mod_cast (pos_iff_ne_zero.mpr he₀)
  have hpow : |E.pairWordScale w f g| ^ p = (e : ℝ)⁻¹ := by
    change |((e : ℝ) ^ p⁻¹)⁻¹| ^ p = _
    rw [abs_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hpos.le _)),
      Real.inv_rpow (Real.rpow_nonneg hpos.le _),
      Real.rpow_inv_rpow hpos.le (zero_lt_one.trans E.one_lt_p).ne']
  dsimp only
  rw [E.energyMeasure_normalizedPairWordPullback_rat, smul_apply, smul_eq_mul, hpow,
    E.energyMeasure_image_word]
  change ENNReal.ofReal ((e : ℝ)⁻¹) * _ = m⁻¹ * (s * _)
  rw [he, ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.mul_inv (Or.inl hs₀) (Or.inl hs₁)]
  rw [show ∀ z : ℝ≥0∞, (s⁻¹ * (e : ℝ≥0∞)⁻¹) * (s * z) =
        (s⁻¹ * s) * ((e : ℝ≥0∞)⁻¹ * z) from fun _ ↦ by ac_rfl,
    ENNReal.inv_mul_cancel hs₀ hs₁, one_mul]

theorem normalizedPairMeasure_image (w : List (Fin 8)) (f g : E.domain) (A : Set CarpetPoints)
    (h : 0 < (E.energyMeasure f + E.energyMeasure g) (range (wordMap w))) :
    let v := E.normalizedPairWordPullback w f g
    (E.energyMeasure v.1 + E.energyMeasure v.2) A =
      ((E.energyMeasure f + E.energyMeasure g) (range (wordMap w)))⁻¹ *
        (E.energyMeasure f + E.energyMeasure g) (wordMap w '' A) := by
  dsimp only
  simp only [add_apply, mul_add]
  have h₁ := E.energyMeasure_normalizedPairWordPullback_image w f g 1 0 A h
  have h₂ := E.energyMeasure_normalizedPairWordPullback_image w f g 0 1 A h
  simp only [one_smul, zero_smul, add_zero, zero_add, add_apply] at h₁ h₂
  rw [h₁, h₂]

end CarpetEnergy.SelfSimilarPEnergy
