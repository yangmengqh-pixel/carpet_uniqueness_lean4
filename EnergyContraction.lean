import EnergyMeasure

/-!
# Scalar contractions and energy measures

An energy estimate for scalar composition passes to energy measures by
applying it on every symbolic cylinder. Unit contractivity supplies an
unconditional instance of this argument.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Energy-domain implementation of the truncation to the unit interval. -/
noncomputable def unitTruncation (f : E.domain) : E.domain :=
  (E.unit_contractivity f).choose

theorem unitTruncation_ae (f : E.domain) :
    (E.unitTruncation f : CarpetLp p) =ᵐ[carpetMeasure]
      fun x ↦ min (max ((f : CarpetLp p) x) 0) 1 :=
  (E.unit_contractivity f).choose_spec.1

theorem energy_unitTruncation_le (f : E.domain) :
    E.energy (E.unitTruncation f) ≤ E.energy f :=
  (E.unit_contractivity f).choose_spec.2

/-- Translate by the lower endpoint and truncate to the interval of the given width. -/
noncomputable def shiftedTruncation (a b : ℝ) (f : E.domain) : E.domain :=
  b • E.unitTruncation (b⁻¹ • (f + ⟨constantLp p (-a), E.constant_mem (-a)⟩))

theorem shiftedTruncation_ae (a : ℝ) {b : ℝ} (hb : 0 < b) (f : E.domain) :
    (E.shiftedTruncation a b f : CarpetLp p) =ᵐ[carpetMeasure]
      fun x ↦ min (max ((f : CarpetLp p) x - a) 0) b := by
  let c : E.domain := ⟨constantLp p (-a), E.constant_mem (-a)⟩
  let v : E.domain := b⁻¹ • (f + c)
  change ((b • E.unitTruncation v : E.domain) : CarpetLp p) =ᵐ[carpetMeasure] _
  filter_upwards [Lp.coeFn_smul b (E.unitTruncation v : CarpetLp p), E.unitTruncation_ae v,
    Lp.coeFn_smul b⁻¹ ((f + c : E.domain) : CarpetLp p),
    Lp.coeFn_add (f : CarpetLp p) (c : CarpetLp p),
    Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (-a)] with x h₁ h₂ h₃ h₄ h₅
  change ((b • E.unitTruncation v : E.domain) : CarpetLp p) x =
    b * (E.unitTruncation v : CarpetLp p) x at h₁
  change (v : CarpetLp p) x = b⁻¹ * ((f + c : E.domain) : CarpetLp p) x at h₃
  change ((f + c : E.domain) : CarpetLp p) x = (f : CarpetLp p) x + (c : CarpetLp p) x at h₄
  change (c : CarpetLp p) x = -a at h₅
  rw [h₁, h₂, h₃, h₄, h₅, mul_min_of_nonneg _ _ hb.le, mul_max_of_nonneg _ _ hb.le,
    ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul, mul_zero, mul_one, ← sub_eq_add_neg]

theorem rootSeminorm_shiftedTruncation_le (a : ℝ) {b : ℝ} (hb : 0 < b) (f : E.domain) :
    E.rootSeminorm (E.shiftedTruncation a b f) ≤ E.rootSeminorm f := by
  let c : E.domain := ⟨constantLp p (-a), E.constant_mem (-a)⟩
  let v : E.domain := b⁻¹ • (f + c)
  have hv : E.rootSeminorm (E.unitTruncation v) ≤ E.rootSeminorm v := by
    simp only [E.rootSeminorm_apply]
    apply Real.rpow_le_rpow (E.energy (E.unitTruncation v)).property
    · exact_mod_cast E.energy_unitTruncation_le v
    · exact inv_nonneg.mpr (zero_lt_one.trans E.one_lt_p).le
  have hc : E.rootSeminorm (f + c) = E.rootSeminorm f := by
    simp only [E.rootSeminorm_apply, c, E.add_constant]
  change E.rootSeminorm (b • E.unitTruncation v) ≤ _
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hb]
  calc
    b * E.rootSeminorm (E.unitTruncation v) ≤ b * E.rootSeminorm v :=
      mul_le_mul_of_nonneg_left hv hb.le
    _ = E.rootSeminorm f := by
      change b * E.rootSeminorm (b⁻¹ • (f + c)) = _
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb), hc,
        ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]

private theorem pullbackWord_compScalar {φ : ℝ → ℝ} {T : E.domain → E.domain}
    (hT : ∀ f : E.domain, (T f : CarpetLp p) =ᵐ[carpetMeasure] φ ∘ (f : CarpetLp p))
    (w : List (Fin 8)) (f : E.domain) :
    E.pullbackWord w (T f) = T (E.pullbackWord w f) := by
  apply Subtype.ext
  apply Lp.ext
  have h₁ := E.pullbackWord_isLpPullback w (T f)
  have h₂ := (quasiMeasurePreserving_wordMap w).ae_eq_comp (hT f)
  have h₃ := (E.pullbackWord_isLpPullback w f).fun_comp φ
  exact h₁.trans (h₂.trans (h₃.symm.trans (hT (E.pullbackWord w f)).symm))

/-- A uniform energy bound for a scalar composition passes to energy measures. -/
theorem energyMeasure_le_of_compScalar_energy_le {φ : ℝ → ℝ} (T : E.domain → E.domain)
    (hT : ∀ f : E.domain, (T f : CarpetLp p) =ᵐ[carpetMeasure] φ ∘ (f : CarpetLp p))
    (c : ℝ≥0) (hc : ∀ f : E.domain, E.energy (T f) ≤ c * E.energy f) (f : E.domain) :
    E.energyMeasure (T f) ≤ (c : ℝ≥0∞) • E.energyMeasure f := by
  rw [energyMeasure, energyMeasure, ← Measure.map_smul _ continuous_coding.measurable.aemeasurable]
  apply Measure.map_mono _ continuous_coding.measurable
  apply CylinderMasses.measure_le_smul_of_mass_le
  intro n w
  change E.scalingFactor.toNNReal ^ n * E.energy (E.pullbackWord (List.ofFn w) (T f)) ≤
    c * (E.scalingFactor.toNNReal ^ n * E.energy (E.pullbackWord (List.ofFn w) f))
  rw [E.pullbackWord_compScalar hT, mul_left_comm c]
  exact mul_le_mul_of_nonneg_left (hc _) bot_le

/-- Unit truncation does not increase the energy measure. -/
theorem energyMeasure_unitTruncation_le (f : E.domain) :
    E.energyMeasure (E.unitTruncation f) ≤ E.energyMeasure f := by
  simpa only [ENNReal.coe_one, one_smul] using
    (E.energyMeasure_le_of_compScalar_energy_le
      (φ := fun x ↦ min (max x 0) 1) E.unitTruncation
      E.unitTruncation_ae 1 (fun g ↦ by
        simpa only [one_mul] using E.energy_unitTruncation_le g) f)

end CarpetEnergy.SelfSimilarPEnergy
