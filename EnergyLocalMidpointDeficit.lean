import SeminormPowerMidpoints
import AddressMeasureComparison

/-!
# Local midpoint deficits in the energy measures

The root seminorm midpoint inequality applies to each pulled-back
profile on a word. Its nonnegative linear form is an inequality of
cylinder masses, hence an inequality of the corresponding energy
measures on the carpet.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Pull a continuous finite-energy function back along the specified word. -/
noncomputable def wordPullbackCore (w : List (Fin 8)) (f : E.continuousCore) : E.continuousCore := by
  let u := f.val.comp ⟨wordMap w, continuous_wordMap w⟩
  have h := continuousLp_interpolate_word_eq f.val f.property u w (fun _ ↦ rfl)
  have hu : continuousLp p u ∈ E.domain := h.symm ▸ (E.pullbackWord w (E.continuousCoreToDomain f)).property
  exact ⟨u, hu⟩

theorem wordPullbackCore_apply (w : List (Fin 8)) (f : E.continuousCore) (x : CarpetPoints) :
    (E.wordPullbackCore w f).val x = f.val (wordMap w x) := rfl

theorem continuousCoreToDomain_wordPullbackCore (w : List (Fin 8)) (f : E.continuousCore) :
    E.continuousCoreToDomain (E.wordPullbackCore w f) = E.pullbackWord w (E.continuousCoreToDomain f) :=
  Subtype.ext (continuousLp_interpolate_word_eq f.val f.property
    (E.wordPullbackCore w f).val w (fun _ ↦ rfl))

theorem wordPullbackCore_sub (w : List (Fin 8)) (f g : E.continuousCore) :
    E.wordPullbackCore w (f - g) = E.wordPullbackCore w f - E.wordPullbackCore w g := by
  apply Subtype.ext
  ext x
  rfl

/-- The local form of the uniform midpoint deficit, expressed as an
inequality of finite energy measures. -/
theorem exists_energyMeasure_midpoint_deficit (ε : ℝ) (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ f g : E.continuousCore,
      E.energyMeasure (E.continuousCoreToDomain (f - g)) +
          ENNReal.ofReal C • E.energyMeasure (E.continuousCoreToDomain ((1 / 2 : ℝ) • (f + g))) ≤
        ENNReal.ofReal (ε + C / 2) •
          (E.energyMeasure (E.continuousCoreToDomain f) + E.energyMeasure (E.continuousCoreToDomain g)) := by
  let R := E.rootSeminorm.comp E.continuousCoreToDomain
  have hp := zero_lt_one.trans E.one_lt_p
  obtain ⟨C, hC, h⟩ := power_deficit_controls_difference R E.one_lt_p
    (fun e he ↦ E.exists_root_midpoint_gap e he) ε hε
  let a : ℝ≥0 := ⟨C, hC⟩
  let b : ℝ≥0 := ⟨ε + C / 2, by positivity⟩
  have hPow (f : E.continuousCore) : R f ^ p = (E.energy (E.continuousCoreToDomain f) : ℝ) := by
    change E.rootSeminorm (E.continuousCoreToDomain f) ^ p = _
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'
  have hlin (f g : E.continuousCore) :
      E.energy (E.continuousCoreToDomain (f - g)) +
        a * E.energy (E.continuousCoreToDomain ((1 / 2 : ℝ) • (f + g))) ≤
        b * (E.energy (E.continuousCoreToDomain f) + E.energy (E.continuousCoreToDomain g)) := by
    have he := h f g
    simp only [hPow] at he
    apply NNReal.coe_le_coe.mp
    change (E.energy (E.continuousCoreToDomain (f - g)) : ℝ) +
      C * (E.energy (E.continuousCoreToDomain ((1 / 2 : ℝ) • (f + g))) : ℝ) ≤
        (ε + C / 2) * ((E.energy (E.continuousCoreToDomain f) : ℝ) +
          (E.energy (E.continuousCoreToDomain g) : ℝ))
    nlinarith only [he]
  refine ⟨C, hC, fun f g ↦ ?_⟩
  let u := E.continuousCoreToDomain f
  let v := E.continuousCoreToDomain g
  let z := E.continuousCoreToDomain (f - g)
  let t := E.continuousCoreToDomain ((1 / 2 : ℝ) • (f + g))
  let μ := E.symbolicEnergyMeasure z + (a : ℝ≥0∞) • E.symbolicEnergyMeasure t
  let ν := (b : ℝ≥0∞) • (E.symbolicEnergyMeasure u + E.symbolicEnergyMeasure v)
  let : IsFiniteMeasure ((a : ℝ≥0∞) • E.symbolicEnergyMeasure t) :=
    Measure.smul_finite _ ENNReal.coe_ne_top
  let : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure
    (E.symbolicEnergyMeasure z + (a : ℝ≥0∞) • E.symbolicEnergyMeasure t))
  let : IsFiniteMeasure ν := Measure.smul_finite _ ENNReal.coe_ne_top
  have hle : μ ≤ ν := by
    have hl : μ ≤ (↑(1 : ℝ≥0) : ℝ≥0∞) • ν := by
      apply measure_le_smul_of_addressCylinder_le μ ν 1
      intro n w
      let W := List.ofFn w
      let f' := E.wordPullbackCore W f
      let g' := E.wordPullbackCore W g
      have hf' := E.continuousCoreToDomain_wordPullbackCore W f
      have hg' := E.continuousCoreToDomain_wordPullbackCore W g
      change E.continuousCoreToDomain f' = E.pullbackWord W u at hf'
      change E.continuousCoreToDomain g' = E.pullbackWord W v at hg'
      have hz : E.pullbackWord W z = E.continuousCoreToDomain (f' - g') := by
        dsimp only [z]
        rw [← E.continuousCoreToDomain_wordPullbackCore, E.wordPullbackCore_sub]
      have ht : E.pullbackWord W t = E.continuousCoreToDomain ((1 / 2 : ℝ) • (f' + g')) := by
        dsimp only [t]
        rw [map_smul, map_add, E.pullbackWord_smul, E.pullbackWord_add, map_smul, map_add]
        change (1 / 2 : ℝ) • (E.pullbackWord W u + E.pullbackWord W v) =
          (1 / 2 : ℝ) • (E.continuousCoreToDomain f' + E.continuousCoreToDomain g')
        rw [hf', hg']
      dsimp only [μ, ν]
      simp only [add_apply, smul_apply, smul_eq_mul, ENNReal.coe_one, one_mul, E.symbolicEnergyMeasure_cylinder]
      change _ * (E.energy (E.pullbackWord W z) : ℝ≥0∞) + _ * (_ * (E.energy (E.pullbackWord W t) : ℝ≥0∞)) ≤
        _ * (_ * (E.energy (E.pullbackWord W u) : ℝ≥0∞) + _ * (E.energy (E.pullbackWord W v) : ℝ≥0∞))
      rw [hz, ht, ← hf', ← hg']
      have hlin' := ENNReal.coe_le_coe.mpr (hlin f' g')
      simp only [ENNReal.coe_add, ENNReal.coe_mul] at hlin'
      let c := ENNReal.ofReal E.scalingFactor ^ n
      let D := (E.energy (E.continuousCoreToDomain (f' - g')) : ℝ≥0∞)
      let T := (E.energy (E.continuousCoreToDomain ((1 / 2 : ℝ) • (f' + g'))) : ℝ≥0∞)
      let U := (E.energy (E.continuousCoreToDomain f') : ℝ≥0∞)
      let V := (E.energy (E.continuousCoreToDomain g') : ℝ≥0∞)
      change c * D + (a : ℝ≥0∞) * (c * T) ≤ (b : ℝ≥0∞) * (c * U + c * V)
      calc
        _ = c * (D + (a : ℝ≥0∞) * T) := by rw [mul_add, mul_left_comm (a : ℝ≥0∞) c]
        _ ≤ c * ((b : ℝ≥0∞) * (U + V)) := mul_le_mul' le_rfl hlin'
        _ = _ := by rw [mul_left_comm c (b : ℝ≥0∞), mul_add c]
    simpa only [ENNReal.coe_one, one_smul] using hl
  have hm := Measure.map_mono hle continuous_coding.measurable
  dsimp only [μ, ν] at hm
  rw [Measure.map_add _ _ continuous_coding.measurable,
    Measure.map_smul _ continuous_coding.measurable.aemeasurable,
    Measure.map_smul _ continuous_coding.measurable.aemeasurable,
    Measure.map_add _ _ continuous_coding.measurable] at hm
  change E.energyMeasure z + (a : ℝ≥0∞) • E.energyMeasure t ≤
    (b : ℝ≥0∞) • (E.energyMeasure u + E.energyMeasure v) at hm
  rw [show (a : ℝ≥0∞) = ENNReal.ofReal C from
    (ENNReal.ofReal_eq_coe_nnreal hC).symm,
    show (b : ℝ≥0∞) = ENNReal.ofReal (ε + C / 2) from
    (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm] at hm
  exact hm

end CarpetEnergy.SelfSimilarPEnergy
