import EnergySmoothCompositionBound
import CarpetOpenWordComparison

/-!
# Local energy bound for a smooth scalar composition
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

private theorem scalar_comp_root_le (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (f v : E.continuousCore) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hv : ∀ x, v.val x = ψ (f.val x)) :
    E.rootSeminorm (E.continuousCoreToDomain v) ≤
      (∫ x, |deriv ψ (f.val x)| ^ p ∂E.energyMeasure (E.continuousCoreToDomain f)) ^ p⁻¹ := by
  let u : Fin 1 → E.continuousCore := fun _ ↦ f
  let P : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let φ : (Fin 1 → ℝ) → ℝ := ψ ∘ P
  have hφ : ContDiff ℝ 1 φ := hψ.comp P.contDiff
  have hA := E.rootSeminorm_smooth_comp_le h hc u φ hφ v hv
  have hd (x : CarpetPoints) :
      fderiv ℝ φ (E.continuousCoreTuple u x) (Pi.single 0 1) = deriv ψ (f.val x) := by
    let y := E.continuousCoreTuple u x
    have hD := ((hψ.differentiable (by norm_num) (P y)).hasDerivAt).comp_hasFDerivAt y P.hasFDerivAt
    change HasFDerivAt φ _ y at hD
    rw [hD.fderiv, smul_apply, smul_eq_mul]
    have hP : P (Pi.single 0 1) = 1 := by
      change (Pi.single 0 1 : Fin 1 → ℝ) 0 = 1
      exact Pi.single_eq_same _ _
    rw [hP, mul_one]
    rfl
  rw [Fin.sum_univ_one] at hA
  simp only [hd, u] at hA
  exact hA

set_option maxHeartbeats 2200000 in
/-- The smooth scalar chain bound on an open subset of the carpet. -/
theorem energyMeasure_real_smooth_comp_le_open (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (f v : E.continuousCore) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hv : ∀ x, v.val x = ψ (f.val x)) {U : Set CarpetPoints} (hU : IsOpen U) :
    (E.energyMeasure (E.continuousCoreToDomain v)).real U ≤
      ∫ x in U, |deriv ψ (f.val x)| ^ p ∂E.energyMeasure (E.continuousCoreToDomain f) := by
  let d := E.continuousCoreToDomain f
  let e := E.continuousCoreToDomain v
  let μ := E.energyMeasure d
  let W (x : CarpetPoints) := |deriv ψ (f.val x)| ^ p
  have hp := zero_lt_one.trans E.one_lt_p
  have hW : Continuous W := ((hψ.continuous_deriv (by norm_num)).comp
    f.val.continuous).abs.rpow_const (fun _ ↦ Or.inr hp.le)
  have hW₀ (x : CarpetPoints) : 0 ≤ W x := Real.rpow_nonneg (abs_nonneg _) _
  have hI : Integrable W μ := hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (W x))
  have hν (A : Set CarpetPoints) (hA : MeasurableSet A) :
      ν A = ENNReal.ofReal (∫ x in A, W x ∂μ) := by
    rw [withDensity_apply _ hA, ofReal_integral_eq_lintegral_ofReal hI.restrict
      (Eventually.of_forall hW₀)]
  have hnull (n : ℕ) : ν (carpetCellBoundary n) = 0 := by
    dsimp only [ν]
    exact (withDensity_absolutelyContinuous _ _) (E.energyMeasure_carpetCellBoundary_eq_zero
      E.energyMeasure_carpetOuterBoundary_eq_zero d n)
  have hcell (w : List (Fin 8)) : E.energyMeasure e (range (wordMap w)) ≤ ν (range (wordMap w)) := by
    let V := range (wordMap w)
    let f' := E.wordPullbackCore w f
    let v' := E.wordPullbackCore w v
    let μ' := E.energyMeasure (E.pullbackWord w d)
    have hpull (x : CarpetPoints) : v'.val x = ψ (f'.val x) := by
      rw [E.wordPullbackCore_apply, E.wordPullbackCore_apply, hv]
    have hp' := E.scalar_comp_root_le h hc f' v' ψ hψ hpull
    have hnon : 0 ≤ ∫ x, |deriv ψ (f'.val x)| ^ p ∂E.energyMeasure (E.continuousCoreToDomain f') :=
      integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    have hb := Real.rpow_le_rpow (apply_nonneg E.rootSeminorm _) hp' hp.le
    rw [E.rootSeminorm_apply, Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne',
      Real.rpow_inv_rpow hnon hp.ne', E.continuousCoreToDomain_wordPullbackCore,
      E.continuousCoreToDomain_wordPullbackCore] at hb
    have hρ := E.isScalingFactor_scalingFactor.1
    let r := ENNReal.ofReal E.scalingFactor ^ w.length
    have hInt (x : CarpetPoints) : |deriv ψ (f'.val x)| ^ p = W (wordMap w x) := by
      rw [E.wordPullbackCore_apply]
    have hmap : (∫ x in V, W x ∂μ) = r.toReal * ∫ x, W (wordMap w x) ∂μ' := by
      change (∫ x, W x ∂(E.energyMeasure d).restrict V) = _
      rw [E.energyMeasure_restrict_word, integral_smul_measure, smul_eq_mul,
        integral_map (continuous_wordMap w).measurable.aemeasurable hW.aestronglyMeasurable]
    have hfin : r ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hpos : 0 ≤ ∫ x, W (wordMap w x) ∂μ' := integral_nonneg fun x ↦ hW₀ _
    have hcoeff : ENNReal.ofReal (r.toReal * ∫ x, W (wordMap w x) ∂μ') =
        r * ENNReal.ofReal (∫ x, W (wordMap w x) ∂μ') := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]
    rw [E.energyMeasure_range_word, hν _ (measurableEmbedding_wordMap w).measurableSet_range, hmap, hcoeff]
    apply mul_le_mul' le_rfl
    simpa only [hInt, ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hb
  have hdom := measure_open_le_of_wordCell_le (E.energyMeasure e) ν hnull hcell hU
  rw [hν U hU.measurableSet] at hdom
  have hU₀ : 0 ≤ ∫ x in U, W x ∂μ := integral_nonneg hW₀
  simpa only [Measure.real, ENNReal.toReal_ofReal hU₀] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hdom

end CarpetEnergy.SelfSimilarPEnergy
