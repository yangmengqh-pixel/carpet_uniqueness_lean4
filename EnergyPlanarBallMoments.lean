import EnergyWeightedCutoffComposition
import SmoothScaledBallCutoff

/-!
# Pulse tests for planar pushforwards of energy and volume
-/

open Filter Function Metric MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy

theorem integral_le_mul_measure_of_vanishes {V : Type*} [MeasurableSpace V]
    {μ : Measure V} {A : Set V} (hA : MeasurableSet A) (hμ : μ A ≠ ∞)
    {f : V → ℝ} {M : ℝ} (hf : Integrable f μ) (hM : ∀ x, f x ≤ M)
    (hzero : ∀ x ∉ A, f x = 0) :
    ∫ x, f x ∂μ ≤ M * μ.real A := by
  have hind : Integrable (A.indicator fun _ ↦ M) μ := by
    rw [integrable_indicator_iff hA]
    exact integrableOn_const hμ
  have hpt (x : V) : f x ≤ A.indicator (fun _ ↦ M) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      exact hM x
    · rw [indicator_of_notMem hx, hzero x hx]
  exact (integral_mono hf hind hpt).trans_eq (by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_comm])

private theorem measure_le_integral_of_one_on {V : Type*} [MeasurableSpace V]
    {μ : Measure V} [IsFiniteMeasure μ] {A : Set V} (hA : MeasurableSet A)
    {f : V → ℝ} (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x) (hone : ∀ x ∈ A, f x = 1) :
    μ.real A ≤ ∫ x, f x ∂μ := by
  have hind : Integrable (A.indicator fun _ ↦ (1 : ℝ)) μ := (integrable_const _).indicator hA
  have hpt (x : V) : A.indicator (fun _ ↦ (1 : ℝ)) x ≤ f x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, hone x hx]
    · rw [indicator_of_notMem hx]
      exact hn x
  have h := integral_mono hind hf hpt
  rwa [integral_indicator_const _ hA, smul_eq_mul, mul_one] at h

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3100000 in
/-- A pulse at scale (r) has volume moments controlled by the
volume pushforward and energy controlled by the energy pushforward. -/
theorem exists_planar_ball_pulse
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (u : Fin 2 → E.continuousCore) :
    ∃ D > (0 : ℝ), ∀ (z : Fin 2 → ℝ) (r : ℝ), 0 < r →
      ∃ v : E.continuousCore,
        let H := E.continuousCoreTuple u
        let ν := carpetMeasure.map H
        let κ := (E.pairEnergyMeasure u).map H
        (∀ q > (0 : ℝ), ν.real (ball z r) ≤ ∫ x, |v.val x| ^ q ∂carpetMeasure) ∧
        (∫ x, |v.val x| ^ p ∂carpetMeasure) ≤ ν.real (ball z (3 * r)) ∧
        E.rootSeminorm (E.continuousCoreToDomain v) ≤
          2 * (((D / r) ^ p) * κ.real (ball z (3 * r))) ^ p⁻¹ := by
  obtain ⟨D, hD, hcut⟩ := exists_planar_ball_cutoffs
  refine ⟨D, hD, fun z r hr ↦ ?_⟩
  obtain ⟨φ, hφ, h01, hsmall, hlarge, hbound⟩ := hcut z r hr
  obtain ⟨v, hv⟩ := E.exists_core_comp_contDiff hc u φ hφ
  let H := E.continuousCoreTuple u
  let ν := carpetMeasure.map H
  let Λ := E.pairEnergyMeasure u
  let κ := Λ.map H
  let B := ball z (3 * r)
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hm (μ : Measure CarpetPoints) : AEMeasurable H μ := H.continuous.measurable.aemeasurable
  have hPow (q : ℝ) (hq : 0 < q) :
      Continuous (fun y ↦ |φ y| ^ q) :=
    hφ.continuous.abs.rpow_const (fun _ ↦ Or.inr hq.le)
  have hMap (q : ℝ) (hq : 0 < q) :
      (∫ x, |v.val x| ^ q ∂carpetMeasure) = ∫ y, |φ y| ^ q ∂ν := by
    rw [integral_map (hm carpetMeasure) (hPow q hq).aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun x ↦
      congrArg (fun t : ℝ ↦ |t| ^ q) (hv x))
  have hInt (q : ℝ) (hq : 0 < q) : Integrable (fun y ↦ |φ y| ^ q) ν := by
    rw [integrable_map_measure (hPow q hq).aestronglyMeasurable (hm carpetMeasure)]
    exact ((hPow q hq).comp H.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp := zero_lt_one.trans E.one_lt_p
  refine ⟨v, ?_, ?_, ?_⟩
  · intro q hq
    rw [hMap q hq]
    exact measure_le_integral_of_one_on Metric.isOpen_ball.measurableSet (hInt q hq)
      (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) (fun y hy ↦ by rw [hsmall y hy, abs_one, Real.one_rpow])
  · rw [hMap p hp]
    have hh := integral_le_mul_measure_of_vanishes hB (measure_ne_top _ _) (hInt p hp)
      (M := 1) (fun y ↦ by
        rw [abs_of_nonneg (h01 y).1, ← Real.one_rpow p]
        exact Real.rpow_le_rpow (h01 y).1 (h01 y).2 hp.le)
      (fun y hy ↦ by rw [(hlarge y hy).1, abs_zero, Real.zero_rpow hp.ne'])
    simpa only [one_mul] using hh
  · apply (E.rootSeminorm_smooth_comp_le h hc u φ hφ v hv).trans
    have hc' (i : Fin 2) :
        (∫ x, |fderiv ℝ φ (H x) (Pi.single i 1)| ^ p
          ∂E.energyMeasure (E.continuousCoreToDomain (u i))) ≤ (D / r) ^ p * κ.real B := by
      let F (y : Fin 2 → ℝ) := |fderiv ℝ φ y (Pi.single i 1)| ^ p
      have hF : Continuous F := ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).abs.rpow_const
        (fun _ ↦ Or.inr hp.le)
      have hI : Integrable (F ∘ H) Λ :=
        (hF.comp H.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hI' : Integrable F κ := (integrable_map_measure hF.aestronglyMeasurable (hm Λ)).mpr hI
      have hmono := integral_mono_measure (E.energyMeasure_le_pairEnergyMeasure u i)
        (Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg
          (fderiv ℝ φ (H x) (Pi.single i 1))) p) hI
      have hd := integral_le_mul_measure_of_vanishes hB (measure_ne_top _ _) hI'
        (fun y ↦ Real.rpow_le_rpow (abs_nonneg _) (hbound y i) hp.le)
        (fun y hy ↦ by dsimp only [F]; rw [(hlarge y hy).2, zero_apply,
          abs_zero, Real.zero_rpow hp.ne'])
      rw [integral_map (hm Λ) hF.aestronglyMeasurable] at hd
      exact hmono.trans hd
    calc
      _ ≤ ∑ _i : Fin 2, (((D / r) ^ p) * κ.real B) ^ p⁻¹ :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow
          (integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)) (hc' i) (inv_nonneg.mpr hp.le)
      _ = _ := by rw [Fin.sum_univ_two, two_mul]

end SelfSimilarPEnergy
end CarpetEnergy
