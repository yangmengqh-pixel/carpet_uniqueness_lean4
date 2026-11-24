import EnergyContinuousLogTest
import EnergyLocalSmoothChainBound
import EnergyBallCapacityUpper
import EnergyBallPoincare
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A logarithmic mean oscillation bound for continuous harmonic profiles
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3600000 in
/-- The logarithm of a positive shift of a nonnegative continuous
harmonic function has a uniform normalized (p)-oscillation bound. -/
theorem exists_log_p_meanOscillation_bound
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ))) :
    ∃ A C : ℝ, 1 < A ∧ 0 < C ∧ ∀ (x : CarpetPoints) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ f : E.continuousCore, E.IsHarmonicOn (ball x (A * r)) f → (∀ y, 0 ≤ f.val y) →
      ∀ ε > (0 : ℝ),
        let L (y : CarpetPoints) := Real.log (f.val y + ε)
        (∫ y in ball x r, |L y - (⨍ z in ball x r, L z ∂carpetMeasure)| ^ p ∂carpetMeasure) ≤
          C * carpetMeasure.real (ball x r) := by
  have hp := zero_lt_one.trans E.one_lt_p
  obtain ⟨m, hm⟩ := exists_nat_ge p
  have hm₀ : 0 < (m : ℝ) := hp.trans_le hm
  obtain ⟨A₀, C₀, hA₀, hC₀, hPI⟩ := E.exists_ball_poincare
  obtain ⟨A₁, C₁, hA₁, hC₁, hcut⟩ := E.exists_ball_capacity_cutoff
  obtain ⟨a, _, ha, _, hvol⟩ := exists_carpet_ball_volume_bounds
  let A := A₁ * A₀
  let s := carpetSimilarityDimension - E.walkDimension
  let Q := ((m : ℝ) / (p - 1)) ^ p
  let C := C₀ * Q * C₁ * A₀ ^ s / a
  have hA : 1 < A := hA₁.trans_le (le_mul_of_one_le_right (zero_lt_one.trans hA₁).le hA₀)
  have hC : 0 < C := by
    dsimp only [C, Q]
    exact div_pos (mul_pos (mul_pos (mul_pos hC₀ (Real.rpow_pos_of_pos
      (div_pos hm₀ (sub_pos.mpr E.one_lt_p)) _)) hC₁)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hA₀) _)) ha
  refine ⟨A, C, hA, hC, fun x r hr hr₁ f hf hf₀ ε hε ↦ ?_⟩
  obtain ⟨S, hS, hSp, hSid⟩ := exists_smooth_positive_shift hε
  let ψ : ℝ → ℝ := Real.log ∘ S
  have hψ : ContDiff ℝ 1 ψ := hS.log (fun t ↦ (hSp t).ne')
  let u : Fin 1 → E.continuousCore := fun _ ↦ f
  let P : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let φ : (Fin 1 → ℝ) → ℝ := ψ ∘ P
  have hφ : ContDiff ℝ 1 φ := hψ.comp P.contDiff
  obtain ⟨L, hL₀⟩ := E.exists_core_comp_contDiff hc u φ hφ
  have hL (y : CarpetPoints) : L.val y = ψ (f.val y) := hL₀ y
  have hlog (y : CarpetPoints) : L.val y = Real.log (f.val y + ε) := by
    rw [hL]
    exact congrArg Real.log (hSid _ (hf₀ y)).1
  let W (y : CarpetPoints) := (f.val y + ε) ^ (-p)
  have hW (y : CarpetPoints) : |deriv ψ (f.val y)| ^ p = W y := by
    have hd := (Real.hasDerivAt_log (hSp (f.val y)).ne').comp _ (hSid _ (hf₀ y)).2
    change HasDerivAt ψ _ (f.val y) at hd
    rw [hd.deriv, (hSid _ (hf₀ y)).1, mul_one,
      abs_of_pos (inv_pos.mpr (add_pos_of_nonneg_of_pos (hf₀ y) hε)), ← Real.rpow_neg_eq_inv_rpow]
  let R := A₀ * r
  have hR : 0 < R := mul_pos (zero_lt_one.trans_le hA₀) hr
  obtain ⟨χ, hχ1, hχs, hχ01, hχE⟩ := hcut x R hR
  have hχ0 (y : CarpetPoints) (hy : y ∉ ball x (A * r)) : χ.val y = 0 := by
    by_contra hne
    apply hy
    have hh := hχs (subset_tsupport _ (mem_support.mpr hne))
    simpa only [R, A, mul_assoc] using hh
  have hχB (y : CarpetPoints) (hy : y ∈ ball x R) : χ.val y = 1 :=
    hχ1 y (ball_subset_ball (by linarith) hy)
  let μ := E.energyMeasure (E.continuousCoreToDomain f)
  have hWc : Continuous W := (f.val.continuous.add continuous_const).rpow_const
    (fun y ↦ Or.inl (add_pos_of_nonneg_of_pos (hf₀ y) hε).ne')
  have hNW (y : CarpetPoints) : 0 ≤ W y := Real.rpow_nonneg (add_nonneg (hf₀ y) hε.le) _
  have hWI : Integrable (fun y ↦ (χ.val y) ^ m * W y) μ :=
    ((χ.val.continuous.pow _).mul hWc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlocal := E.energyMeasure_real_smooth_comp_le_open h hc f L ψ hψ hL
    (U := ball x R) isOpen_ball
  simp only [hW] at hlocal
  have hlarge : (∫ y in ball x R, W y ∂μ) ≤ ∫ y, (χ.val y) ^ m * W y ∂μ := by
    have hBW : (∫ y in ball x R, W y ∂μ) = ∫ y in ball x R, (χ.val y) ^ m * W y ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
      rw [hχB y hy, one_pow, one_mul]
    rw [hBW]
    simpa only [Measure.restrict_univ] using
      (setIntegral_mono_set hWI.restrict (Eventually.of_forall fun y ↦
        mul_nonneg (pow_nonneg (hχ01 y).1 _) (hNW y)) (Eventually.of_forall (subset_univ (ball x R))))
  have hbudget := E.integral_log_weight_le_of_harmonicOn h hc f χ hf hf₀ hχ01 hχ0 hε m hm
  have hfinal : (E.energyMeasure (E.continuousCoreToDomain L)).real (ball x R) ≤ Q * (C₁ * R ^ s) :=
    hlocal.trans (hlarge.trans (hbudget.trans
      (mul_le_mul_of_nonneg_left hχE (Real.rpow_nonneg (div_nonneg hm₀.le (sub_nonneg.mpr E.one_lt_p.le)) _))))
  let B := ball x r
  let ℓ (y : CarpetPoints) := Real.log (f.val y + ε)
  let d := E.continuousCoreToDomain L
  have hae : (d : CarpetLp p) =ᵐ[carpetMeasure] ℓ :=
    (continuousLp_ae_eq p L.val).trans (Eventually.of_forall hlog)
  have hs : (⨍ z in B, (d : CarpetLp p) z ∂carpetMeasure) =
      ⨍ z in B, ℓ z ∂carpetMeasure := average_congr (ae_restrict_of_ae hae)
  have hEq : (∫ y in B, |(d : CarpetLp p) y - (⨍ z in B, (d : CarpetLp p) z ∂carpetMeasure)| ^ p ∂carpetMeasure) =
      ∫ y in B, |ℓ y - (⨍ z in B, ℓ z ∂carpetMeasure)| ^ p ∂carpetMeasure := by
    rw [hs]
    exact integral_congr_ae ((ae_restrict_of_ae hae).mono fun y hy ↦ congrArg
      (fun t : ℝ ↦ |t - (⨍ z in B, ℓ z ∂carpetMeasure)| ^ p) hy)
  have hosc := hPI x r hr hr₁ d
  change _ ≤ C * carpetMeasure.real B
  rw [← hEq]
  refine hosc.trans ((mul_le_mul_of_nonneg_left hfinal (by positivity : 0 ≤ C₀ * r ^ E.walkDimension)).trans ?_)
  have he : C₀ * r ^ E.walkDimension * (Q * (C₁ * R ^ s)) =
      (C₀ * Q * C₁ * A₀ ^ s) * r ^ carpetSimilarityDimension := by
    rw [show R ^ s = A₀ ^ s * r ^ s from Real.mul_rpow (zero_le_one.trans hA₀) hr.le]
    have hs' : r ^ E.walkDimension * r ^ s = r ^ carpetSimilarityDimension := by
      rw [← Real.rpow_add hr, show E.walkDimension + s = carpetSimilarityDimension by dsimp only [s]; ring]
    rw [← hs']
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left (hvol x r hr hr₁).1 hC.le
  change _ ≤ C * carpetMeasure.real B at h
  simpa only [C, ← mul_assoc, div_mul_cancel₀ _ ha.ne'] using h

end CarpetEnergy.SelfSimilarPEnergy
