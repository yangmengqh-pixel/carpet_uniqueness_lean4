import EnergyBallHarnackThresholds
import ThresholdRatioAE

/-!
# Elliptic Harnack inequality for balls
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- Ball Harnack comparison in pairwise almost-everywhere form. The
proof uses continuous graph approximations and permits measurable profiles. -/
theorem exists_ball_harnack_ae
    (hρ : E.scalingFactor ≤ 1) (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (hs : HasUniformSymmetricIncrement (fun f ↦ (E.energy f : ℝ))) :
    ∃ A H : ℝ, 1 < A ∧ 1 ≤ H ∧
      ∀ (x : CarpetPoints) (R : ℝ), 0 < R → R ≤ 1 / 2 →
        carpetMeasure (ball x R)ᶜ ≠ 0 →
        ∀ f : E.domain, E.MinimizesWithExterior (ball x (A * R))ᶜ f →
          (∀ᵐ y ∂carpetMeasure, 0 ≤ (f : CarpetLp p) y) →
            ∀ᵐ y ∂carpetMeasure.restrict (ball x (R / 2)),
              ∀ᵐ z ∂carpetMeasure.restrict (ball x (R / 2)),
                (f : CarpetLp p) y ≤ H * (f : CarpetLp p) z := by
  obtain ⟨A, H, hA, hH, hr⟩ := E.exists_ball_harnack_threshold_ratio hρ h hc hs
  refine ⟨A, H, hA, hH, fun x R hR hR₁ hout f hf hf₀ ↦ ?_⟩
  exact ae_pair_le_of_integral_threshold_ratio ((Lp.memLp (f : CarpetLp p)).integrable (Fact.out : 1 ≤ ENNReal.ofReal p)).restrict
    (ae_restrict_of_ae hf₀) hH (hr x R hR hR₁ hout f hf hf₀)

end CarpetEnergy.SelfSimilarPEnergy
