import EnergyLocalMidpointDeficit
import EnergyNormalizedPair
import EnergyComponentKernel

/-!
# Continuous normalization on the entire carpet

Centering and rescaling globally gives the normalized word pullback on
the central cell and preserves interior harmonicity.
-/

open Function MeasureTheory Set

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

noncomputable def constCore (c : ℝ) : E.continuousCore :=
  ⟨ContinuousMap.const CarpetPoints c, (E.zeroComponent.continuousKernel_const c).choose⟩

theorem continuousCoreToDomain_constCore (c : ℝ) :
    E.continuousCoreToDomain (E.constCore c) = ⟨constantLp p c, E.constant_mem c⟩ := by
  apply Subtype.ext
  apply Lp.ext
  exact (continuousLp_ae_eq p _).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c).symm

/-- The global profile whose pullback at the central cell has mean zero
and unit energy. -/
noncomputable def globallyNormalizedCore (w : List (Fin 8)) (f : E.continuousCore) : E.continuousCore :=
  E.unitEnergyScale (E.pullbackWord w (E.continuousCoreToDomain f)) •
    (f + E.constCore (-E.wordMean w (E.continuousCoreToDomain f)))

theorem globallyNormalizedCore_harmonic (w : List (Fin 8)) (f : E.continuousCore)
    (hf : E.IsInteriorHarmonic (E.continuousCoreToDomain f)) :
    E.IsInteriorHarmonic (E.continuousCoreToDomain (E.globallyNormalizedCore w f)) := by
  rw [globallyNormalizedCore, map_smul, map_add, E.continuousCoreToDomain_constCore]
  exact (hf.add_constant E _).smul E _

theorem globallyNormalizedCore_pullback (w : List (Fin 8)) (f : E.continuousCore) :
    E.pullbackWord w (E.continuousCoreToDomain (E.globallyNormalizedCore w f)) =
      E.normalizedWordPullback w (E.continuousCoreToDomain f) := by
  rw [globallyNormalizedCore, map_smul, map_add, E.pullbackWord_smul, E.pullbackWord_add]
  have hc (a : ℝ) : E.wordPullbackCore w (E.constCore a) = E.constCore a := by
    apply Subtype.ext
    ext x
    rfl
  rw [← E.continuousCoreToDomain_wordPullbackCore w (E.constCore _), hc,
    E.continuousCoreToDomain_constCore]
  rfl

theorem globallyNormalizedCore_wordMean (w : List (Fin 8)) (f : E.continuousCore) :
    E.wordMean w (E.continuousCoreToDomain (E.globallyNormalizedCore w f)) = 0 := by
  let c := E.wordMean w (E.continuousCoreToDomain f)
  let a := E.unitEnergyScale (E.pullbackWord w (E.continuousCoreToDomain f))
  let fn := E.globallyNormalizedCore w f
  have he : E.wordMean w (E.continuousCoreToDomain fn) =
      ∫ x, fn.val (wordMap w x) ∂carpetMeasure := E.wordMean_continuousLp w fn.val fn.property
  rw [he]
  change (∫ x : CarpetPoints, a * (f.val (wordMap w x) + -c) ∂carpetMeasure) = 0
  rw [integral_const_mul, integral_add, integral_const, probReal_univ, one_smul]
  · have hc : (∫ x, f.val (wordMap w x) ∂carpetMeasure) = c :=
      (E.wordMean_continuousLp w f.val f.property).symm
    rw [hc, add_neg_cancel, mul_zero]
  · exact (f.val.continuous.comp (continuous_wordMap w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact integrable_const _

theorem globallyNormalizedCore_energyMeasure (w : List (Fin 8)) (f : E.continuousCore) :
    E.energyMeasure (E.continuousCoreToDomain (E.globallyNormalizedCore w f)) =
      ENNReal.ofReal (|E.unitEnergyScale (E.pullbackWord w (E.continuousCoreToDomain f))| ^ p) •
        E.energyMeasure (E.continuousCoreToDomain f) := by
  rw [globallyNormalizedCore, map_smul, map_add, E.continuousCoreToDomain_constCore,
    E.energyMeasure_smul, E.energyMeasure_add_constant]

end CarpetEnergy.SelfSimilarPEnergy
