import EnergyWalkScale
import CarpetDiscreteEnergy

/-!
# Discrete-to-continuum interpolation

The discrepancy between the continuous interpolant and the piecewise
constant lift is controlled by the discrete p-energy times the inverse
walk scale. This estimate applies to data from any ambient Lp function.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent

variable {p : ℝ} {E : SelfSimilarPEnergy p} {Q : E.SelfSimilarComponent}

/-- A cellwise interpolation differs from its cell data by at most the
local discrete energy to the power 1/p. -/
theorem CornerProfile.abs_interpolation_sub_cellValue_le (P : Q.CornerProfile)
    (n : ℕ) (m : (Fin n → Fin 8) → ℝ) (g : C(CarpetPoints, ℝ))
    (hg : ∀ (w : Fin n → Fin 8) x, g (wordMap (List.ofFn w) x) =
      P.interpolate (cornerData (cornerAverage n m) (List.ofFn w)) x)
    (w : Fin n → Fin 8) {x : CarpetPoints} (hx : x ∈ range (wordMap (List.ofFn w))) :
    |g x - m w| ≤ (∑ v ∈ gridNeighbors w, |m w - m v| ^ p) ^ p⁻¹ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hg]
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  apply P.abs_interpolate_sub_le
  intro i j
  exact cornerAmplitude_le_neighborEnergy n m w i j hp

theorem CornerProfile.norm_sub_cellAveraging_rpow_le [Fact (1 ≤ ENNReal.ofReal p)] (P : Q.CornerProfile)
    (n : ℕ) (f : CarpetLp p) (g : C(CarpetPoints, ℝ))
    (hg : ∀ (w : Fin n → Fin 8) x, g (wordMap (List.ofFn w) x) =
      P.interpolate (cornerData (cornerAverage n (fun v ↦ ambientWordMean p (List.ofFn v) f))
        (List.ofFn w)) x) :
    ‖continuousLp p g - cellAveraging p n f‖ ^ p ≤
      2 * ((8 * E.scalingFactor)⁻¹) ^ n *
        (discreteCellEnergy p E.scalingFactor n f).toReal := by
  let m (w : Fin n → Fin 8) := ambientWordMean p (List.ofFn w) f
  let S (w : Fin n → Fin 8) := ∑ v ∈ gridNeighbors w, |m w - m v| ^ p
  let u : CarpetLp p := continuousLp p g - cellAveraging p n f
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hS (w : Fin n → Fin 8) : 0 ≤ S w :=
    Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hint : Integrable (fun x ↦ |u x| ^ p) carpetMeasure := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using
      (Lp.memLp u).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  have hcell (w : Fin n → Fin 8) :
      (∫ x in openWordCell w, |u x| ^ p ∂carpetMeasure) ≤ ((8 : ℝ)⁻¹) ^ n * S w := by
    have hc : ∀ᵐ x ∂carpetMeasure.restrict (openWordCell w), |u x| ^ p ≤ S w := by
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (continuousLp p g) (cellAveraging p n f)),
        ae_restrict_of_ae (continuousLp_ae_eq p g), cellAveraging_ae_eq_on_openWordCell n f w,
        ae_restrict_mem (measurableSet_openWordCell w)] with x hx hxg hxm hxw
      change |(continuousLp p g - cellAveraging p n f) x| ^ p ≤ S w
      rw [hx, Pi.sub_apply, hxg, hxm]
      exact (Real.rpow_le_rpow (abs_nonneg _)
        (P.abs_interpolation_sub_cellValue_le n m g hg w hxw.1) hp.le).trans_eq
          (Real.rpow_inv_rpow (hS w) hp.ne')
    refine (integral_mono_ae hint.integrableOn (integrable_const _) hc).trans_eq ?_
    rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      carpetMeasure_openWordCell, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  have hρ : 0 < E.scalingFactor := E.isScalingFactor_scalingFactor.1
  change ‖u‖ ^ p ≤ _
  rw [← integral_abs_rpow_eq_norm_rpow hp, integral_eq_sum_openWordCell hint n,
    discreteCellEnergy_eq_grid hp n, ENNReal.toReal_ofReal (by
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun w _ ↦ hS w)))]
  calc
    _ ≤ ∑ w, ((8 : ℝ)⁻¹) ^ n * S w := Finset.sum_le_sum (fun w _ ↦ hcell w)
    _ = _ := by
      change _ = 2 * ((8 * E.scalingFactor)⁻¹) ^ n * (E.scalingFactor ^ n / 2 * ∑ w, S w)
      rw [← Finset.mul_sum, mul_inv, mul_pow, inv_pow (E.scalingFactor)]
      have hn : E.scalingFactor ^ n ≠ 0 := pow_ne_zero _ hρ.ne'
      field_simp

end CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent
