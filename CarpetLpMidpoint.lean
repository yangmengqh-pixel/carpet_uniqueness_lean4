import CarpetWordIntegral
import ScalarPowerMidpoint

/-!
# The scalar midpoint deficit integrated over the carpet measure
-/

open MeasureTheory
open scoped ENNReal

namespace CarpetEnergy

theorem carpetLp_rpow_midpoint_deficit {p ε C : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (h : ∀ x y : ℝ, |x - y| ^ p + C * |(x + y) / 2| ^ p ≤
      (ε + C / 2) * (|x| ^ p + |y| ^ p))
    (f g : CarpetLp p) :
    ‖f - g‖ ^ p + C * ‖(1 / 2 : ℝ) • (f + g)‖ ^ p ≤
      (ε + C / 2) * (‖f‖ ^ p + ‖g‖ ^ p) := by
  have hp₀ := zero_lt_one.trans hp
  let m := (1 / 2 : ℝ) • (f + g)
  let P (u : CarpetLp p) (x : CarpetPoints) := |u x| ^ p
  have hi (u : CarpetLp p) : Integrable (P u) carpetMeasure := by
    have hh := (Lp.memLp u).integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top
    simpa only [P, Real.norm_eq_abs, ENNReal.toReal_ofReal hp₀.le] using hh
  have hh : ∀ᵐ x ∂carpetMeasure,
      P (f - g) x + C * P m x ≤ (ε + C / 2) * (P f x + P g x) := by
    filter_upwards [Lp.coeFn_sub f g, Lp.coeFn_add f g, Lp.coeFn_smul (1 / 2 : ℝ) (f + g)]
      with x hsub hadd hsmul
    unfold P
    dsimp only [m]
    rw [hsub, hsmul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hadd, Pi.add_apply,
      show (1 / 2 : ℝ) * (f x + g x) = (f x + g x) / 2 by ring]
    exact h (f x) (g x)
  have ht := integral_mono_ae ((hi _).add ((hi _).const_mul C))
    (((hi f).add (hi g)).const_mul (ε + C / 2)) hh
  change (∫ x, P (f - g) x + C * P m x ∂carpetMeasure) ≤
    (∫ x, (ε + C / 2) * (P f x + P g x) ∂carpetMeasure) at ht
  rw [integral_add (hi _) ((hi _).const_mul C), integral_const_mul, integral_const_mul,
    integral_add (hi f) (hi g)] at ht
  simpa only [P, integral_abs_rpow_eq_norm_rpow hp₀] using ht

end CarpetEnergy
