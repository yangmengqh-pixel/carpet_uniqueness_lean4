import EnergyVariationAffineLimit
import CarpetEnergyRiemannSums

/-!
# A first-variation bound for a two-coordinate test
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 2250000 in
/-- In the variation based at the first coordinate, its derivative
coefficient integrates against its energy measure. The remaining term
is bounded by Hölder's inequality against the same energy measure. -/
theorem abs_variation_two_coordinate_sub_integral_le
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (u : Fin 2 → E.continuousCore)
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (v : E.continuousCore) (hv : ∀ x, v.val x = φ (E.continuousCoreTuple u x))
    (a b : C(CarpetPoints, ℝ))
    (ha : ∀ x, fderiv ℝ φ (E.continuousCoreTuple u x) (Pi.single 0 1) = a x)
    (hb : ∀ x, fderiv ℝ φ (E.continuousCoreTuple u x) (Pi.single 1 1) = b x) :
    let f := E.continuousCoreToDomain (u 0)
    let g := E.continuousCoreToDomain (u 1)
    let q := p.conjExponent
    |E.variation h f (E.continuousCoreToDomain v) - ∫ x, a x ∂E.energyMeasure f| ≤
      (∫ x, |b x| ^ q ∂E.energyMeasure f) ^ q⁻¹ * (E.energy g : ℝ) ^ p⁻¹ := by
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent E.one_lt_p
  let z := bottomPoint 0
  let f := E.continuousCoreToDomain (u 0)
  let g := E.continuousCoreToDomain (u 1)
  let μ := E.energyMeasure f
  have hμ := E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero f
  let aSum (n : ℕ) := ∑ w : Fin n → Fin 8, a (wordMap (List.ofFn w) z) *
    μ.real (range (wordMap (List.ofFn w)))
  let bq : C(CarpetPoints, ℝ) := ⟨fun x ↦ |b x| ^ q,
    b.continuous.abs.rpow_const (fun _ ↦ Or.inr hpq.symm.nonneg)⟩
  let bSum (n : ℕ) := ∑ w : Fin n → Fin 8, bq (wordMap (List.ofFn w) z) *
    μ.real (range (wordMap (List.ofFn w)))
  let L (n : ℕ) := E.scalingFactor ^ n * ∑ w : Fin n → Fin 8,
    b (wordMap (List.ofFn w) z) *
      E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) g)
  have hsum (n : ℕ) : E.affineVariationSum h f u φ z n = aSum n + L n := by
    unfold affineVariationSum
    simp only [Fin.sum_univ_two, ha, hb, f, E.variation_self, Finset.sum_add_distrib, mul_add]
    congr 1
    · dsimp only [aSum, μ, f]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [E.energyMeasure_real_word, List.length_ofFn]
      ring
  have hlim := E.tendsto_affineVariationSum h hc f u φ hφ v hv z
  have hlimL : Tendsto L atTop (𝓝
      (E.variation h f (E.continuousCoreToDomain v) - ∫ x, a x ∂μ)) := by
    have he : L = fun n ↦ E.affineVariationSum h f u φ z n - aSum n := by
      funext n
      rw [hsum, add_sub_cancel_left]
    rw [he]
    exact hlim.sub (tendsto_wordCell_riemannSum μ hμ a z)
  have hlimB : Tendsto (fun n ↦ (bSum n) ^ q⁻¹ * (E.energy g : ℝ) ^ p⁻¹) atTop
      (𝓝 ((∫ x, bq x ∂μ) ^ q⁻¹ * (E.energy g : ℝ) ^ p⁻¹)) :=
    ((((Real.continuous_rpow_const (inv_nonneg.mpr hpq.symm.nonneg)).tendsto _).comp
      (tendsto_wordCell_riemannSum μ hμ bq z))).mul_const _
  have hle (n : ℕ) : |L n| ≤ (bSum n) ^ q⁻¹ * (E.energy g : ℝ) ^ p⁻¹ :=
    E.abs_word_variation_sum_le hpq h n f g (fun w ↦ b (wordMap (List.ofFn w) z))
  exact le_of_tendsto_of_tendsto (continuous_abs.tendsto _ |>.comp hlimL) hlimB
    (Eventually.of_forall hle)

end CarpetEnergy.SelfSimilarPEnergy
