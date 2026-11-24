import EnergyVariationAffineLimit
import CarpetEnergyRiemannSums

/-!
# Energy bound for smooth compositions on the continuous core
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 2000000 in
/-- Global energy-root form of the smooth composition estimate (5.37).
Each coefficient is measured against the energy measure of its corresponding
coordinate. -/
theorem rootSeminorm_smooth_comp_le (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {m : ℕ} (u : Fin m → E.continuousCore)
    (φ : (Fin m → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (v : E.continuousCore)
    (hv : ∀ x, v.val x = φ (E.continuousCoreTuple u x)) :
    E.rootSeminorm (E.continuousCoreToDomain v) ≤ ∑ i : Fin m,
      (∫ x, |fderiv ℝ φ (E.continuousCoreTuple u x) (Pi.single i 1)| ^ p
        ∂E.energyMeasure (E.continuousCoreToDomain (u i))) ^ p⁻¹ := by
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent E.one_lt_p
  let f := E.continuousCoreToDomain v
  let F := E.continuousCoreTuple u
  let g (i : Fin m) := E.continuousCoreToDomain (u i)
  let z := bottomPoint 0
  let R (i : Fin m) : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ fderiv ℝ φ (F x) (Pi.single i 1),
      (((hφ.continuous_fderiv (by norm_num)).comp F.continuous).clm_apply continuous_const)⟩
  let Rp (i : Fin m) : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ |R i x| ^ p,
      (R i).continuous.abs.rpow_const (fun _ ↦ Or.inr hpq.nonneg)⟩
  let T (i : Fin m) (n : ℕ) := ∑ w : Fin n → Fin 8,
    Rp i (wordMap (List.ofFn w) z) * (E.energyMeasure (g i)).real (range (wordMap (List.ofFn w)))
  let A (i : Fin m) := ∫ x, Rp i x ∂E.energyMeasure (g i)
  have hA (i : Fin m) : 0 ≤ A i := integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hT (i : Fin m) : Tendsto (T i) atTop (𝓝 (A i)) :=
    tendsto_wordCell_riemannSum (E.energyMeasure (g i))
      (E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero (g i))
      (Rp i) z
  have hlim := E.tendsto_affineVariationSum h hc f u φ hφ v hv z
  have he : E.variation h f (E.continuousCoreToDomain v) = (E.energy f : ℝ) :=
    E.variation_self h f
  rw [he] at hlim
  let U (i : Fin m) (n : ℕ) := E.scalingFactor ^ n * ∑ w : Fin n → Fin 8,
    R i (wordMap (List.ofFn w) z) *
      E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) (g i))
  have hsum (n : ℕ) : E.affineVariationSum h f u φ z n = ∑ i : Fin m, U i n := by
    unfold affineVariationSum
    rw [Finset.sum_comm, Finset.mul_sum]
    rfl
  have hb (n : ℕ) : |E.affineVariationSum h f u φ z n| ≤
      (E.energy f : ℝ) ^ q⁻¹ * ∑ i : Fin m, (T i n) ^ p⁻¹ := by
    rw [hsum, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
      E.abs_word_variation_sum_le_direction_weight hpq h n f (g i) (fun w ↦ R i (wordMap (List.ofFn w) z)))
  have hlimR : Tendsto (fun n ↦ (E.energy f : ℝ) ^ q⁻¹ * ∑ i, (T i n) ^ p⁻¹)
      atTop (𝓝 ((E.energy f : ℝ) ^ q⁻¹ * ∑ i, (A i) ^ p⁻¹)) := by
    apply Tendsto.const_mul
    exact tendsto_finsetSum _ (fun i _ ↦
      ((Real.continuous_rpow_const (inv_nonneg.mpr hpq.nonneg)).tendsto (A i)).comp (hT i))
  have h := le_of_tendsto_of_tendsto ((continuous_abs.tendsto _).comp hlim) hlimR
    (Eventually.of_forall hb)
  rw [abs_of_nonneg (NNReal.coe_nonneg _)] at h
  have h' : (E.energy f : ℝ) ^ p⁻¹ ≤ ∑ i : Fin m, (A i) ^ p⁻¹ := by
    rcases (NNReal.coe_nonneg (E.energy f)).eq_or_lt with hzero | hpos
    · rw [← hzero, Real.zero_rpow (inv_ne_zero hpq.ne_zero)]
      exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hA i) _
    · have hm : (E.energy f : ℝ) ^ q⁻¹ * (E.energy f : ℝ) ^ p⁻¹ ≤
          (E.energy f : ℝ) ^ q⁻¹ * ∑ i : Fin m, (A i) ^ p⁻¹ := by
        rw [← Real.rpow_add hpos, hpq.symm.inv_add_inv_eq_one, Real.rpow_one]
        exact h
      exact le_of_mul_le_mul_left hm (Real.rpow_pos_of_pos hpos _)
  show E.rootSeminorm f ≤ _
  rw [E.rootSeminorm_apply]
  exact h'

end CarpetEnergy.SelfSimilarPEnergy
