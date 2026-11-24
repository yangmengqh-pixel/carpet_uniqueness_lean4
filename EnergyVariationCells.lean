import EnergyRelativeSelfSimilarEnergy
import EnergyBoundaryCovariance
import EnergyPiecewiseHarmonic
import EnergyFoldingAmplification
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# First variations and cell decompositions
-/

open Filter Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The normalized first-variation functional at a given base function. -/
noncomputable def variation (h : E.HasLinearFirstVariations) (f : E.domain) :
    E.domain →ₗ[ℝ] ℝ := (h f).choose

theorem hasDerivAt_energy_variation (h : E.HasLinearFirstVariations) (f g : E.domain) :
    HasDerivAt (fun t : ℝ ↦ (E.energy (f + t • g) : ℝ)) (p * E.variation h f g) 0 :=
  (h f).choose_spec g

set_option maxHeartbeats 1000000 in
/-- The derivative of the p-power of a seminorm is dominated by the
p-energy analogue of the Cauchy–Schwarz bound. -/
theorem abs_variation_le (h : E.HasLinearFirstVariations) (f g : E.domain) :
    |E.variation h f g| ≤ (E.rootSeminorm f) ^ (p - 1) * E.rootSeminorm g := by
  have hp := zero_lt_one.trans E.one_lt_p
  let S := E.rootSeminorm
  obtain ⟨L, hL, hnorm⟩ := exists_seminorm_norming S f
  let r := S f
  let c := |r| ^ (p - 2) * r
  let F (t : ℝ) := (E.energy (f + t • g) : ℝ)
  let G (t : ℝ) := |r + t * L g| ^ p
  have hr : 0 ≤ r := apply_nonneg S f
  have hpow (z : E.domain) : S z ^ p = (E.energy z : ℝ) := by
    dsimp only [S]
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'
  have he : F 0 = G 0 := by
    simp only [F, G, zero_smul, add_zero, zero_mul, abs_of_nonneg hr, ← hpow]
    rfl
  have hge (t : ℝ) : G t ≤ F t := by
    have h := hnorm (f + t • g)
    rw [map_add, map_smul, smul_eq_mul, hL] at h
    dsimp only [F]
    rw [← hpow (f + t • g)]
    exact Real.rpow_le_rpow (abs_nonneg _) h hp.le
  have hG : HasDerivAt G (p * c * L g) 0 := by
    have hlin : HasDerivAt (fun t : ℝ ↦ r + t * L g) (L g) 0 := by
      simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const (L g)).const_add r
    have hh := (hasDerivAt_abs_rpow (r + (0 : ℝ) * L g) E.one_lt_p).comp 0 hlin
    change HasDerivAt G _ 0 at hh
    simpa only [zero_mul, add_zero, c, mul_assoc] using hh
  have hF : HasDerivAt F (p * E.variation h f g) 0 :=
    E.hasDerivAt_energy_variation h f g
  have hmin : IsLocalMin (fun t ↦ F t - G t) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change F 0 - G 0 ≤ F t - G t
    rw [he, sub_self]
    exact sub_nonneg.mpr (hge t)
  have hzero := hmin.hasDerivAt_eq_zero (hF.sub hG)
  have hlin : E.variation h f g = c * L g := by
    apply mul_left_cancel₀ hp.ne'
    linarith only [hzero]
  have hc : c = r ^ (p - 1) := by
    dsimp only [c]
    rw [abs_of_nonneg hr]
    by_cases hz : r = 0
    · rw [hz, mul_zero, Real.zero_rpow (sub_ne_zero.mpr E.one_lt_p.ne')]
    · have hr' := lt_of_le_of_ne hr (Ne.symm hz)
      calc
        r ^ (p - 2) * r = r ^ (p - 2) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hr']; congr 1; ring
  rw [hlin, hc, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _)]
  exact mul_le_mul_of_nonneg_left (hnorm g) (Real.rpow_nonneg hr _)

theorem variation_eq_sum_words (h : E.HasLinearFirstVariations) (n : ℕ) (f g : E.domain) :
    E.variation h f g = E.scalingFactor ^ n *
      ∑ w : Fin n → Fin 8, E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) g) := by
  let B (t : ℝ) := ∑ w : Fin n → Fin 8,
    (E.energy (E.pullbackWord (List.ofFn w) f + t • E.pullbackWord (List.ofFn w) g) : ℝ)
  have hB : HasDerivAt B (∑ w : Fin n → Fin 8,
      p * E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) g)) 0 :=
    HasDerivAt.fun_sum (fun w _ ↦ E.hasDerivAt_energy_variation h _ _)
  have hF (t : ℝ) : (E.energy (f + t • g) : ℝ) = E.scalingFactor ^ n * B t := by
    rw [E.energy_eq_sum_words n]
    simp only [B, E.pullbackWord_add, E.pullbackWord_smul]
  have h := (E.hasDerivAt_energy_variation h f g).unique (by
    simp only [hF]
    exact hB.const_mul _)
  rw [← Finset.mul_sum, mul_left_comm] at h
  exact mul_left_cancel₀ (zero_lt_one.trans E.one_lt_p).ne' h

/-- Variational harmonicity annihilates the first variation of every
continuous zero-trace test. -/
theorem variation_eq_zero_of_interior_harmonic (h : E.HasLinearFirstVariations)
    (f : E.domain) (hf : E.IsInteriorHarmonic f)
    (v : E.continuousCore) (hv : ∀ x ∈ carpetOuterBoundary, v.val x = 0) :
    E.variation h f (E.continuousCoreToDomain v) = 0 := by
  have hmin : IsLocalMin (fun t : ℝ ↦ (E.energy (f + t • E.continuousCoreToDomain v) : ℝ)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (E.energy (f + (0 : ℝ) • E.continuousCoreToDomain v) : ℝ) ≤
      (E.energy (f + t • E.continuousCoreToDomain v) : ℝ)
    rw [zero_smul, add_zero]
    have ht := hf (t • v).val (t • v).property (fun x hx ↦ by
      change t * v.val x = 0
      rw [hv x hx, mul_zero])
    have htest : (⟨continuousLp p (t • v).val, (t • v).property⟩ : E.domain) =
        t • E.continuousCoreToDomain v := E.continuousCoreToDomain.map_smul t v
    rw [htest] at ht
    exact NNReal.coe_le_coe.mpr ht
  have hz := hmin.hasDerivAt_eq_zero (E.hasDerivAt_energy_variation h f _)
  exact (mul_eq_zero.mp hz).resolve_left (zero_lt_one.trans E.one_lt_p).ne'

/-- The first variation in the base direction is the energy itself. -/
theorem variation_self (h : E.HasLinearFirstVariations) (f : E.domain) :
    E.variation h f f = (E.energy f : ℝ) := by
  have hp := zero_lt_one.trans E.one_lt_p
  have h := E.hasDerivAt_energy_variation h f f
  have he (t : ℝ) : (E.energy (f + t • f) : ℝ) = |1 + t| ^ p * (E.energy f : ℝ) := by
    rw [show f + t • f = (1 + t) • f by rw [add_smul, one_smul]]
    exact E.smul_energy _ f
  have hlin : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add 1
  have hpow := ((hasDerivAt_abs_rpow (1 + (0 : ℝ)) E.one_lt_p).comp 0 hlin).mul_const
    (E.energy f : ℝ)
  have heq : HasDerivAt (fun t : ℝ ↦ (E.energy (f + t • f) : ℝ))
      (p * (E.energy f : ℝ)) 0 := by
    simp only [he]
    simpa only [add_zero, abs_one, Real.one_rpow, mul_one, Function.comp_apply] using hpow
  exact mul_left_cancel₀ hp.ne' (h.unique heq)

end CarpetEnergy.SelfSimilarPEnergy
