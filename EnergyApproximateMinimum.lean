import ScalarPowerIncrement
import EnergyUniformFirstVariation
import EnergyHarmonicReplacement

/-!
# Energy defects of graph approximations to constrained minimizers
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem real_energy_eq_root_pow (f : E.domain) : (E.energy f : ℝ) = E.rootSeminorm f ^ p := by
  rw [E.rootSeminorm_apply, Real.rpow_inv_rpow (NNReal.coe_nonneg _) (zero_lt_one.trans E.one_lt_p).ne']

theorem energy_difference_le_of_root_perturbation (f g : E.domain) {B δ : ℝ}
    (hB : E.rootSeminorm g ≤ B) (hδ : E.rootSeminorm (f - g) ≤ δ) :
    (E.energy f : ℝ) - (E.energy g : ℝ) ≤ p * δ * (B + δ) ^ (p - 1) := by
  have hδ₀ : 0 ≤ δ := (apply_nonneg E.rootSeminorm _).trans hδ
  have hS : E.rootSeminorm f ≤ E.rootSeminorm g + δ := by
    have h := map_add_le_add E.rootSeminorm (f - g) g
    rw [sub_add_cancel, add_comm] at h
    exact h.trans (add_le_add_right hδ _)
  rw [E.real_energy_eq_root_pow f, E.real_energy_eq_root_pow g, sub_le_iff_le_add, add_comm]
  exact (Real.rpow_le_rpow (apply_nonneg E.rootSeminorm _) hS
    (zero_lt_one.trans E.one_lt_p).le).trans
    (rpow_increment_le E.one_lt_p (apply_nonneg E.rootSeminorm g) hδ₀ hB)

set_option maxHeartbeats 1900000 in
/-- Perturbing the base of a constrained minimizer by a small amount
in energy gives a uniform defect for bounded admissible directions. -/
theorem energy_le_perturbation_add_defect {A : Set CarpetPoints}
    (f u v : E.domain) (hf : E.MinimizesWithExterior A f)
    (hv : ∀ᵐ x ∂carpetMeasure.restrict A, (v : CarpetLp p) x = 0)
    {B δ : ℝ} (hfB : E.rootSeminorm f ≤ B) (huB : E.rootSeminorm u ≤ B)
    (hvB : E.rootSeminorm v ≤ B) (hδ : E.rootSeminorm (u - f) ≤ δ) (hδ₁ : δ ≤ 1) :
    (E.energy u : ℝ) ≤ (E.energy (u + v) : ℝ) + 2 * p * δ * (2 * B + 1) ^ (p - 1) := by
  have hB : 0 ≤ B := (apply_nonneg E.rootSeminorm _).trans hfB
  have hδ₀ := (apply_nonneg E.rootSeminorm _).trans hδ
  have hm : (E.energy f : ℝ) ≤ (E.energy (f + v) : ℝ) := by
    apply NNReal.coe_le_coe.mpr
    apply hf
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (f : CarpetLp p) (v : CarpetLp p)), hv] with x hx hvx
    change ((f : CarpetLp p) + (v : CarpetLp p)) x = (f : CarpetLp p) x
    rw [hx, Pi.add_apply, hvx, add_zero]
  have hE₀ := E.energy_difference_le_of_root_perturbation u f hfB hδ
  have hu' : E.rootSeminorm (u + v) ≤ 2 * B := (map_add_le_add E.rootSeminorm u v).trans
    (by linarith [add_le_add huB hvB])
  have hdiff : (f + v) - (u + v) = -(u - f) := by abel
  have hE₁ := E.energy_difference_le_of_root_perturbation (f + v) (u + v) hu'
    (show E.rootSeminorm ((f + v) - (u + v)) ≤ δ by rw [hdiff, map_neg_eq_map]; exact hδ)
  have hpδ : 0 ≤ p * δ := mul_nonneg (zero_le_one.trans E.one_lt_p.le) hδ₀
  have hB₀ : p * δ * (B + δ) ^ (p - 1) ≤ p * δ * (2 * B + 1) ^ (p - 1) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (add_nonneg hB hδ₀) (by linarith) (sub_nonneg.mpr E.one_lt_p.le)) hpδ
  have hB₁ : p * δ * (2 * B + δ) ^ (p - 1) ≤ p * δ * (2 * B + 1) ^ (p - 1) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) (sub_nonneg.mpr E.one_lt_p.le)) hpδ
  linarith only [hm, hE₀.trans hB₀, hE₁.trans hB₁]

set_option maxHeartbeats 1700000 in
/-- A symmetric energy increment bound turns a two-sided
approximate minimum into a quantitative first-variation bound. -/
theorem abs_variation_le_of_two_sided_defect (h : E.HasLinearFirstVariations)
    (hs : HasUniformSymmetricIncrement (fun f ↦ (E.energy f : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t > (0 : ℝ), t ≤ 1 ∧ ∀ (f g : E.domain) (d : ℝ),
      (E.energy f : ℝ) ≤ (E.energy (f + t • g) : ℝ) + d →
      (E.energy f : ℝ) ≤ (E.energy (f - t • g) : ℝ) + d →
      p * |E.variation h f g| ≤ ε * ((E.energy f : ℝ) + (E.energy g : ℝ)) + d / t := by
  obtain ⟨a, ha, hbound⟩ := E.exists_uniform_energy_variation_error_bound h hs hε
  let t := min 1 (a / 2)
  have ht : 0 < t := lt_min one_pos (half_pos ha)
  have hta : t < a := (min_le_right _ _).trans_lt (half_lt_self ha)
  refine ⟨t, ht, min_le_left _ _, fun f g d h₀ h₁ ↦ ?_⟩
  have hP := (hbound f g t ht hta).2
  have hM := (hbound f (-g) t ht hta).2
  rw [map_neg, smul_neg, ← sub_eq_add_neg] at hM
  have heng : E.energy (-g) = E.energy g := by
    apply NNReal.eq
    rw [show (-g) = (-1 : ℝ) • g from (neg_one_smul ℝ g).symm, E.smul_energy,
      abs_neg, abs_one, Real.one_rpow, one_mul]
  rw [heng] at hM
  have hB₀ : t * (p * E.variation h f g) ≤ ε * t *
      ((E.energy f : ℝ) + (E.energy g : ℝ)) + d := by linarith only [h₁, hM]
  have hB₁ : t * (-(p * E.variation h f g)) ≤ ε * t *
      ((E.energy f : ℝ) + (E.energy g : ℝ)) + d := by linarith only [h₀, hP]
  have hA : t * |p * E.variation h f g| ≤ ε * t *
      ((E.energy f : ℝ) + (E.energy g : ℝ)) + d := by
    rw [abs_eq_max_neg, mul_max_of_nonneg _ _ ht.le]
    exact max_le hB₀ hB₁
  rw [abs_mul, abs_of_nonneg (zero_lt_one.trans E.one_lt_p).le] at hA
  apply (mul_le_mul_iff_right₀ ht).mp
  calc
    _ ≤ _ := hA
    _ = t * (ε * ((E.energy f : ℝ) + (E.energy g : ℝ))) + d := by ring
    _ = _ := by
      have hh : t * (d / t) = d := by rw [mul_comm, div_mul_cancel₀ _ ht.ne']
      rw [mul_add t, hh]

end CarpetEnergy.SelfSimilarPEnergy
