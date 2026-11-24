import EnergyFoldingAmplification
import CarpetCrossingCapacity

/-!
# Quantitative product estimate on the continuous energy core
-/

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Pointwise multiplication stays in the continuous finite-energy core. -/
noncomputable def mulCore (f g : E.continuousCore) : E.continuousCore :=
  ⟨f.val * g.val, (E.zeroComponent.continuousKernel_mul
    ⟨f.property, rfl⟩ ⟨g.property, rfl⟩).choose⟩

theorem mulCore_apply (f g : E.continuousCore) (x : CarpetPoints) :
    (E.mulCore f g).val x = f.val x * g.val x := rfl

private theorem rootSeminorm_square_le (f : E.continuousCore) :
    E.rootSeminorm (E.continuousCoreToDomain (E.mulCore f f)) ≤
      2 * ‖f.val‖ * E.rootSeminorm (E.continuousCoreToDomain f) := by
  let M : NNReal := ⟨‖f.val‖, norm_nonneg _⟩
  obtain ⟨φ, hφ, he⟩ := exists_clipped_square M
  obtain ⟨v, hv, happ, henergy⟩ := E.exists_continuous_comp_energy_le_mul f.val f.property hφ
  have hv' : v = (E.mulCore f f).val := by
    ext x
    rw [E.mulCore_apply, happ]
    exact he _ (by
      change |f.val x| ≤ ‖f.val‖
      rw [← Real.norm_eq_abs]
      exact f.val.norm_coe_le_norm x)
  have hd : (⟨continuousLp p v, hv⟩ : E.domain) =
      E.continuousCoreToDomain (E.mulCore f f) := by
    apply Subtype.ext
    exact congrArg (continuousLp p) hv'
  rw [hd] at henergy
  have hp := zero_lt_one.trans E.one_lt_p
  have h := Real.rpow_le_rpow (NNReal.coe_nonneg _) henergy (inv_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (NNReal.coe_nonneg _),
    Real.rpow_rpow_inv (NNReal.coe_nonneg _) hp.ne'] at h
  rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
  exact h

/-- A symmetric energy bound for products, obtained by polarization
and the Lipschitz bound for the scalar square on a bounded interval. -/
theorem rootSeminorm_mulCore_le (f g : E.continuousCore) :
    E.rootSeminorm (E.continuousCoreToDomain (E.mulCore f g)) ≤
      (‖f.val‖ + ‖g.val‖) *
        (E.rootSeminorm (E.continuousCoreToDomain f) +
          E.rootSeminorm (E.continuousCoreToDomain g)) := by
  let S := E.rootSeminorm.comp E.continuousCoreToDomain
  let a := E.mulCore (f + g) (f + g)
  let b := E.mulCore (f - g) (f - g)
  have he : E.mulCore f g = (1 / 4 : ℝ) • (a - b) := by
    apply Subtype.ext
    ext x
    change f.val x * g.val x = (1 / 4 : ℝ) *
      ((f.val x + g.val x) * (f.val x + g.val x) -
        (f.val x - g.val x) * (f.val x - g.val x))
    ring
  have ha : S a ≤ 2 * (‖f.val‖ + ‖g.val‖) * (S f + S g) := by
    refine (E.rootSeminorm_square_le (f + g)).trans ?_
    have hn : ‖(f + g).val‖ ≤ ‖f.val‖ + ‖g.val‖ := norm_add_le _ _
    exact mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) (S.add_le' f g)
      (apply_nonneg S _) (by positivity)
  have hb : S b ≤ 2 * (‖f.val‖ + ‖g.val‖) * (S f + S g) := by
    refine (E.rootSeminorm_square_le (f - g)).trans ?_
    have hn : ‖(f - g).val‖ ≤ ‖f.val‖ + ‖g.val‖ := norm_sub_le _ _
    have hs : S (f - g) ≤ S f + S g := by
      rw [sub_eq_add_neg]
      exact (S.add_le' f (-g)).trans_eq (congrArg (S f + ·) (S.neg' g))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hs
      (apply_nonneg S _) (by positivity)
  have hab : S (a - b) ≤ S a + S b := by
    rw [sub_eq_add_neg]
    exact (S.add_le' a (-b)).trans_eq (congrArg (S a + ·) (S.neg' b))
  change S (E.mulCore f g) ≤ (‖f.val‖ + ‖g.val‖) * (S f + S g)
  rw [he, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  linarith only [ha, hb, hab]

/-- Rescaling the factors separately gives a cross bound, so a
uniformly small factor contributes only its supremum to the term
involving the other factor's energy. -/
theorem rootSeminorm_mulCore_le_cross (f g : E.continuousCore) :
    E.rootSeminorm (E.continuousCoreToDomain (E.mulCore f g)) ≤
      2 * (‖g.val‖ * E.rootSeminorm (E.continuousCoreToDomain f) +
        ‖f.val‖ * E.rootSeminorm (E.continuousCoreToDomain g)) := by
  let S := E.rootSeminorm.comp E.continuousCoreToDomain
  change S (E.mulCore f g) ≤ 2 * (‖g.val‖ * S f + ‖f.val‖ * S g)
  by_cases hf : f = 0
  · subst f
    have hz : E.mulCore (0 : E.continuousCore) g = 0 := by
      apply Subtype.ext; ext x; exact zero_mul _
    rw [hz, map_zero]
    positivity
  by_cases hg : g = 0
  · subst g
    have hz : E.mulCore f (0 : E.continuousCore) = 0 := by
      apply Subtype.ext; ext x; exact mul_zero _
    rw [hz, map_zero]
    positivity
  let a := ‖f.val‖
  let b := ‖g.val‖
  have ha : 0 < a := norm_pos_iff.mpr (fun hz ↦ hf (Subtype.ext hz))
  have hb : 0 < b := norm_pos_iff.mpr (fun hz ↦ hg (Subtype.ext hz))
  let u := a⁻¹ • f
  let v := b⁻¹ • g
  have he : E.mulCore f g = (a * b) • E.mulCore u v := by
    apply Subtype.ext
    ext x
    change f.val x * g.val x = a * b * ((a⁻¹ * f.val x) * (b⁻¹ * g.val x))
    field_simp [ha.ne', hb.ne']
  have hu : ‖u.val‖ = 1 := by
    change ‖a⁻¹ • f.val‖ = 1
    exact (norm_smul_of_nonneg (inv_nonneg.mpr ha.le) f.val).trans (inv_mul_cancel₀ ha.ne')
  have hv : ‖v.val‖ = 1 := by
    change ‖b⁻¹ • g.val‖ = 1
    exact (norm_smul_of_nonneg (inv_nonneg.mpr hb.le) g.val).trans (inv_mul_cancel₀ hb.ne')
  have hsu : S u = a⁻¹ * S f := by
    dsimp only [u]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  have hsv : S v = b⁻¹ * S g := by
    dsimp only [v]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
  have hbound := E.rootSeminorm_mulCore_le u v
  change S (E.mulCore u v) ≤ (‖u.val‖ + ‖v.val‖) * (S u + S v) at hbound
  rw [hu, hv, hsu, hsv] at hbound
  rw [he, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (mul_pos ha hb)]
  calc
    _ ≤ (a * b) * ((1 + 1) * (a⁻¹ * S f + b⁻¹ * S g)) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg ha.le hb.le)
    _ = 2 * (b * S f + a * S g) := by
      field_simp [ha.ne', hb.ne']
      ring

end CarpetEnergy.SelfSimilarPEnergy
