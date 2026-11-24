import EnergyNormingMatrix
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Directional derivatives and norming functionals

At a unit profile the derivative of the p-th power of a seminorm,
divided by p, is a norming functional whenever that derivative is
linear in the direction.
-/

open Filter Function Set
open scoped Topology

namespace CarpetEnergy

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

theorem norming_of_unit_directional_derivative (S : Seminorm ℝ X) {p : ℝ} (hp : 0 < p)
    (f : X) (hf : S f = 1) (ℓ : X →ₗ[ℝ] ℝ)
    (hderiv : ∀ z : X, HasDerivAt (fun t : ℝ ↦ S (f + t • z) ^ p) (p * ℓ z) 0) :
    ℓ f = 1 ∧ ∀ z, |ℓ z| ≤ S z := by
  have hroot (z : X) : HasDerivAt (fun t : ℝ ↦ S (f + t • z)) (ℓ z) 0 := by
    have h := (hderiv z).rpow_const (p := p⁻¹)
      (Or.inl (show S (f + (0 : ℝ) • z) ^ p ≠ 0 by rw [zero_smul, add_zero, hf, Real.one_rpow]; exact one_ne_zero))
    rw [zero_smul, add_zero, hf, Real.one_rpow, Real.one_rpow, mul_one] at h
    rw [show p * ℓ z * p⁻¹ = ℓ z by field_simp] at h
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
    exact (Real.rpow_rpow_inv (apply_nonneg S (f + t • z)) hp.ne').symm
  have hself : HasDerivAt (fun t : ℝ ↦ S (f + t • f)) 1 0 := by
    have hh : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add 1
    refine hh.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
    change -1 < t at ht
    rw [show f + t • f = (1 + t) • f by rw [add_smul, one_smul], map_smul_eq_mul, hf, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1 + t)]
  refine ⟨(hroot f).unique hself, fun z ↦ ?_⟩
  rw [← Real.norm_eq_abs]
  apply (hroot z).le_of_lip' (apply_nonneg S z)
  filter_upwards with t
  rw [zero_smul, add_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    _ ≤ S ((f + t • z) - f) := abs_sub_map_le_sub S _ _
    _ = S z * |t| := by rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, mul_comm]

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The derivative rows at an independent pair of unit continuous
profiles form an invertible two-by-two matrix. -/
theorem first_variation_matrix_det_ne_zero
    (f g : E.continuousCore) (ℓ₁ ℓ₂ : E.continuousCore →ₗ[ℝ] ℝ)
    (hf : E.rootSeminorm (E.continuousCoreToDomain f) = 1)
    (hg : E.rootSeminorm (E.continuousCoreToDomain g) = 1)
    (h₀ : 0 < E.rootSeminorm (E.continuousCoreToDomain (f - g)))
    (h₁ : 0 < E.rootSeminorm (E.continuousCoreToDomain (f + g)))
    (hderiv₁ : ∀ z : E.continuousCore, HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (f + t • z)) : ℝ)) (p * ℓ₁ z) 0)
    (hderiv₂ : ∀ z : E.continuousCore, HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (g + t • z)) : ℝ)) (p * ℓ₂ z) 0) :
    ℓ₁ f * ℓ₂ g - ℓ₁ g * ℓ₂ f ≠ 0 := by
  let S := E.rootSeminorm.comp E.continuousCoreToDomain
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hE (z : E.continuousCore) : S z ^ p = (E.energy (E.continuousCoreToDomain z) : ℝ) := by
    change E.rootSeminorm _ ^ p = _
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (by positivity) hp.ne'
  obtain ⟨hF, hℓ₁⟩ := norming_of_unit_directional_derivative S hp f hf ℓ₁
    (fun z ↦ by simp only [hE]; exact hderiv₁ z)
  obtain ⟨hG, hℓ₂⟩ := norming_of_unit_directional_derivative S hp g hg ℓ₂
    (fun z ↦ by simp only [hE]; exact hderiv₂ z)
  exact E.norming_matrix_det_ne_zero f g ℓ₁ ℓ₂ hf.le hg.le h₀ h₁ hF hG hℓ₁ hℓ₂


private theorem scaled_first_variation_unit
    (f : E.continuousCore) (ℓ : E.continuousCore →ₗ[ℝ] ℝ)
    (a : ℝ) (ha : 0 < a)
    (hderiv : ∀ z : E.continuousCore, HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (f + t • z)) : ℝ)) (p * ℓ z) 0)
    (z : E.continuousCore) :
    HasDerivAt (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (a⁻¹ • f + t • z)) : ℝ))
      (p * (((a⁻¹) ^ p * a) • ℓ) z) 0 := by
  have hh : HasDerivAt (fun t : ℝ ↦ a * t) a 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul a
  have hh' : HasDerivAt (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (f + t • z)) : ℝ))
      (p * ℓ z) ((fun t : ℝ ↦ a * t) 0) := by simpa only [mul_zero] using hderiv z
  have ht := (hh'.comp (0 : ℝ) hh).const_mul ((a⁻¹) ^ p)
  have he (t : ℝ) : a⁻¹ • f + t • z = a⁻¹ • (f + (a * t) • z) := by
    rw [smul_add, smul_smul, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  have hEq : (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (a⁻¹ • f + t • z)) : ℝ)) =
    (fun t : ℝ ↦ (a⁻¹) ^ p * (E.energy (E.continuousCoreToDomain (f + (a * t) • z)) : ℝ)) := by
    funext t
    rw [he, map_smul, E.smul_energy, abs_of_nonneg (inv_nonneg.mpr ha.le)]
  rw [hEq, LinearMap.smul_apply, smul_eq_mul]
  rw [show p * ((a⁻¹ ^ p * a) * ℓ z) = a⁻¹ ^ p * (p * ℓ z * a) by ring]
  exact ht

/-- The determinant argument in Proposition 5.6 without imposing a
unit-energy normalization on the original continuous profiles. -/
theorem first_variation_matrix_det_ne_zero_of_independent
    (f g : E.continuousCore) (ℓ₁ ℓ₂ : E.continuousCore →ₗ[ℝ] ℝ)
    (hind : ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      0 < E.rootSeminorm (E.continuousCoreToDomain (a • f + b • g)))
    (hderiv₁ : ∀ z : E.continuousCore, HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (f + t • z)) : ℝ)) (p * ℓ₁ z) 0)
    (hderiv₂ : ∀ z : E.continuousCore, HasDerivAt
      (fun t : ℝ ↦ (E.energy (E.continuousCoreToDomain (g + t • z)) : ℝ)) (p * ℓ₂ z) 0) :
    ℓ₁ f * ℓ₂ g - ℓ₁ g * ℓ₂ f ≠ 0 := by
  let S := E.rootSeminorm.comp E.continuousCoreToDomain
  let a := S f
  let b := S g
  have ha : 0 < a := by
    change 0 < E.rootSeminorm (E.continuousCoreToDomain f)
    simpa only [one_smul, zero_smul, add_zero] using hind 1 0 (Or.inl one_ne_zero)
  have hb : 0 < b := by
    change 0 < E.rootSeminorm (E.continuousCoreToDomain g)
    simpa only [one_smul, zero_smul, zero_add] using hind 0 1 (Or.inr one_ne_zero)
  let u := a⁻¹ • f
  let v := b⁻¹ • g
  have hu : S u = 1 := by
    rw [show u = a⁻¹ • f from rfl, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ha.le)]
    exact inv_mul_cancel₀ ha.ne'
  have hv : S v = 1 := by
    rw [show v = b⁻¹ • g from rfl, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hb.le)]
    exact inv_mul_cancel₀ hb.ne'
  have h₀ : 0 < S (u - v) := by
    change 0 < S (a⁻¹ • f - b⁻¹ • g)
    rw [sub_eq_add_neg, show -(b⁻¹ • g) = (-b⁻¹) • g from (neg_smul _ _).symm]
    exact hind _ _ (Or.inl (inv_ne_zero ha.ne'))
  have h₁ : 0 < S (u + v) := hind _ _ (Or.inl (inv_ne_zero ha.ne'))
  let q₁ := (a⁻¹) ^ p * a
  let q₂ := (b⁻¹) ^ p * b
  have hh := E.first_variation_matrix_det_ne_zero u v (q₁ • ℓ₁) (q₂ • ℓ₂) hu hv h₀ h₁
    (E.scaled_first_variation_unit f ℓ₁ a ha hderiv₁)
    (E.scaled_first_variation_unit g ℓ₂ b hb hderiv₂)
  change (q₁ • ℓ₁) (a⁻¹ • f) * (q₂ • ℓ₂) (b⁻¹ • g) -
    (q₁ • ℓ₁) (b⁻¹ • g) * (q₂ • ℓ₂) (a⁻¹ • f) ≠ 0 at hh
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul] at hh
  intro hz
  apply hh
  calc
    _ = (q₁ * q₂ * a⁻¹ * b⁻¹) * (ℓ₁ f * ℓ₂ g - ℓ₁ g * ℓ₂ f) := by ring
    _ = 0 := by rw [hz, mul_zero]

end SelfSimilarPEnergy
end CarpetEnergy
