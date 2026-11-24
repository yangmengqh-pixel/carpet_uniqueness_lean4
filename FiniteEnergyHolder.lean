import Mathlib.Analysis.MeanInequalities

/-!
# Hölder bounds for cell mass budgets
-/

open scoped BigOperators

namespace CarpetEnergy

variable {I : Type*} [Fintype I]

/-- Hölder's inequality with the first factor written as a power of a
mass and with a scalar coefficient at each index. -/
theorem sum_abs_mul_mass_rpow_le {p q : ℝ} (hpq : p.HolderConjugate q)
    (a b c : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, |c i| * a i ^ q⁻¹ * b i ^ p⁻¹) ≤
      (∑ i, |c i| ^ q * a i) ^ q⁻¹ * (∑ i, b i) ^ p⁻¹ := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg
    (Finset.univ : Finset I) (f := fun i ↦ |c i| * a i ^ q⁻¹) (g := fun i ↦ b i ^ p⁻¹)
    hpq.symm
    (fun i _ ↦ mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (ha i) _))
    (fun i _ ↦ Real.rpow_nonneg (hb i) _)
  simp only [Real.mul_rpow (abs_nonneg _) (Real.rpow_nonneg (ha _) _),
    Real.rpow_inv_rpow (ha _) hpq.symm.ne_zero, Real.rpow_inv_rpow (hb _) hpq.ne_zero,
    one_div] at h
  exact h

theorem weighted_root_product_eq_mass_product {p q r a b : ℝ} (hpq : p.HolderConjugate q)
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    r * (a ^ q⁻¹ * b ^ p⁻¹) = (r * a) ^ q⁻¹ * (r * b) ^ p⁻¹ := by
  rw [Real.mul_rpow hr ha, Real.mul_rpow hr hb]
  calc
    _ = r ^ (q⁻¹ + p⁻¹) * (a ^ q⁻¹ * b ^ p⁻¹) := by
      rw [add_comm, hpq.inv_add_inv_eq_one, Real.rpow_one]
    _ = _ := by
      rw [Real.rpow_add' hr (by rw [hpq.symm.inv_add_inv_eq_one]; exact one_ne_zero)]
      ring

end CarpetEnergy
