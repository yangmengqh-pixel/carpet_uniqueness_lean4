import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Comparable seminorms on a one-dimensional quotient

The pointwise proportionality calculation in Proposition 7.5 of Yang's
*On the uniqueness of p-energy on the Sierpiński carpet*.
-/

open Filter Set
open scoped Topology

namespace CarpetEnergy

/-- A rational seminorm bounded above by a seminorm realized in a one-dimensional
real normed space is a scalar multiple of it. The rational image need not itself
have dimension one over the rationals. -/
theorem seminorm_eq_mul_of_finrank_one {D V : Type*} [AddCommGroup D] [Module ℚ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R T : Seminorm ℚ D) (j : D →ₛₗ[algebraMap ℚ ℝ] V) (hR : ∀ f, R f = ‖j f‖)
    (hdim : Module.finrank ℝ V = 1)
    {U : ℝ} (hupper : ∀ f, T f ≤ U * R f) {g : D} (hg : 0 < R g) :
    ∀ f, T f = (T g / R g) * R f := by
  have hjg : j g ≠ 0 := norm_pos_iff.mp (hR g ▸ hg)
  intro f
  obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hdim hjg (j f)
  have hRf : R f = |t| * R g := by
    rw [hR f, ← ht, norm_smul, Real.norm_eq_abs, hR g]
  obtain ⟨q, _, _, hq⟩ := Real.exists_seq_rat_strictMono_tendsto t
  have hsmall : Tendsto (fun n ↦ R (f - q n • g)) atTop (𝓝 0) := by
    have hconv : Tendsto (fun n ↦ ‖j f - (q n : ℝ) • j g‖) atTop (𝓝 ‖j f - t • j g‖) :=
      (tendsto_const_nhds.sub (hq.smul tendsto_const_nhds)).norm
    rw [ht, sub_self, norm_zero] at hconv
    have cast_eq (r : ℚ) : algebraMap ℚ ℝ r = (r : ℝ) := rfl
    simpa only [hR, map_sub, map_smulₛₗ, cast_eq] using hconv
  have hscalar : Tendsto (fun n ↦ T (q n • g)) atTop (𝓝 (|t| * T g)) := by
    have hconv := (hq.abs.mul_const (T g))
    simpa only [map_smul_eq_mul, ← Rat.norm_cast_real, Real.norm_eq_abs] using hconv
  have herror : Tendsto (fun n ↦ U * R (f - q n • g)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul U
  have hT : T f = |t| * T g := by
    apply le_antisymm
    · have hconv := herror.add hscalar
      rw [zero_add] at hconv
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hconv
      filter_upwards with n
      calc
        T f = T ((f - q n • g) + q n • g) := by rw [sub_add_cancel]
        _ ≤ T (f - q n • g) + T (q n • g) := map_add_le_add T _ _
        _ ≤ U * R (f - q n • g) + T (q n • g) := add_le_add (hupper _) le_rfl
    · have hconv := (tendsto_const_nhds (x := T f)).add herror
      rw [add_zero] at hconv
      apply le_of_tendsto_of_tendsto hscalar hconv
      filter_upwards with n
      calc
        T (q n • g) = T (f - (f - q n • g)) := by rw [sub_sub_cancel]
        _ ≤ T f + T (f - q n • g) := map_sub_le_add T _ _
        _ ≤ T f + U * R (f - q n • g) := add_le_add le_rfl (hupper _)
  rw [hT, hRf, ← mul_assoc, mul_comm (T g / R g) |t|, mul_assoc, div_mul_cancel₀ _ hg.ne']

/-- Taking the p-th powers of the comparable seminorms gives a single
pointwise multiplier in the original comparison interval. -/
theorem exists_rpow_eq_mul_of_finrank_one {D V : Type*} [AddCommGroup D] [Module ℚ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R T : Seminorm ℚ D) (j : D →ₛₗ[algebraMap ℚ ℝ] V) (hR : ∀ f, R f = ‖j f‖)
    (hdim : Module.finrank ℝ V = 1) {p lower upper : ℝ} (hp : 0 < p)
    (hlo : 0 ≤ lower) (hup : 0 ≤ upper)
    (hcompare : ∀ f, lower ^ p⁻¹ * R f ≤ T f ∧ T f ≤ upper ^ p⁻¹ * R f)
    {g : D} (hg : 0 < R g) :
    ∃ c ∈ Icc lower upper, ∀ f, T f ^ p = c * R f ^ p := by
  let b := T g / R g
  have hb : 0 ≤ b := div_nonneg (apply_nonneg T g) hg.le
  have hb₁ : lower ^ p⁻¹ ≤ b := (le_div_iff₀ hg).mpr (hcompare g).1
  have hb₂ : b ≤ upper ^ p⁻¹ := (div_le_iff₀ hg).mpr (hcompare g).2
  have h₁ := Real.rpow_le_rpow (Real.rpow_nonneg hlo _) hb₁ hp.le
  have h₂ := Real.rpow_le_rpow hb hb₂ hp.le
  rw [Real.rpow_inv_rpow hlo hp.ne'] at h₁
  rw [Real.rpow_inv_rpow hup hp.ne'] at h₂
  refine ⟨b ^ p, ⟨h₁, h₂⟩, fun f ↦ ?_⟩
  rw [seminorm_eq_mul_of_finrank_one R T j hR hdim (fun f ↦ (hcompare f).2) hg f,
    Real.mul_rpow hb (apply_nonneg R f)]

end CarpetEnergy
