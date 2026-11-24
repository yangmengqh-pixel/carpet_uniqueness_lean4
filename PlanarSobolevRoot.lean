import SmoothPowerRoot
import WeakDerivativeChain

/-!
# Sobolev regularity of the p-th root of the planar density

The weighted derivative identities control the derivatives of
smooth regularizations of the density's root. Dominated convergence
gives the weak derivatives of the root itself.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

/-- First-order Sobolev membership on the plane, using the weak
coordinate derivatives with respect to Lebesgue measure. -/
def MemPlanarSobolev (p : ℝ) (u : (Fin 2 → ℝ) → ℝ) : Prop :=
  MemLp u (ENNReal.ofReal p) volume ∧
    ∀ i : Fin 2, ∃ v : (Fin 2 → ℝ) → ℝ, MemLp v (ENNReal.ofReal p) volume ∧
      HasWeakDirectionalDerivative volume u v (planarDirection i)

private theorem memLp_rpow_inv_of_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ} (hp : 0 < p) {ξ : X → ℝ} (hξ : Measurable ξ)
    (hξ₀ : ∀ x, 0 ≤ ξ x) (hI : Integrable ξ μ) :
    MemLp (fun x ↦ ξ x ^ p⁻¹) (ENNReal.ofReal p) μ := by
  have hM : Measurable (fun x ↦ ξ x ^ p⁻¹) :=
    (Real.continuous_rpow_const (inv_nonneg.mpr hp.le)).measurable.comp hξ
  apply (integrable_norm_rpow_iff hM.aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
  refine hI.congr (Eventually.of_forall fun x ↦ ?_)
  change ξ x = ‖ξ x ^ p⁻¹‖ ^ (ENNReal.ofReal p).toReal
  rw [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hξ₀ x) _),
    Real.rpow_inv_rpow (hξ₀ x) hp.ne']

set_option maxHeartbeats 3100000 in
theorem memPlanarSobolev_rpow_inv_of_weighted_derivatives {p : ℝ} (hp : 1 < p)
    (ξ : (Fin 2 → ℝ) → ℝ) (hξ : Measurable ξ) (hξ₀ : ∀ x, 0 ≤ ξ x)
    (hξI : Integrable ξ volume) (r : Fin 2 → (Fin 2 → ℝ) → ℝ)
    (hr : ∀ i, Measurable (r i))
    (hD : ∀ i, Integrable (fun x ↦ -(ξ x * r i x)) volume ∧
      HasWeakDirectionalDerivative volume ξ (fun x ↦ -(ξ x * r i x)) (planarDirection i) ∧
      MemLp (fun x ↦ ξ x ^ p⁻¹ * r i x) (ENNReal.ofReal p) volume) :
    MemPlanarSobolev p (fun x ↦ ξ x ^ p⁻¹) := by
  have hp₀ := zero_lt_one.trans hp
  have hpq := Real.HolderConjugate.conjExponent hp
  let q := p.conjExponent
  let : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 := hpq.ennrealOfReal
  let α := p⁻¹
  have hα : 0 < α := inv_pos.mpr hp₀
  have hα₁ : α ≤ 1 := inv_le_one_of_one_le₀ hp.le
  let u (x : Fin 2 → ℝ) := ξ x ^ α
  have hu : MemLp u (ENNReal.ofReal p) volume := memLp_rpow_inv_of_integrable hp₀ hξ hξ₀ hξI
  refine ⟨hu, fun i ↦ ?_⟩
  let v (x : Fin 2 → ℝ) := -(ξ x * r i x)
  let a (x : Fin 2 → ℝ) := u x * r i x
  let w (x : Fin 2 → ℝ) := -α * a x
  have hv : Integrable v volume := (hD i).1
  have ha : MemLp a (ENNReal.ofReal p) volume := (hD i).2.2
  refine ⟨w, ha.const_mul (-α), ?_⟩
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεL : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let γ (n : ℕ) := smoothPowerRoot α (ε n)
  have hγ (n : ℕ) : ContDiff ℝ 1 (γ n) := contDiff_smoothPowerRoot α (hε n)
  have hweak (n : ℕ) : HasWeakDirectionalDerivative volume (γ n ∘ ξ)
      (fun x ↦ deriv (γ n) (ξ x) * v x) (planarDirection i) := by
    obtain ⟨C, hC, hb⟩ := exists_deriv_smoothPowerRoot_bound hα.le hα₁ (hε n)
    exact HasWeakDirectionalDerivative.comp_bounded_deriv hξI hv (hD i).2.1 (hγ n)
      (smoothPowerRoot_zero α (ε n)) hC hb
  intro φ hφ hφs
  let D (x : Fin 2 → ℝ) := fderiv ℝ φ x (planarDirection i)
  have hDc : Continuous D := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDLp : MemLp D (ENNReal.ofReal q) volume :=
    hDc.memLp_of_hasCompactSupport (HasCompactSupport.fderiv_apply ℝ hφs (planarDirection i))
  have hφLp : MemLp φ (ENNReal.ofReal q) volume := hφ.continuous.memLp_of_hasCompactSupport hφs
  have hleftDom : Integrable (fun x ↦ u x * |D x|) volume := by
    change Integrable (u * fun x ↦ |D x|) volume
    simpa only [Real.norm_eq_abs] using hu.integrable_mul hDLp.norm
  have hrightDom : Integrable (fun x ↦ α * |a x| * |φ x|) volume := by
    simpa only [Pi.mul_apply, Real.norm_eq_abs, mul_assoc] using
      (ha.norm.integrable_mul hφLp.norm).const_mul α
  have hLeft : Tendsto (fun n ↦ ∫ x, γ n (ξ x) * D x ∂volume) atTop
      (𝓝 (∫ x, u x * D x ∂volume)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ u x * |D x|)
    · intro n
      exact (((hγ n).continuous.measurable.comp hξ).mul hDc.measurable).aestronglyMeasurable
    · exact hleftDom
    · intro n
      apply Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (smoothPowerRoot_nonneg hα.le)]
      exact mul_le_mul_of_nonneg_right (smoothPowerRoot_le_rpow hα.le hα₁ (hξ₀ x)) (abs_nonneg _)
    · exact Eventually.of_forall fun x ↦ (tendsto_smoothPowerRoot hα (hξ₀ x) hεL).mul_const (D x)
  have hRight : Tendsto (fun n ↦ ∫ x, (deriv (γ n) (ξ x) * v x) * φ x ∂volume) atTop
      (𝓝 (∫ x, w x * φ x ∂volume)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ α * |a x| * |φ x|)
    · intro n
      have hM : Measurable (fun x ↦ deriv (γ n) (ξ x)) :=
        ((hγ n).continuous_deriv (by norm_num)).measurable.comp hξ
      exact ((hM.mul (hξ.mul (hr i)).neg).mul hφ.continuous.measurable).aestronglyMeasurable
    · exact hrightDom
    · intro n
      apply Eventually.of_forall
      intro x
      have he : (deriv (γ n) (ξ x) * v x) * φ x =
          (deriv (γ n) (ξ x) * ξ x) * ((-r i x) * φ x) := by dsimp only [v]; ring
      rw [Real.norm_eq_abs, he, abs_mul (deriv (γ n) (ξ x) * ξ x) (-r i x * φ x),
        abs_mul (-r i x) (φ x), abs_neg]
      have h := deriv_smoothPowerRoot_mul_le_rpow hα.le hα₁ (hε n) (hξ₀ x)
      have h' := mul_le_mul_of_nonneg_right h (mul_nonneg (abs_nonneg (r i x)) (abs_nonneg (φ x)))
      dsimp only [a, u]
      rw [abs_mul (ξ x ^ α) (r i x), abs_of_nonneg (Real.rpow_nonneg (hξ₀ x) _)]
      exact h'.trans_eq (by ring)
    · apply Eventually.of_forall
      intro x
      have hL := (tendsto_deriv_smoothPowerRoot_mul hα (hξ₀ x) hε hεL).mul_const ((-r i x) * φ x)
      have he : α * ξ x ^ α * (-r i x * φ x) = w x * φ x := by dsimp only [w, a, u]; ring
      rw [he] at hL
      apply hL.congr
      intro n
      dsimp only [v, γ]
      ring
  have he (n : ℕ) : (∫ x, γ n (ξ x) * D x ∂volume) =
      -(∫ x, (deriv (γ n) (ξ x) * v x) * φ x ∂volume) := hweak n φ hφ hφs
  exact tendsto_nhds_unique hLeft (hRight.neg.congr fun n ↦ (he n).symm)

end CarpetEnergy
