import WeakDerivativeSmoothProduct
import SmoothScaledBallCutoff

/-!
# Compactly supported Sobolev weights agreeing near a given compact set
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

set_option maxHeartbeats 3100000 in
/-- Cut off a planar Sobolev function outside a neighborhood of a compact
set. Both the function and its weak derivatives then belong to L¹. -/
theorem exists_integrable_planar_sobolev_localization {p : ℝ} (hp : 1 < p)
    {u : Plane2 → ℝ} (hu : Measurable u) (hu₀ : ∀ x, 0 ≤ u x)
    (hSob : MemPlanarSobolev p u) {K : Set Plane2} (hK : IsCompact K) :
    ∃ a : Plane2 → ℝ, Measurable a ∧ (∀ x, 0 ≤ a x) ∧ (∀ x ∈ K, a x = u x) ∧
      Integrable a volume ∧ MemLp a (ENNReal.ofReal p) volume ∧
      ∃ g : Fin 2 → Plane2 → ℝ, ∀ i, Integrable (g i) volume ∧
        MemLp (g i) (ENNReal.ofReal p) volume ∧
        HasWeakDirectionalDerivative volume a (g i) (planarDirection i) := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 (0 : Plane2)
  obtain ⟨_, _, hcut⟩ := exists_planar_ball_cutoffs
  obtain ⟨χ, hχ, hχ01, hχ1, hχ0, _⟩ := hcut 0 r hr
  have hχs : HasCompactSupport χ := by
    apply (isCompact_closedBall (0 : Plane2) (3 * r)).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hx'
    exact hx ((hχ0 x (fun hb ↦ hx' (ball_subset_closedBall hb))).1)
  have hχtop : MemLp χ ∞ volume := hχ.continuous.memLp_of_hasCompactSupport hχs
  have hχq : MemLp χ (ENNReal.ofReal p.conjExponent) volume :=
    hχ.continuous.memLp_of_hasCompactSupport hχs
  let : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal p.conjExponent) 1 :=
    (Real.HolderConjugate.conjExponent hp).ennrealOfReal
  let a := χ * u
  refine ⟨a, hχ.continuous.measurable.mul hu, fun x ↦ mul_nonneg (hχ01 x).1 (hu₀ x),
    fun x hx ↦ ?_, ?_, ?_, ?_⟩
  · change χ x * u x = u x
    rw [hχ1 x (hKr hx), one_mul]
  · change Integrable (χ * u) volume
    rw [mul_comm χ u]
    exact hSob.1.integrable_mul hχq
  · change MemLp (χ * u) (ENNReal.ofReal p) volume
    rw [mul_comm χ u]
    exact hSob.1.mul hχtop
  choose v hv hvD using hSob.2
  let D (i : Fin 2) (x : Plane2) := fderiv ℝ χ x (planarDirection i)
  let g (i : Fin 2) (x : Plane2) := χ x * v i x + D i x * u x
  refine ⟨g, fun i ↦ ?_⟩
  have hDc : Continuous (D i) := (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDs : HasCompactSupport (D i) := hχs.fderiv_apply ℝ (planarDirection i)
  have hDq : MemLp (D i) (ENNReal.ofReal p.conjExponent) volume :=
    hDc.memLp_of_hasCompactSupport hDs
  have hDtop : MemLp (D i) ∞ volume := hDc.memLp_of_hasCompactSupport hDs
  refine ⟨?_, ?_, (hvD i).mul_smooth_cutoff hp hSob.1 (hv i) hχ hχs⟩
  · have h₀ := (hv i).integrable_mul hχq
    have h₁ := hSob.1.integrable_mul hDq
    rw [mul_comm] at h₀ h₁
    exact h₀.add h₁
  · have h₀ : MemLp (v i * χ) (ENNReal.ofReal p) volume := (hv i).mul hχtop
    have h₁ : MemLp (u * D i) (ENNReal.ofReal p) volume := hSob.1.mul hDtop
    rw [mul_comm] at h₀ h₁
    exact h₀.add h₁

end CarpetEnergy
