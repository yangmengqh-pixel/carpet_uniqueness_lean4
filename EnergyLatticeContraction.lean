import EnergyRelativeGeneralizedContraction
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Lattice contraction

Sorting two real coordinates is a contraction for the sum of the
p-th powers of the coordinate differences. The generalized
p-contraction property therefore gives the lattice energy inequality.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

private theorem abs_sub_rpow_ordered {p a b c d : ℝ}
    (hp : 1 ≤ p) (hab : a ≤ b) (hcd : c ≤ d) :
    |a - c| ^ p + |b - d| ^ p ≤ |a - d| ^ p + |b - c| ^ p := by
  let s := b - a + (d - c)
  have hs : 0 ≤ s := by dsimp [s]; linarith
  rcases hs.eq_or_lt with hs | hs
  · have heq : c = d := by dsimp [s] at hs; linarith
    rw [heq]
  let t := (b - a) / s
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hab) hs.le
  have ht' : t ≤ 1 := (div_le_one hs).mpr (by dsimp [s]; linarith)
  have hsum : t + (1 - t) = 1 := by ring
  have hts : t * s = b - a := div_mul_cancel₀ _ hs.ne'
  have h₁ : t * (b - c) + (1 - t) * (a - d) = b - d := by
    dsimp [s] at hts
    linarith only [hts]
  have h₂ : (1 - t) * (b - c) + t * (a - d) = a - c := by
    dsimp [s] at hts
    linarith only [hts]
  have hnorm : ConvexOn ℝ (univ : Set ℝ) norm := convexOn_norm convex_univ
  have hpos : norm '' (univ : Set ℝ) ⊆ Ici (0 : ℝ) := by
    rintro _ ⟨x, _, rfl⟩
    exact norm_nonneg x
  -- The image of the norm is the nonnegative half-line.
  have hrange : norm '' (univ : Set ℝ) = Ici (0 : ℝ) := by
    refine le_antisymm hpos ?_
    intro x hx
    exact ⟨x, mem_univ _, by rw [Real.norm_eq_abs, abs_of_nonneg hx]⟩
  have hconv : ConvexOn ℝ (univ : Set ℝ) (fun x ↦ |x| ^ p) := by
    have hpow' : ConvexOn ℝ (norm '' (univ : Set ℝ)) (fun x ↦ x ^ p) := by
      rw [hrange]
      exact convexOn_rpow hp
    simpa only [Function.comp_def, Real.norm_eq_abs] using hpow'.comp hnorm
      (fun x hx y _ hxy ↦ Real.rpow_le_rpow (hpos hx) hxy (zero_le_one.trans hp))
  have hbd := hconv.2 (mem_univ (b - c)) (mem_univ (a - d)) ht (sub_nonneg.mpr ht') hsum
  have hac := hconv.2 (mem_univ (b - c)) (mem_univ (a - d)) (sub_nonneg.mpr ht') ht
    (by rw [add_comm]; exact hsum)
  simp only [smul_eq_mul, h₁] at hbd
  simp only [smul_eq_mul, h₂] at hac
  linarith only [hbd, hac]

theorem abs_sub_rpow_min_add_max_le {p : ℝ} (hp : 1 ≤ p) (a b c d : ℝ) :
    |min a b - min c d| ^ p + |max a b - max c d| ^ p ≤
      |a - c| ^ p + |b - d| ^ p := by
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · simp only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd, le_rfl]
  · rw [min_eq_left hab, max_eq_right hab, min_eq_right hdc, max_eq_left hdc]
    simpa only [add_comm] using abs_sub_rpow_ordered hp hab hdc
  · rw [min_eq_right hba, max_eq_left hba, min_eq_left hcd, max_eq_right hcd]
    simpa only [add_comm] using abs_sub_rpow_ordered hp hba hcd
  · simp only [min_eq_right hba, max_eq_left hba, min_eq_right hdc, max_eq_left hdc]
    rw [add_comm]

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The pointwise minimum and maximum belong to the domain and satisfy
the submodular energy inequality. -/
theorem exists_lattice_energy_le (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ E.energy f))
    (f g : E.domain) :
    ∃ u v : E.domain,
      ((u : CarpetLp p) =ᵐ[carpetMeasure] fun x ↦ min ((f : CarpetLp p) x) ((g : CarpetLp p) x)) ∧
      ((v : CarpetLp p) =ᵐ[carpetMeasure] fun x ↦ max ((f : CarpetLp p) x) ((g : CarpetLp p) x)) ∧
      E.energy u + E.energy v ≤ E.energy f + E.energy g := by
  let T (z : Fin 2 → ℝ) : Fin 2 → ℝ := ![min (z 0) (z 1), max (z 0) (z 1)]
  let L : Fin 2 → ℝ≥0 := fun _ ↦ 1
  have hproj (i : Fin 2) : LipschitzWith 1 (fun z : Fin 2 → ℝ ↦ z i) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa only [NNReal.coe_one, one_mul] using dist_le_pi_dist x y i
  have hLip (i : Fin 2) : LipschitzWith (L i) fun z ↦ T z i := by
    fin_cases i
    · exact (hproj 0).min (hproj 1)
    · exact (hproj 0).max (hproj 1)
  have h0 (i : Fin 2) : T 0 i = 0 := by fin_cases i <;> simp [T]
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hT (x y : Fin 2 → ℝ) :
      finitePowerSum p (fun i ↦ |T x i - T y i|) ≤
        finitePowerSum p (fun i ↦ |x i - y i|) := by
    unfold finitePowerSum
    simp only [Fin.sum_univ_two]
    apply Real.rpow_le_rpow (by positivity) _ (inv_nonneg.mpr hp.le)
    exact abs_sub_rpow_min_add_max_le E.one_lt_p.le (x 0) (x 1) (y 0) (y 1)
  obtain ⟨hD, hle⟩ := hG 2 2 p p hp le_rfl le_rfl T hT hLip h0
  let z : Fin 2 → E.domain := ![f, g]
  let u := E.domainMixedOperation hD z 0
  let v := E.domainMixedOperation hD z 1
  have hu := ae_pointwiseLp T hLip h0 (fun i ↦ (z i : CarpetLp p)) 0
  have hv := ae_pointwiseLp T hLip h0 (fun i ↦ (z i : CarpetLp p)) 1
  have h := hle z
  simp only [div_self hp.ne', finitePowerSum, Real.rpow_one, inv_one, Fin.sum_univ_two] at h
  refine ⟨u, v, ?_, ?_, NNReal.coe_le_coe.mp ?_⟩
  · exact hu
  · exact hv
  · push_cast
    exact h

end SelfSimilarPEnergy

end CarpetEnergy
