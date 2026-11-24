import EnergyGammaFiniteContraction
import Mathlib.Data.Fin.VecNotation

/-!
# Two-point linear inequalities for Γ-limits
-/

open Filter Function
open scoped ENNReal Topology

namespace CarpetEnergy

theorem IsGammaLimit.twoPoint_affine_bound {X : Type*} [PseudoMetricSpace X]
    {Fₙ : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞} (hF : IsGammaLimit Fₙ F)
    (U V : (Fin 2 → X) → X) (hU : Continuous U) (hV : Continuous V)
    {a b c d : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (h : ∀ n u, a * Fₙ n (U u) + b * Fₙ n (V u) ≤ c * Fₙ n (u 0) + d * Fₙ n (u 1))
    (u : Fin 2 → X) (hu : ∀ i, F (u i) < ∞) :
    a * F (U u) + b * F (V u) ≤ c * F (u 0) + d * F (u 1) := by
  let P (f : Fin 2 → ℝ≥0∞) := c * f 0 + d * f 1
  let Q (f : Fin 2 → ℝ≥0∞) := a * f 0 + b * f 1
  let G (v : Fin 2 → X) : Fin 2 → X := ![U v, V v]
  have hP : Continuous P :=
    ((ENNReal.continuous_const_mul hc).comp (continuous_apply 0)).add
      ((ENNReal.continuous_const_mul hd).comp (continuous_apply 1))
  have hQ : Continuous Q :=
    ((ENNReal.continuous_const_mul ha).comp (continuous_apply 0)).add
      ((ENNReal.continuous_const_mul hb).comp (continuous_apply 1))
  have hG : Continuous G := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact hU
    · exact hV
  exact hF.finite_contraction_of_approximate P Q hP hQ
    (fun _ _ h ↦ add_le_add (mul_le_mul' le_rfl (h 0)) (mul_le_mul' le_rfl (h 1)))
    (fun _ ↦ G) G (fun _ _ u _ hu ↦ (hG.tendsto u).comp hu) h u hu

end CarpetEnergy
