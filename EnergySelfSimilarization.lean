import EnergyDiscreteLimit
import EnergyRenormalizationLimit

/-!
# Self-similarization on the finite-energy domain

When an energy satisfying Definition 2.1 is given, its domain supplies
the pullback maps and its energy supplies a fixed comparison bound.
A Γ-limit of the rescaled cell graph energies can then be averaged
to a functional obeying the exact self-similar identity.
-/

open Filter Function Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem renormalization_iterate_le
    (A B : ℝ) (F : E.domain → ℝ)
    (h : ∀ f, A * (E.energy f : ℝ) ≤ F f ∧ F f ≤ B * (E.energy f : ℝ)) :
    ∀ n f, A * (E.energy f : ℝ) ≤
      ((renormalize E.scalingFactor E.pullback)^[n]) F f ∧
      ((renormalize E.scalingFactor E.pullback)^[n]) F f ≤ B * (E.energy f : ℝ) := by
  let T := renormalize E.scalingFactor E.pullback
  have hρ := E.isScalingFactor_scalingFactor.1
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    intro f
    rw [Function.iterate_succ_apply']
    change _ ≤ T (T^[n] F) f ∧ T (T^[n] F) f ≤ _
    dsimp only [T, renormalize]
    have hmul (C : ℝ) : C * (E.energy f : ℝ) =
        E.scalingFactor * ∑ i : Fin 8, C * (E.energy (E.pullback i f) : ℝ) := by
      rw [← Finset.mul_sum, E.isScalingFactor_scalingFactor.2 f, mul_left_comm C]
    constructor
    · rw [hmul A]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ (ih (E.pullback i f)).1) hρ.le
    · rw [hmul B]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ (ih (E.pullback i f)).2) hρ.le

/-- A subsequential Γ-limit and its self-similarized limit, on the domain
of a given Definition 2.1 energy. Both retain the comparison bounds. -/
theorem exists_selfSimilarized_discreteLimit [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ (j : ℕ → ℕ) (F : CarpetLp p → ℝ≥0∞) (l : Filter ℕ) (G : E.domain → ℝ),
      ∃ A > (0 : ℝ), ∃ B > (0 : ℝ),
        StrictMono j ∧ IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F ∧
        l.NeBot ∧ l ≤ atTop ∧
        (∀ f, A * (E.energy f : ℝ) ≤ G f ∧ G f ≤ B * (E.energy f : ℝ)) ∧
        (∀ f, Tendsto (fun n ↦ renormalizationMean E.scalingFactor E.pullback
          (fun v : E.domain ↦ (F v).toReal) n f) l (𝓝 (G f))) ∧
        (∀ f, G f = E.scalingFactor * ∑ i, G (E.pullback i f)) := by
  obtain ⟨j, F, hj, hF⟩ := exists_discreteCellEnergy_gammaLimit p E.scalingFactor
  obtain ⟨A, hA, B, hB, hcomp⟩ := IsGammaLimit.discreteLimit_comparable E hj hF
  have hi := E.renormalization_iterate_le A B (fun v : E.domain ↦ (F v).toReal) hcomp
  obtain ⟨l, G, hl₀, hl, h, ht, heq⟩ := exists_renormalization_fixedPoint
    E.scalingFactor E.pullback (fun v : E.domain ↦ (F v).toReal)
    (fun v ↦ A * (E.energy v : ℝ)) (fun v ↦ B * (E.energy v : ℝ))
    (fun n f ↦ (hi n f).1) (fun n f ↦ (hi n f).2)
  exact ⟨j, F, l, G, A, hA, B, hB, hj, hF, hl₀, hl, h, ht, fun f ↦ (congrFun heq f).symm⟩

end CarpetEnergy.SelfSimilarPEnergy
