import EnergyGlobalNormalization
import EnergyRelativeInvariance
import EnergyMorreyNeighborhoodBounds
import EnergyCellUnionCalculus

/-!
# Global normalization in the full domain

Translate and rescale a domain profile so that its central pullback
has mean zero and unit energy. A lower bound on the central share
of the energy gives a uniform bound on the neighboring pullbacks.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

noncomputable def globallyNormalizedDomain (w : List (Fin 8)) (f : E.domain) : E.domain :=
  E.unitEnergyScale (E.pullbackWord w f) •
    (f + ⟨constantLp p (-E.wordMean w f), E.constant_mem _⟩)

theorem globallyNormalizedDomain_harmonic (w : List (Fin 8)) {f : E.domain}
    (hf : E.IsInteriorHarmonic f) : E.IsInteriorHarmonic (E.globallyNormalizedDomain w f) :=
  (hf.add_constant E _).smul E _

theorem globallyNormalizedDomain_pullback (w : List (Fin 8)) (f : E.domain) :
    E.pullbackWord w (E.globallyNormalizedDomain w f) = E.normalizedWordPullback w f := by
  rw [globallyNormalizedDomain, E.pullbackWord_smul, E.pullbackWord_add, E.pullbackWord_constant]
  rfl

theorem globallyNormalizedDomain_wordMean (w : List (Fin 8)) (f : E.domain) :
    E.wordMean w (E.globallyNormalizedDomain w f) = 0 := by
  let c := E.wordMean w f
  let g : CarpetLp p := E.pullbackWord w f
  let a := E.unitEnergyScale (E.pullbackWord w f)
  have hInt : Integrable g carpetMeasure :=
    (Lp.memLp g).integrable (ENNReal.one_le_ofReal.mpr E.one_lt_p.le)
  have h : (E.normalizedWordPullback w f : CarpetLp p) =ᵐ[carpetMeasure]
      (fun x ↦ a * (g x + -c)) := by
    filter_upwards [Lp.coeFn_smul a (g + constantLp p (-c)),
      Lp.coeFn_add g (constantLp p (-c)), Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (-c)]
      with x h₁ h₂ h₃
    change (E.normalizedWordPullback w f : CarpetLp p) x = a * (g + constantLp p (-c)) x at h₁
    change (g + constantLp p (-c)) x = g x + constantLp p (-c) x at h₂
    change constantLp p (-c) x = -c at h₃
    rw [h₁, h₂, h₃]
  unfold wordMean
  rw [E.globallyNormalizedDomain_pullback, integral_congr_ae h]
  change (∫ x, a * (g x + -c) ∂carpetMeasure) = 0
  rw [integral_const_mul, integral_add hInt (integrable_const _), integral_const, probReal_univ,
    one_smul, show (∫ x, g x ∂carpetMeasure) = c from rfl, add_neg_cancel, mul_zero]

theorem globallyNormalizedDomain_energyMeasure (w : List (Fin 8)) (f : E.domain) :
    E.energyMeasure (E.globallyNormalizedDomain w f) =
      ENNReal.ofReal (|E.unitEnergyScale (E.pullbackWord w f)| ^ p) • E.energyMeasure f := by
  rw [globallyNormalizedDomain, E.energyMeasure_smul, E.energyMeasure_add_constant]

set_option maxHeartbeats 1400000 in
theorem sum_normalizedDomain_pullback_energy_le {n k : ℕ} (w : Fin n → Fin 8)
    (f : E.domain) (b : ℝ≥0) (hb : 0 < b)
    (hpos : 0 < E.energyMeasure f (range (wordMap (List.ofFn w))))
    (hgood : (b : ℝ≥0∞) * E.energyMeasure f (wordCellUnion (cellNeighborhood w k)) ≤
      E.energyMeasure f (range (wordMap (List.ofFn w)))) :
    (∑ v ∈ cellNeighborhood w k, (E.energy (E.pullbackWord (List.ofFn v)
      (E.globallyNormalizedDomain (List.ofFn w) f)) : ℝ)) ≤ (b : ℝ)⁻¹ := by
  let q := E.globallyNormalizedDomain (List.ofFn w) f
  have hgood' : (b : ℝ≥0∞) * E.energyMeasure q (wordCellUnion (cellNeighborhood w k)) ≤
      E.energyMeasure q (range (wordMap (List.ofFn w))) := by
    simp only [q, E.globallyNormalizedDomain_energyMeasure, smul_apply, smul_eq_mul]
    rw [mul_left_comm]
    exact mul_le_mul' le_rfl hgood
  have h := E.sum_neighborhood_energy_le_of_mass_ratio w q b hb hgood'
  rw [E.globallyNormalizedDomain_pullback,
    E.energy_normalizedWordPullback _ f (E.pullback_energy_pos_of_mass _ hpos), NNReal.coe_one,
    mul_one] at h
  exact h

end CarpetEnergy.SelfSimilarPEnergy
