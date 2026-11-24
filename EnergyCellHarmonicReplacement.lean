import EnergyHarmonicReplacement
import EnergyComparison
import CarpetNeighborhoodMass

/-!
# Local harmonic replacement on a union of cells

Prescribing the exterior values fixes the energy on each exterior
cell. Global minimization is then equivalent to minimization of the
sum of the energies on the selected cells.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem pullbackWord_eq_of_ae_eq_on_cell (w : List (Fin 8)) {f g : E.domain}
    (h : (f : CarpetLp p) =ᵐ[carpetMeasure.restrict (range (wordMap w))] (g : CarpetLp p)) :
    E.pullbackWord w f = E.pullbackWord w g := by
  apply Subtype.ext
  apply Lp.ext
  have h' := (ae_restrict_iff' (measurableEmbedding_wordMap w).measurableSet_range).mp h
  have hcomp := (quasiMeasurePreserving_wordMap w).ae h'
  filter_upwards [hcomp, E.pullbackWord_isLpPullback w f, E.pullbackWord_isLpPullback w g]
    with x hx hf hg
  exact hf.trans ((hx (mem_range_self x)).trans hg.symm)

/-- The part of the energy carried by the given level cells. -/
noncomputable def cellUnionEnergy {n : ℕ} (S : Finset (Fin n → Fin 8)) (f : E.domain) : ℝ :=
  E.scalingFactor ^ n * ∑ w ∈ S, (E.energy (E.pullbackWord (List.ofFn w) f) : ℝ)

theorem cellUnionEnergy_eq_of_ae_eq {n : ℕ} (S : Finset (Fin n → Fin 8)) {f g : E.domain}
    (h : (f : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion S)] (g : CarpetLp p)) :
    E.cellUnionEnergy S f = E.cellUnionEnergy S g := by
  unfold cellUnionEnergy
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun w hw ↦ ?_)
  have hw' : range (wordMap (List.ofFn w)) ⊆ wordCellUnion S := by
    intro x hx
    exact mem_iUnion.2 ⟨w, mem_iUnion.2 ⟨hw, hx⟩⟩
  rw [E.pullbackWord_eq_of_ae_eq_on_cell (List.ofFn w)
    (h.filter_mono (ae_mono (Measure.restrict_mono hw' le_rfl)))]

theorem energy_eq_cellUnionEnergy_add_compl {n : ℕ} (S : Finset (Fin n → Fin 8)) (f : E.domain) :
    (E.energy f : ℝ) = E.cellUnionEnergy S f + E.cellUnionEnergy Sᶜ f := by
  rw [E.energy_eq_sum_words n f, cellUnionEnergy, cellUnionEnergy, ← mul_add,
    Finset.sum_add_sum_compl]

theorem minimizesWithExterior_wordCellUnion_iff {n : ℕ} (S : Finset (Fin n → Fin 8))
    (f : E.domain) :
    E.MinimizesWithExterior (wordCellUnion Sᶜ) f ↔
      ∀ g : E.domain, (g : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion Sᶜ)] (f : CarpetLp p) →
        E.cellUnionEnergy S f ≤ E.cellUnionEnergy S g := by
  have hle (g : E.domain)
      (hg : (g : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion Sᶜ)] (f : CarpetLp p)) :
      E.energy f ≤ E.energy g ↔ E.cellUnionEnergy S f ≤ E.cellUnionEnergy S g := by
    rw [← NNReal.coe_le_coe, E.energy_eq_cellUnionEnergy_add_compl S f,
      E.energy_eq_cellUnionEnergy_add_compl S g, E.cellUnionEnergy_eq_of_ae_eq Sᶜ hg]
    exact add_le_add_iff_right _
  exact ⟨fun h g hg ↦ (hle g hg).mp (h g hg), fun h g hg ↦ (hle g hg).mpr (h g hg)⟩

end CarpetEnergy.SelfSimilarPEnergy
