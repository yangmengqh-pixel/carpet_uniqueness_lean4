import EnergySupportedApproximation
import EnergyHarmonicReplacement
import EnergyPiecewiseHarmonic
import EnergyAdjacentCellMeans
import CarpetNeighborhoodRescaling
import CarpetGoodCells

/-!
# Interior harmonicity with measurable exterior data

When a closed cell region stays away from the outer boundary, an
almost-everywhere exterior constraint gives an admissible variation
in the graph closure of the continuous interior tests.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem MinimizesWithExterior.mono {A B : Set CarpetPoints} (hAB : A ⊆ B)
    {f : E.domain} (hf : E.MinimizesWithExterior A f) : E.MinimizesWithExterior B f :=
  fun g hg ↦ hf g (hg.filter_mono (ae_mono (Measure.restrict_mono hAB le_rfl)))

theorem IsInteriorHarmonic.minimizesWithExterior {K A : Set CarpetPoints}
    (hK : IsClosed K) (hKint : K ⊆ carpetOuterBoundaryᶜ) (hKA : Kᶜ ⊆ A)
    {f : E.domain} (hf : E.IsInteriorHarmonic f) : E.MinimizesWithExterior A f := by
  intro g hg
  let z := g - f
  have hz : ∀ᵐ x ∂carpetMeasure.restrict Kᶜ, (z : CarpetLp p) x = 0 := by
    filter_upwards [hg.filter_mono (ae_mono (Measure.restrict_mono hKA le_rfl)),
      (Lp.coeFn_sub (g : CarpetLp p) (f : CarpetLp p)).filter_mono
        (ae_mono Measure.restrict_le_self)] with x h₁ h₂
    change (z : CarpetLp p) x = (g : CarpetLp p) x - (f : CarpetLp p) x at h₂
    rw [h₂, h₁, sub_self]
  have hclose := E.mem_supportedCoreGraph_closure_of_ae_zero hK
    isClosed_carpetOuterBoundary.isOpen_compl hKint z hz
  let S : Set E.GraphDomain := {v | (E.energy f : ℝ) ≤ (E.energy (f + E.graphToDomain v) : ℝ)}
  have hclosed : IsClosed S := isClosed_le continuous_const
    (E.continuous_graphEnergy.comp (continuous_const.add continuous_id : Continuous (E.toGraph f + ·)))
  have hsub : (E.supportedCoreGraph carpetOuterBoundaryᶜ : Set E.GraphDomain) ⊆ S := by
    rintro _ ⟨v, rfl, hv⟩
    exact NNReal.coe_le_coe.mpr (hf v.val v.property fun x hx ↦ hv x (by simpa only [mem_compl_iff, not_not]))
  have h : (E.energy f : ℝ) ≤ (E.energy (f + z) : ℝ) := closure_minimal hsub hclosed hclose
  rw [add_comm f z, sub_add_cancel] at h
  exact NNReal.coe_le_coe.mp h

theorem IsInteriorHarmonic.minimizesWithExterior_wordCells {n : ℕ}
    (S : Finset (Fin n → Fin 8)) (hS : Disjoint (wordCellUnion S) carpetOuterBoundary)
    {f : E.domain} (hf : E.IsInteriorHarmonic f) :
    E.MinimizesWithExterior (wordCellUnion Sᶜ) f := by
  refine IsInteriorHarmonic.minimizesWithExterior E (isClosed_wordCellUnion S)
    (disjoint_left.mp hS) ?_ hf
  intro x hx
  obtain ⟨v, hv⟩ := exists_wordMap_range n x
  have h : v ∉ S := fun hvS ↦ hx (mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hvS, hv⟩⟩)
  exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨Finset.mem_compl.mpr h, hv⟩⟩

end CarpetEnergy.SelfSimilarPEnergy
