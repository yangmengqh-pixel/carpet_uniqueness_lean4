import EnergyPiecewiseHarmonic
import CarpetNeighborhoodMass

/-!
# Positive invariant mass on an interior-harmonic function

Graph density preserves a strictly positive restricted energy mass.
The cell covariance then transfers a positive summand to one interior
harmonic pullback.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A positive invariant set for a minimal energy-dominant measure
has positive energy mass for an interior harmonic function. -/
theorem exists_interiorHarmonic_pos_mass
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (hmin : ∀ ν : Measure CarpetPoints, (∀ f, E.energyMeasure f ≪ ν) → μ ≪ ν)
    (A : Set CarpetPoints) (hA : MeasurableSet A) (hpos : 0 < μ A)
    (hcell : ∀ i, ∀ᵐ x ∂μ, cellMap i x ∈ A ↔ x ∈ A) :
    ∃ h : E.domain, E.IsInteriorHarmonic h ∧ 0 < E.energyMeasure h A := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hnot : ¬ ∀ f : E.domain, E.energyMeasure f A = 0 := by
    intro h
    exact hpos.ne' ((E.null_iff_forall_energyMeasure_null hdom hmin hA).mpr h)
  obtain ⟨f, hf⟩ := not_forall.mp hnot
  let Q := E.energyMeasureSeminorm A hA
  have hQf : 0 < Q f := by
    rw [E.energyMeasureSeminorm_apply A hA f, Measure.real]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hf (measure_ne_top _ _)) _
  obtain ⟨n, g, hg, hnear⟩ := E.exists_piecewiseHarmonic_graph_approximation f (Q f / 2)
    (half_pos hQf)
  have hdiff : Q (g - f) ≤ E.graphSeminorm (g - f) :=
    (E.energyMeasureSeminorm_le_rootSeminorm A hA _).trans (E.rootSeminorm_le_graphSeminorm _)
  have htri := map_add_le_add Q (f - g) g
  rw [sub_add_cancel, ← neg_sub g f, map_neg_eq_map] at htri
  have hQg : 0 < Q g := by linarith
  have hΓ : 0 < E.energyMeasure g A := by
    by_contra! hn
    have hz : E.energyMeasure g A = 0 := nonpos_iff_eq_zero.mp hn
    rw [E.energyMeasureSeminorm_apply A hA g, Measure.real, hz, ENNReal.toReal_zero,
      Real.zero_rpow (inv_ne_zero hp.ne')] at hQg
    exact (lt_irrefl _ hQg)
  have hmass : E.energyMeasure g A =
      ∑ w : Fin n → Fin 8, E.energyMeasure g (range (wordMap (List.ofFn w)) ∩ A) := by
    have h := measure_wordCellUnion_inter (E.energyMeasure g)
      (E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero g n)
      (Finset.univ : Finset (Fin n → Fin 8)) hA
    rwa [wordCellUnion_univ, univ_inter] at h
  have hex : ∃ w : Fin n → Fin 8, E.energyMeasure g (range (wordMap (List.ofFn w)) ∩ A) ≠ 0 := by
    by_contra! h
    have hz : (∑ w : Fin n → Fin 8, E.energyMeasure g (range (wordMap (List.ofFn w)) ∩ A)) = 0 :=
      Finset.sum_eq_zero (fun w _ ↦ h w)
    exact hΓ.ne' (hmass.trans hz)
  obtain ⟨w, hw⟩ := hex
  obtain ⟨d, hdc, hdd⟩ := E.exists_energyDense_continuous_sequence
  let ν := E.energyReferenceMeasure d
  have hνμ : ν ≪ μ := E.energyReferenceMeasure_absolutelyContinuous d μ hdom
  have hμν : μ ≪ ν := hmin ν (E.energyMeasure_absolutelyContinuous_reference d hdd)
  have hi : ∀ᵐ x ∂μ, wordMap (List.ofFn w) x ∈ A ↔ x ∈ A :=
    (E.ae_mem_word_of_ae_mem_cell d hdc hdd
      (fun i ↦ (hcell i).filter_mono hνμ.ae_le) (List.ofFn w)).filter_mono hμν.ae_le
  have hm := E.energyMeasure_inter_image_word_of_invariant hdom A (List.ofFn w) hi g univ
  rw [image_univ, inter_univ, inter_comm A] at hm
  refine ⟨E.pullbackWord (List.ofFn w) g, hg w, pos_iff_ne_zero.mpr ?_⟩
  intro h
  rw [h, mul_zero] at hm
  exact hw hm

end CarpetEnergy.SelfSimilarPEnergy
