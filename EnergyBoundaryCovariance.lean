import EnergyBoundaryNullity
import EnergyComponentDominance

/-!
# Word-cell covariance and invariant restrictions

Boundary nullity gives the full word-cell formula for every self-similar
p-energy. Invariance then gives the same formula for restricted measures.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Distinct first-level cells have zero common energy mass. -/
theorem energyMeasure_inter_cellMap_eq_zero (f : E.domain) {i j : Fin 8} (h : i ≠ j) :
    E.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0 := by
  let w : Fin 1 → Fin 8 := fun _ ↦ i
  let v : Fin 1 → Fin 8 := fun _ ↦ j
  have hne : w ≠ v := fun h' ↦ h (congrFun h' 0)
  have hs := inter_word_subset_cellBoundary hne
  have hn := E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero f 1
  exact measure_mono_null (by simpa only [w, v, List.ofFn_succ, List.ofFn_zero,
    wordMap, comp_id] using hs) hn

/-- Lemma 7.2(2), with nullity supplied by the boundary theorem. -/
theorem energyMeasure_image_word (f : E.domain) (w : List (Fin 8)) (A : Set CarpetPoints) :
    E.energyMeasure f (wordMap w '' A) =
      ENNReal.ofReal E.scalingFactor ^ w.length * E.energyMeasure (E.pullbackWord w f) A :=
  E.energyMeasure_image_word_of_null_intersections E.energyMeasure_inter_cellMap_eq_zero f w A

theorem energyMeasure_restrict_word (f : E.domain) (w : List (Fin 8)) :
    (E.energyMeasure f).restrict (range (wordMap w)) =
      (ENNReal.ofReal E.scalingFactor ^ w.length) •
        (E.energyMeasure (E.pullbackWord w f)).map (wordMap w) :=
  E.energyMeasure_restrict_word_of_null_intersections E.energyMeasure_inter_cellMap_eq_zero f w

/-- Lemma 7.2(1), the energy mass of a word cell. -/
theorem energyMeasure_range_word (f : E.domain) (w : List (Fin 8)) :
    E.energyMeasure f (range (wordMap w)) =
      ENNReal.ofReal E.scalingFactor ^ w.length * (E.energy (E.pullbackWord w f) : ℝ≥0∞) := by
  rw [← image_univ, E.energyMeasure_image_word, E.energyMeasure_univ]

theorem energyReferenceMeasure_allCellBoundaries_eq_zero (d : ℕ → E.domain) :
    E.energyReferenceMeasure d carpetAllCellBoundaries = 0 :=
  E.energyReferenceMeasure_carpetAllCellBoundaries_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero d

/-- Invariance under the first-level cells implies invariance under all words. -/
theorem ae_mem_word_of_ae_mem_cell
    (d : ℕ → E.domain)
    (hd : ∀ n, ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (d n : CarpetLp p))
    (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0))
    {A : Set CarpetPoints} (hcell : ∀ i, ∀ᵐ x ∂E.energyReferenceMeasure d, cellMap i x ∈ A ↔ x ∈ A)
    (w : List (Fin 8)) : ∀ᵐ x ∂E.energyReferenceMeasure d, wordMap w x ∈ A ↔ x ∈ A := by
  induction w with
  | nil => exact Eventually.of_forall (fun _ ↦ Iff.rfl)
  | cons i w ih =>
    have h := E.quasiMeasurePreserving_wordMap_energyReference d hd hdense w
    filter_upwards [h.ae (hcell i), ih] with x hx hw
    exact hx.trans hw

/-- Lemma 6.7(a), the invariant restriction formula. -/
theorem energyMeasure_inter_image_word_of_invariant
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (A : Set CarpetPoints) (w : List (Fin 8))
    (hinv : ∀ᵐ x ∂μ, wordMap w x ∈ A ↔ x ∈ A)
    (f : E.domain) (B : Set CarpetPoints) :
    E.energyMeasure f (A ∩ wordMap w '' B) =
      ENNReal.ofReal E.scalingFactor ^ w.length * E.energyMeasure (E.pullbackWord w f) (A ∩ B) := by
  rw [← image_preimage_inter, E.energyMeasure_image_word]
  congr 1
  have h : (wordMap w ⁻¹' A : Set CarpetPoints) =ᵐ[E.energyMeasure (E.pullbackWord w f)] A :=
    hinv.filter_mono ((hdom (E.pullbackWord w f)).ae_le)
  exact measure_congr (h.inter Filter.EventuallyEqSet.rfl)

theorem componentOfInvariantSet_add_compl
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (A : Set CarpetPoints) (hA : MeasurableSet A)
    (hcell : ∀ i, ∀ᵐ x ∂μ, cellMap i x ∈ A ↔ x ∈ A)
    (hsym : ∀ σ, ∀ᵐ x ∂μ, carpetSymmetry σ x ∈ A ↔ x ∈ A)
    (f : E.domain) :
    (E.componentOfInvariantSet hdom A hA hcell hsym).mass f +
    (E.componentOfInvariantSet hdom Aᶜ hA.compl
      (fun i ↦ (hcell i).mono fun _ h ↦ not_congr h)
      (fun σ ↦ (hsym σ).mono fun _ h ↦ not_congr h)).mass f = E.energy f := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_add, E.componentOfInvariantSet_mass, E.componentOfInvariantSet_mass,
    measure_add_measure_compl hA, E.energyMeasure_univ]

end CarpetEnergy.SelfSimilarPEnergy
