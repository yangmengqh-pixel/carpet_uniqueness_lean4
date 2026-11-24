import CarpetCellNeighborhoods
import CarpetCellBoundaries

/-!
# Cell-neighborhood mass budgets

Level boundaries are null for the measures in the blowup argument.
Finite cell unions are therefore additive, and bounded overlap of
neighborhoods controls the mass of cells with poor local mass ratios.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy

/-- The union of a finite family of cells at one level. -/
noncomputable def wordCellUnion {n : ℕ} (A : Finset (Fin n → Fin 8)) : Set CarpetPoints :=
  ⋃ w ∈ A, range (wordMap (List.ofFn w))

theorem wordCellUnion_univ (n : ℕ) :
    wordCellUnion (Finset.univ : Finset (Fin n → Fin 8)) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨w, hw⟩ := exists_wordMap_range n x
  exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨Finset.mem_univ _, hw⟩⟩

theorem measurableSet_wordCellUnion {n : ℕ} (A : Finset (Fin n → Fin 8)) :
    MeasurableSet (wordCellUnion A) := by
  apply MeasurableSet.biUnion A.countable_toSet
  intro w _
  exact (measurableEmbedding_wordMap _).measurableSet_range

/-- Same-level unions are additive after intersecting with a Borel set. -/
theorem measure_wordCellUnion_inter {n : ℕ} (ν : Measure CarpetPoints)
    (hν : ν (carpetCellBoundary n) = 0) (A : Finset (Fin n → Fin 8))
    {B : Set CarpetPoints} (hB : MeasurableSet B) :
    ν (wordCellUnion A ∩ B) = ∑ w ∈ A, ν (range (wordMap (List.ofFn w)) ∩ B) := by
  let C (w : Fin n → Fin 8) := range (wordMap (List.ofFn w)) ∩ B
  have he : wordCellUnion A ∩ B = ⋃ w ∈ A, C w := by
    unfold wordCellUnion
    simp only [iUnion_inter, C]
  rw [he]
  apply measure_biUnion_finset₀
  · intro w _ v _ hne
    apply measure_mono_null (μ := ν) _ hν
    exact fun x hx ↦ inter_word_subset_cellBoundary hne ⟨hx.1.1, hx.2.1⟩
  · intro w _
    exact ((measurableEmbedding_wordMap _).measurableSet_range.inter hB).nullMeasurableSet

theorem measure_wordCellUnion {n : ℕ} (ν : Measure CarpetPoints)
    (hν : ν (carpetCellBoundary n) = 0) (A : Finset (Fin n → Fin 8)) :
    ν (wordCellUnion A) = ∑ w ∈ A, ν (range (wordMap (List.ofFn w))) := by
  simpa only [inter_univ] using measure_wordCellUnion_inter ν hν A MeasurableSet.univ

/-- The total mass of all radius-k neighborhoods is bounded by their
uniform overlap count times the total mass. -/
theorem sum_measure_cellNeighborhood_le {n : ℕ} (ν : Measure CarpetPoints)
    (hν : ν (carpetCellBoundary n) = 0) (k : ℕ) :
    (∑ w : Fin n → Fin 8, ν (wordCellUnion (cellNeighborhood w k))) ≤
      (((2 * k + 1) ^ 2 : ℕ) : ℝ≥0∞) * ν univ := by
  classical
  let e (w : Fin n → Fin 8) := ν (range (wordMap (List.ofFn w)))
  have hsum : (∑ w : Fin n → Fin 8, e w) = ν univ := by
    rw [← wordCellUnion_univ n, measure_wordCellUnion ν hν]
  have hswap : (∑ w : Fin n → Fin 8, ∑ v ∈ cellNeighborhood w k, e v) =
      ∑ v : Fin n → Fin 8, ((cellNeighborhood v k).card : ℝ≥0∞) * e v := by
    calc
      _ = ∑ w : Fin n → Fin 8, ∑ v : Fin n → Fin 8, if v ∈ cellNeighborhood w k then e v else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        rw [← Finset.sum_filter]
        have he : Finset.univ.filter (fun v ↦ v ∈ cellNeighborhood w k) = cellNeighborhood w k := by
          ext v
          simp
        rw [he]
      _ = ∑ v : Fin n → Fin 8, ∑ w : Fin n → Fin 8, if v ∈ cellNeighborhood w k then e v else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        have hs (w : Fin n → Fin 8) : v ∈ cellNeighborhood w k ↔ w ∈ cellNeighborhood v k :=
          ⟨mem_cellNeighborhood_symm, mem_cellNeighborhood_symm⟩
        simp only [hs]
        rw [← Finset.sum_filter]
        have he : Finset.univ.filter (fun w ↦ w ∈ cellNeighborhood v k) = cellNeighborhood v k := by
          ext w
          simp
        rw [he, Finset.sum_const, nsmul_eq_mul]
  simp_rw [measure_wordCellUnion ν hν]
  rw [hswap, ← hsum, Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ ↦ mul_le_mul' (by exact_mod_cast card_cellNeighborhood_le v k) le_rfl

/-- The union of cells whose own mass is a small fraction of their
neighborhood mass has proportionately small total mass. -/
theorem measure_bad_cell_ratio_le {n : ℕ} (ν : Measure CarpetPoints)
    (hν : ν (carpetCellBoundary n) = 0) (k : ℕ) (a : ℝ≥0∞) :
    ν (wordCellUnion (Finset.univ.filter (fun w : Fin n → Fin 8 ↦
      ν (range (wordMap (List.ofFn w))) < a * ν (wordCellUnion (cellNeighborhood w k))))) ≤
      a * ((((2 * k + 1) ^ 2 : ℕ) : ℝ≥0∞) * ν univ) := by
  classical
  let A := Finset.univ.filter (fun w : Fin n → Fin 8 ↦
    ν (range (wordMap (List.ofFn w))) < a * ν (wordCellUnion (cellNeighborhood w k)))
  change ν (wordCellUnion A) ≤ _
  rw [measure_wordCellUnion ν hν]
  calc
    _ ≤ ∑ w ∈ A, a * ν (wordCellUnion (cellNeighborhood w k)) :=
      Finset.sum_le_sum fun w hw ↦ (Finset.mem_filter.mp hw).2.le
    _ ≤ ∑ w : Fin n → Fin 8, a * ν (wordCellUnion (cellNeighborhood w k)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ bot_le)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul' le_rfl (sum_measure_cellNeighborhood_le ν hν k)

end CarpetEnergy
