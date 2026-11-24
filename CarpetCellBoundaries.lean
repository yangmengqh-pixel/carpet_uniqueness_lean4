import CarpetCorners
import CarpetDensity
import EnergyPointwiseComparison

/-!
# The cell boundary sets

The outer square boundary and its images under all finite words give the
boundary sets in (4.4). Nullity of the outer boundary for every energy
measure propagates to all word images by self-similarity.
-/

open Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

/-- The intersection of the carpet with the four outer sides. -/
def carpetOuterBoundary : Set CarpetPoints :=
  ⋃ j : Fin 2, ⋃ a : Fin 2, {x | (x : Plane) j = (a.val : ℝ)}

theorem mem_carpetOuterBoundary (x : CarpetPoints) :
    x ∈ carpetOuterBoundary ↔ ∃ j a : Fin 2, (x : Plane) j = (a.val : ℝ) := by
  simp [carpetOuterBoundary]

theorem measurableSet_carpetOuterBoundary : MeasurableSet carpetOuterBoundary := by
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro a
  exact measurableSet_eq_fun
    (((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) j).comp continuous_subtypeVal).measurable)
    measurable_const

/-- The union of the Euclidean boundaries of all level-`n` cells, restricted to the carpet cells. -/
noncomputable def carpetCellBoundary (n : ℕ) : Set CarpetPoints :=
  ⋃ w : Fin n → Fin 8, wordMap (List.ofFn w) '' carpetOuterBoundary

/-- The countable union of the cell boundaries at all levels. -/
noncomputable def carpetAllCellBoundaries : Set CarpetPoints := ⋃ n : ℕ, carpetCellBoundary n

theorem measurableSet_carpetCellBoundary (n : ℕ) : MeasurableSet (carpetCellBoundary n) :=
  MeasurableSet.iUnion fun w ↦
    (measurableEmbedding_wordMap (List.ofFn w)).measurableSet_image.mpr measurableSet_carpetOuterBoundary

theorem measurableSet_carpetAllCellBoundaries : MeasurableSet carpetAllCellBoundaries :=
  MeasurableSet.iUnion measurableSet_carpetCellBoundary

theorem word_preimage_image_outerBoundary_subset {w v : List (Fin 8)}
    (hl : w.length = v.length) :
    wordMap v ⁻¹' (wordMap w '' carpetOuterBoundary) ⊆ carpetOuterBoundary := by
  rintro y ⟨x, hx, he⟩
  obtain ⟨j, a, hxa⟩ := (mem_carpetOuterBoundary x).mp hx
  have hg := (wordMap_eq_iff_grid_coordinate hl x y).mp he j
  by_cases h : gridCoordinate w j = gridCoordinate v j
  · rw [h] at hg
    exact (mem_carpetOuterBoundary y).mpr ⟨j, a, (add_left_cancel hg).symm.trans hxa⟩
  · obtain ⟨_, b, _, hb, _⟩ := overlap_coord_endpoints
      (carpet_coord_mem_Icc x j) (carpet_coord_mem_Icc y j) hg h
    exact (mem_carpetOuterBoundary y).mpr ⟨j, b, hb⟩

theorem inter_word_subset_cellBoundary {n : ℕ} {w v : Fin n → Fin 8} (h : w ≠ v) :
    range (wordMap (List.ofFn w)) ∩ range (wordMap (List.ofFn v)) ⊆ carpetCellBoundary n := by
  rintro _ ⟨⟨x, rfl⟩, ⟨y, he⟩⟩
  have hl : (List.ofFn w).length = (List.ofFn v).length := by simp
  have hne : List.ofFn w ≠ List.ofFn v := fun hh ↦ h (List.ofFn_injective hh)
  have hd : ∃ j, gridCoordinate (List.ofFn w) j ≠ gridCoordinate (List.ofFn v) j := by
    by_contra! h
    exact hne (gridCoordinate_injective_of_length hl h)
  obtain ⟨j, hj⟩ := hd
  have hcoords := (wordMap_eq_iff_grid_coordinate hl x y).mp he.symm j
  obtain ⟨a, _, ha, _, _⟩ := overlap_coord_endpoints
    (carpet_coord_mem_Icc x j) (carpet_coord_mem_Icc y j) hcoords hj
  exact mem_iUnion.mpr ⟨w, x, (mem_carpetOuterBoundary x).mpr ⟨j, a, ha⟩, rfl⟩

theorem carpetOuterBoundary_subset_cellBoundary (n : ℕ) :
    carpetOuterBoundary ⊆ carpetCellBoundary n := by
  intro x hx
  obtain ⟨j, a, ha⟩ := (mem_carpetOuterBoundary x).mp hx
  obtain ⟨w, y, rfl⟩ := exists_wordMap_range n x
  have hy := carpet_coord_mem_Icc y j
  have h := wordMap_scaled_coord (List.ofFn w) y j
  let k := gridCoordinate (List.ofFn w) j
  rw [ha] at h
  change (3 : ℝ) ^ (List.ofFn w).length * (a.val : ℝ) = (k : ℝ) + (y : Plane) j at h
  have hside : (y : Plane) j = 0 ∨ (y : Plane) j = 1 := by
    fin_cases a
    · norm_num at h
      have hk₀ : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      exact Or.inl (by linarith [hy.1])
    · norm_num at h
      have hk₁ : (k : ℝ) + 1 ≤ (3 : ℝ) ^ (List.ofFn w).length := by
        have hkNat : k + 1 ≤ 3 ^ (List.ofFn w).length := gridCoordinate_lt _ _
        exact_mod_cast hkNat
      rw [List.length_ofFn] at hk₁
      exact Or.inr (by linarith [hy.2])
  refine mem_iUnion.mpr ⟨w, y, (mem_carpetOuterBoundary y).mpr ?_, rfl⟩
  rcases hside with h₀ | h₁
  · exact ⟨j, 0, h₀⟩
  · exact ⟨j, 1, h₁⟩

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Null outer boundary gives null boundaries at all levels. -/
theorem energyMeasure_carpetCellBoundary_eq_zero
    (h : ∀ f : E.domain, E.energyMeasure f carpetOuterBoundary = 0)
    (f : E.domain) (n : ℕ) :
    E.energyMeasure f (carpetCellBoundary n) = 0 := by
  apply measure_iUnion_null
  intro w
  let A := wordMap (List.ofFn w) '' carpetOuterBoundary
  have hA : MeasurableSet A :=
    (measurableEmbedding_wordMap (List.ofFn w)).measurableSet_image.mpr measurableSet_carpetOuterBoundary
  rw [E.energyMeasure_eq_sum_words n f, Measure.sum_apply _ hA]
  apply tsum_eq_zero_iff.mpr
  intro v
  rw [smul_apply, smul_eq_mul,
    Measure.map_apply (measurableEmbedding_wordMap (List.ofFn v)).measurable hA]
  rw [measure_mono_null (word_preimage_image_outerBoundary_subset (by simp))
    (h (E.pullbackWord (List.ofFn v) f)), mul_zero]

theorem energyMeasure_carpetAllCellBoundaries_eq_zero
    (h : ∀ f : E.domain, E.energyMeasure f carpetOuterBoundary = 0)
    (f : E.domain) :
    E.energyMeasure f carpetAllCellBoundaries = 0 :=
  measure_iUnion_null (E.energyMeasure_carpetCellBoundary_eq_zero h f)

theorem energyReferenceMeasure_carpetAllCellBoundaries_eq_zero
    (h : ∀ f : E.domain, E.energyMeasure f carpetOuterBoundary = 0)
    (d : ℕ → E.domain) :
    E.energyReferenceMeasure d carpetAllCellBoundaries = 0 := by
  rw [energyReferenceMeasure, Measure.sum_apply _ measurableSet_carpetAllCellBoundaries]
  apply tsum_eq_zero_iff.mpr
  intro n
  rw [smul_apply, smul_eq_mul, E.energyMeasure_carpetAllCellBoundaries_eq_zero h, mul_zero]

/-- Nullity of the entire family of boundaries transfers to every comparable energy. -/
theorem energyMeasure_carpetAllCellBoundaries_eq_zero_of_comparison
    (D : SelfSimilarPEnergy p)
    (h : ∀ f : E.domain, E.energyMeasure f carpetOuterBoundary = 0)
    (g : D.domain) :
    D.energyMeasure g carpetAllCellBoundaries = 0 := by
  obtain ⟨hDE, C, _, hC⟩ := D.exists_energyMeasure_comparison E
  have hle := (hC g).1 carpetAllCellBoundaries
  rw [smul_apply, smul_eq_mul, E.energyMeasure_carpetAllCellBoundaries_eq_zero h, mul_zero] at hle
  exact nonpos_iff_eq_zero.mp hle

end SelfSimilarPEnergy
end CarpetEnergy
