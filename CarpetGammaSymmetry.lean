import CarpetGammaHomogeneity
import EnergySymmetry

/-!
# Square symmetry of the discrete and limiting energies
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- The action of a square symmetry on the ambient carpet Lp space. -/
noncomputable def carpetSymmetryLp (σ : SquareSymmetry) :
    CarpetLp p →ₗᵢ[ℝ] CarpetLp p :=
  Lp.compMeasurePreservingₗᵢ ℝ (carpetSymmetry σ) (measurePreserving_carpetSymmetry σ)

theorem carpetSymmetryLp_ae (σ : SquareSymmetry) (f : CarpetLp p) :
    ((carpetSymmetryLp σ f : CarpetLp p) : CarpetPoints → ℝ) =ᵐ[carpetMeasure]
      f ∘ carpetSymmetry σ :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_carpetSymmetry σ)

private theorem carpetSymmetryLp_inverse (σ : SquareSymmetry) (f : CarpetLp p) :
    carpetSymmetryLp (inverseSymmetry σ) (carpetSymmetryLp σ f) = f := by
  apply Lp.ext
  have h := (measurePreserving_carpetSymmetry (inverseSymmetry σ)).quasiMeasurePreserving
  filter_upwards [carpetSymmetryLp_ae (inverseSymmetry σ) (carpetSymmetryLp σ f),
    h.ae_eq_comp (carpetSymmetryLp_ae σ f)] with x hx hy
  exact hx.trans (hy.trans (congrArg f (carpetSymmetry_rightInverse σ x)))

private theorem ambientWordMean_carpetSymmetryLp (σ : SquareSymmetry) (e : Equiv.Perm (Fin 8))
    (h : ∀ i, carpetSymmetry σ ∘ cellMap i = cellMap (e i) ∘ carpetSymmetry σ)
    (w : List (Fin 8)) (f : CarpetLp p) :
    ambientWordMean p w (carpetSymmetryLp σ f) = ambientWordMean p (w.map e) f := by
  rw [ambientWordMean_eq_integral, ambientWordMean_eq_integral]
  rw [integral_congr_ae ((carpetSymmetryLp_ae σ f).filter_mono (SelfSimilarPEnergy.quasiMeasurePreserving_wordMap w).absolutelyContinuous.ae_le),
    (measurableEmbedding_wordMap w).integral_map, (measurableEmbedding_wordMap (w.map e)).integral_map]
  simp only [Function.comp_apply, wordMap_symmetry σ e h]
  have hσ := ((continuous_carpetSymmetry σ).isClosedEmbedding
    (bijective_carpetSymmetry σ).1).measurableEmbedding
  exact (measurePreserving_carpetSymmetry σ).integral_comp hσ (f ∘ wordMap (w.map e))

private theorem image_range_wordMap_carpetSymmetry (σ : SquareSymmetry) (e : Equiv.Perm (Fin 8))
    (h : ∀ i, carpetSymmetry σ ∘ cellMap i = cellMap (e i) ∘ carpetSymmetry σ)
    (w : List (Fin 8)) :
    carpetSymmetry σ '' range (wordMap w) = range (wordMap (w.map e)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨carpetSymmetry σ y, (wordMap_symmetry σ e h w y).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (bijective_carpetSymmetry σ).2 y
    exact ⟨wordMap w z, mem_range_self z, wordMap_symmetry σ e h w z⟩

theorem discreteCellEnergy_carpetSymmetryLp {ρ : ℝ} (n : ℕ) (σ : SquareSymmetry)
    (f : CarpetLp p) :
    discreteCellEnergy p ρ n (carpetSymmetryLp σ f) = discreteCellEnergy p ρ n f := by
  classical
  obtain ⟨e, he⟩ := exists_carpetSymmetry_cellPerm σ
  let P : Equiv.Perm (Fin n → Fin 8) := Equiv.piCongrRight (fun _ ↦ e)
  have hp (w : Fin n → Fin 8) : (List.ofFn w).map e = List.ofFn (P w) := by
    rw [List.map_ofFn]
    rfl
  have hm (w : Fin n → Fin 8) :
      ambientWordMean p (List.ofFn w) (carpetSymmetryLp σ f) =
        ambientWordMean p (List.ofFn (P w)) f := by
    rw [← hp]
    exact ambientWordMean_carpetSymmetryLp σ e he _ _
  have hI (w v : Fin n → Fin 8) :
      (range (wordMap (List.ofFn w)) ∩ range (wordMap (List.ofFn v))).Nonempty ↔
        (range (wordMap (List.ofFn (P w))) ∩ range (wordMap (List.ofFn (P v)))).Nonempty := by
    have hmap (a : Fin n → Fin 8) :
        carpetSymmetry σ '' range (wordMap (List.ofFn a)) = range (wordMap (List.ofFn (P a))) := by
      rw [← hp]
      exact image_range_wordMap_carpetSymmetry σ e he _
    rw [← hmap w, ← hmap v, ← image_inter (bijective_carpetSymmetry σ).1]
    exact image_nonempty.symm
  unfold discreteCellEnergy
  congr 2
  simp only [Finset.sum_filter, hm]
  apply Fintype.sum_equiv P
  intro w
  apply Fintype.sum_equiv P
  intro v
  have hne : v ≠ w ↔ P v ≠ P w := P.injective.ne_iff.symm
  let A := v ≠ w ∧ (range (wordMap (List.ofFn w)) ∩ range (wordMap (List.ofFn v))).Nonempty
  let B := P v ≠ P w ∧ (range (wordMap (List.ofFn (P w))) ∩ range (wordMap (List.ofFn (P v)))).Nonempty
  have hequiv : A ↔ B := and_congr hne (hI w v)
  by_cases hA : A
  · have hB : B := hequiv.mp hA
    rw [ite_eq_left hA, ite_eq_left hB]
  · have hB : ¬B := fun hB ↦ hA (hequiv.mpr hB)
    rw [ite_eq_right hA, ite_eq_right hB]

theorem IsGammaLimit.discreteCellEnergy_carpetSymmetryLp {ρ : ℝ}
    {j : ℕ → ℕ} {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p ρ (j n)) F)
    (σ : SquareSymmetry) (f : CarpetLp p) : F (carpetSymmetryLp σ f) = F f := by
  have hle (τ : SquareSymmetry) (u : CarpetLp p) : F (carpetSymmetryLp τ u) ≤ F u :=
    hF.apply_le_of_apply_le (carpetSymmetryLp τ).isometry.continuous
      (fun n x ↦ (CarpetEnergy.discreteCellEnergy_carpetSymmetryLp (ρ := ρ) (j n) τ x).le) u
  exact le_antisymm (hle σ f)
    (by simpa only [carpetSymmetryLp_inverse] using hle (inverseSymmetry σ) (carpetSymmetryLp σ f))

end CarpetEnergy
