import EnergyNestedReplacement

/-!
# Zero-trace extension into a word cell

A continuous domain function vanishing on the exterior sides can be
inserted into a word cell and extended by zero. Its other cell pullbacks
vanish, and its trace stays zero on the level boundary.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Inserting a zero-trace continuous function into one cell. -/
theorem exists_zeroTrace_extension (n : ℕ) (w : Fin n → Fin 8)
    (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain)
    (hz : ∀ x ∈ carpetOuterBoundary, u x = 0) :
    ∃ (v : C(CarpetPoints, ℝ)) (_hv : continuousLp p v ∈ E.domain),
      (∀ x ∈ carpetCellBoundary n, v x = 0) ∧
      (∀ x, v (wordMap (List.ofFn w) x) = u x) ∧
      ∀ a : Fin n → Fin 8, a ≠ w → ∀ x, v (wordMap (List.ofFn a) x) = 0 := by
  classical
  let Q := E.zeroComponent
  let G (a : Fin n → Fin 8) := if a = w then u else ContinuousMap.const CarpetPoints (0 : ℝ)
  have hG (a : Fin n → Fin 8) : G a ∈ Q.continuousKernel := by
    by_cases h : a = w
    · rw [show G a = u from ite_eq_left h]
      exact ⟨hu, rfl⟩
    · rw [show G a = ContinuousMap.const CarpetPoints 0 from ite_eq_right h]
      exact Q.continuousKernel_const 0
  have hzero (a b : Fin n → Fin 8) (hab : a ≠ b) (x y : CarpetPoints)
      (he : wordMap (List.ofFn a) x = wordMap (List.ofFn b) y) : u x = 0 := by
    have hl : (List.ofFn a).length = (List.ofFn b).length := by simp
    have hd : ∃ i, gridCoordinate (List.ofFn a) i ≠ gridCoordinate (List.ofFn b) i := by
      by_contra! h
      exact hab (List.ofFn_injective (gridCoordinate_injective_of_length hl h))
    obtain ⟨i, hi⟩ := hd
    have hc := (wordMap_eq_iff_grid_coordinate hl x y).mp he i
    obtain ⟨j, _, hj, _, _⟩ := overlap_coord_endpoints
      (carpet_coord_mem_Icc x i) (carpet_coord_mem_Icc y i) hc hi
    exact hz x ((mem_carpetOuterBoundary x).mpr ⟨i, j, hj⟩)
  have heq (a b : Fin n → Fin 8) (x y : CarpetPoints)
      (he : wordMap (List.ofFn a) x = wordMap (List.ofFn b) y) : G a x = G b y := by
    by_cases h : a = b
    · subst b
      rw [(measurableEmbedding_wordMap (List.ofFn a)).injective he]
    by_cases ha : a = w
    · have hb : b ≠ w := fun hb ↦ h (ha.trans hb.symm)
      rw [show G a = u from ite_eq_left ha,
        show G b = ContinuousMap.const CarpetPoints 0 from ite_eq_right hb]
      exact hzero a b h x y he
    · rw [show G a = ContinuousMap.const CarpetPoints 0 from ite_eq_right ha]
      by_cases hb : b = w
      · rw [show G b = u from ite_eq_left hb]
        exact (hzero b a (Ne.symm h) y x he.symm).symm
      · rw [show G b = ContinuousMap.const CarpetPoints 0 from ite_eq_right hb]
        rfl
  obtain ⟨v, ⟨hv, _⟩, h⟩ := Q.exists_continuousKernel_cellwise n G hG heq
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, y, hy, rfl⟩ := mem_iUnion.mp hx
    rw [h]
    by_cases ha : a = w
    · rw [show G a = u from ite_eq_left ha]
      exact hz y hy
    · rw [show G a = ContinuousMap.const CarpetPoints 0 from ite_eq_right ha]
      rfl
  · intro x
    rw [h, show G w = u from ite_eq_left rfl]
  · intro a ha x
    rw [h, show G a = ContinuousMap.const CarpetPoints 0 from ite_eq_right ha]
    rfl

end CarpetEnergy.SelfSimilarPEnergy
