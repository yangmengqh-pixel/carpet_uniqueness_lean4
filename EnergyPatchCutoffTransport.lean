import EnergyNeighborhoodPasting
import EnergyCompactCutoff

/-!
# Transport of a cutoff between equal-shape neighborhoods
-/

open Filter Function MeasureTheory Set
open scoped BigOperators

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 2300000 in
/-- A cutoff on the smaller neighborhood can be copied into the target
using the shape of the larger neighborhood to check the traces. -/
theorem exists_transported_neighborhood_cutoff {n m k : ℕ}
    (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w (k + 2) = neighborhoodShape u (k + 2))
    (χ : E.continuousCore) (hχ0 : ∀ x ∉ wordNeighborhoodOpen u (k + 1), χ.val x = 0)
    (hχ1 : ∀ x ∈ wordCellUnion (cellNeighborhood u k), χ.val x = 1)
    (hχ01 : ∀ x, χ.val x ∈ Icc (0 : ℝ) 1) :
    ∃ g : E.continuousCore,
      (∀ x ∉ wordCellUnion (cellNeighborhood w (k + 1)), g.val x = 0) ∧
      (∀ x ∈ wordCellUnion (cellNeighborhood w k), g.val x = 1) ∧
      (∀ x, g.val x ∈ Icc (0 : ℝ) 1) ∧
      (∀ a : {a // a ∈ cellNeighborhood w (k + 2)},
        E.wordPullbackCore (List.ofFn a.val) g =
          E.wordPullbackCore (List.ofFn (neighborhoodEquiv w u h a).val) χ) ∧
      (∀ a ∉ cellNeighborhood w (k + 2), E.wordPullbackCore (List.ofFn a) g = 0) := by
  classical
  let A := cellNeighborhood w (k + 2)
  let P (a : Fin n → Fin 8) : E.continuousCore :=
    if ha : a ∈ A then E.wordPullbackCore (List.ofFn (neighborhoodEquiv w u h ⟨a, ha⟩).val) χ
    else 0
  have hP (a : {a // a ∈ A}) (x : CarpetPoints) :
      (P a.val).val x = χ.val (wordMap (List.ofFn (neighborhoodEquiv w u h a).val) x) := by
    dsimp only [P]
    rw [dite_eq_left a.property, E.wordPullbackCore_apply]
  have hzero (a : Fin n → Fin 8) (ha : a ∉ A) : P a = 0 := dite_eq_right ha
  have h0 (a : Fin n → Fin 8) (ha : a ∉ cellNeighborhood w (k + 1)) :
      P a = 0 := by
    by_cases hA : a ∈ A
    · let b := neighborhoodEquiv w u h ⟨a, hA⟩
      have hb : b.val ∉ cellNeighborhood u (k + 1) := by
        intro hb'
        apply ha
        have hh := neighborhoodEquiv_mem_cellNeighborhood u w h.symm (by omega : k + 1 ≤ k + 2) b hb'
        have he : (neighborhoodEquiv u w h.symm b).val = a := by
          have hi : neighborhoodEquiv u w h.symm b = (⟨a, hA⟩ : {a // a ∈ A}) := by
            apply neighborhoodOffset_injective w
            rw [neighborhoodEquiv_offset, neighborhoodEquiv_offset]
          exact congrArg Subtype.val hi
        rwa [he] at hh
      apply Subtype.ext
      ext x
      rw [hP ⟨a, hA⟩ x]
      exact hχ0 _ (wordMap_notMem_wordNeighborhoodOpen hb x)
    · exact hzero a hA
  have hglue (a b : Fin n → Fin 8) (x y : CarpetPoints)
      (he : wordMap (List.ofFn a) x = wordMap (List.ofFn b) y) : (P a).val x = (P b).val y := by
    by_cases ha : a ∈ A
    · by_cases hb : b ∈ A
      · rw [hP ⟨a, ha⟩ x, hP ⟨b, hb⟩ y]
        have hr := congrArg (fun z : CarpetPoints ↦ neighborhoodRescale w u z) he
        rw [neighborhoodRescale_wordMap w u h ⟨a, ha⟩ x,
          neighborhoodRescale_wordMap w u h ⟨b, hb⟩ y] at hr
        exact congrArg χ.val (Subtype.ext hr)
      · have hsmall : a ∉ cellNeighborhood w (k + 1) := by
          intro h
          exact hb (mem_cellNeighborhood_succ.mpr ⟨a, h, wordMap (List.ofFn a) x,
            mem_range_self x, by rw [he]; exact mem_range_self y⟩)
        rw [h0 a hsmall, hzero b hb]
        rfl
    · have hsmall : b ∉ cellNeighborhood w (k + 1) := by
        intro h
        exact ha (mem_cellNeighborhood_succ.mpr ⟨b, h, wordMap (List.ofFn b) y,
          mem_range_self y, by rw [← he]; exact mem_range_self x⟩)
      rw [h0 b hsmall, hzero a ha]
      rfl
  obtain ⟨g, hg, hgP⟩ := E.zeroComponent.exists_continuousKernel_cellwise n
    (fun a ↦ (P a).val) (fun a ↦ ⟨(P a).property, rfl⟩) hglue
  let G : E.continuousCore := ⟨g, hg.choose⟩
  have hG (a : Fin n → Fin 8) : E.wordPullbackCore (List.ofFn a) G = P a := by
    apply Subtype.ext
    ext x
    exact hgP a x
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, y, rfl⟩ := exists_wordMap_range n x
    have ha : a ∉ cellNeighborhood w (k + 1) :=
      fun ha ↦ hx (mem_iUnion₂.mpr ⟨a, ha, mem_range_self y⟩)
    rw [← E.wordPullbackCore_apply, hG, h0 a ha]
    rfl
  · intro x hx
    obtain ⟨a, ha, y, rfl⟩ := mem_iUnion₂.mp hx
    have hA : a ∈ A := cellNeighborhood_mono w (by omega : k ≤ k + 2) ha
    have hb := neighborhoodEquiv_mem_cellNeighborhood w u h (by omega : k ≤ k + 2)
      ⟨a, hA⟩ ha
    rw [← E.wordPullbackCore_apply, hG, hP ⟨a, hA⟩]
    exact hχ1 _ (mem_iUnion₂.mpr ⟨_, hb, mem_range_self y⟩)
  · intro x
    obtain ⟨a, y, rfl⟩ := exists_wordMap_range n x
    rw [← E.wordPullbackCore_apply, hG]
    by_cases ha : a ∈ A
    · rw [hP ⟨a, ha⟩]
      exact hχ01 _
    · rw [hzero a ha]
      exact ⟨le_rfl, zero_le_one⟩
  · intro a
    rw [hG]
    exact dite_eq_left a.property
  · intro a ha
    rw [hG]
    exact hzero a ha

end CarpetEnergy.SelfSimilarPEnergy
