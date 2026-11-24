import CarpetNeighborhoodBuffers
import CarpetConnected
import CarpetNeighborhoodMass

/-!
# Uniform finite ball covers of connected carpet neighborhoods
-/

open Filter Function Metric Set

namespace CarpetEnergy

private theorem cell_subset_wordCellUnion {n : ℕ} {S : Finset (Fin n → Fin 8)}
    {v : Fin n → Fin 8} (hv : v ∈ S) :
    range (wordMap (List.ofFn v)) ⊆ wordCellUnion S := by
  intro x hx
  exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, hx⟩⟩

theorem isPreconnected_wordCellUnion_cellNeighborhood {n : ℕ} (w : Fin n → Fin 8) (k : ℕ) :
    IsPreconnected (wordCellUnion (cellNeighborhood w k)) := by
  induction k with
  | zero =>
    have heq : wordCellUnion (cellNeighborhood w 0) = range (wordMap (List.ofFn w)) := by
      ext x
      simp [wordCellUnion, cellNeighborhood]
    rw [heq]
    exact isPreconnected_range (continuous_wordMap _)
  | succ k ih =>
    let U := wordCellUnion (cellNeighborhood w k)
    let I := {v : Fin n → Fin 8 // v ∈ cellNeighborhood w (k + 1)}
    let F (v : I) := U ∪ range (wordMap (List.ofFn v.val))
    have hmono : U ⊆ wordCellUnion (cellNeighborhood w (k + 1)) := by
      intro x hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact cell_subset_wordCellUnion (cellNeighborhood_subset_succ w hv) hxv
    have heq : wordCellUnion (cellNeighborhood w (k + 1)) = ⋃ v, F v := by
      ext x
      constructor
      · intro hx
        obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion.mpr ⟨⟨v, hv⟩, Or.inr hxv⟩
      · intro hx
        obtain ⟨v, hv⟩ := mem_iUnion.mp hx
        exact hv.elim (fun h ↦ hmono h) (fun h ↦ cell_subset_wordCellUnion v.property h)
    rw [heq]
    have hcen : wordMap (List.ofFn w) (bottomPoint 0) ∈ U :=
      cell_subset_wordCellUnion (self_mem_cellNeighborhood w k) (mem_range_self _)
    refine isPreconnected_iUnion ⟨_, mem_iInter.mpr (fun _ ↦ Or.inl hcen)⟩ (fun v ↦ ?_)
    obtain ⟨u, hu, x, hxu, hxv⟩ := mem_cellNeighborhood_succ.mp v.property
    exact IsPreconnected.union' ⟨x, cell_subset_wordCellUnion hu hxu, hxv⟩ ih
      (isPreconnected_range (continuous_wordMap _))

/-- A level neighborhood is covered by a uniformly finite family of
balls whose centers stay in the neighborhood. -/
theorem exists_uniform_wordNeighborhood_ball_cover {t : ℝ} (ht : 0 < t) :
    ∃ L : ℕ, ∀ (n : ℕ) (w : Fin n → Fin 8),
      ∃ z : ({u // u ∈ cellNeighborhood w 2} × (Fin L → Fin 8)) → CarpetPoints,
        (∀ i, z i ∈ wordCellUnion (cellNeighborhood w 2)) ∧
        wordCellUnion (cellNeighborhood w 2) ⊆ ⋃ i, ball (z i) (t * (1 / 3 : ℝ) ^ n) := by
  obtain ⟨L, hL⟩ := (tendsto_wordMap_radius.eventually_lt_const ht).exists
  refine ⟨L, fun n w ↦ ?_⟩
  let z (i : {u // u ∈ cellNeighborhood w 2} × (Fin L → Fin 8)) :=
    wordMap (List.ofFn i.1.val) (wordMap (List.ofFn i.2) (bottomPoint 0))
  refine ⟨z, fun i ↦ cell_subset_wordCellUnion i.1.property (mem_range_self _), ?_⟩
  intro x hx
  obtain ⟨u, hu, y, rfl⟩ := mem_iUnion₂.mp hx
  obtain ⟨v, hv⟩ := exists_wordMap_range L y
  refine mem_iUnion.mpr ⟨(⟨u, hu⟩, v), mem_ball.mpr ?_⟩
  dsimp only [z]
  rw [dist_wordMap, List.length_ofFn]
  have hd := wordMap_dist_le L v hv (mem_range_self (bottomPoint 0))
  calc
    _ ≤ (1 / 3 : ℝ) ^ n * ((1 / 3 : ℝ) ^ L * diam (univ : Set CarpetPoints)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ < (1 / 3 : ℝ) ^ n * t := mul_lt_mul_of_pos_left hL (by positivity)
    _ = _ := mul_comm _ _

end CarpetEnergy
