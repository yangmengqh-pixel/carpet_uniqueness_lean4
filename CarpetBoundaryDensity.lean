import CarpetBoundary
import CarpetConnected

/-!
# The exterior sides of word cells determine continuous functions

Each first-level cell has a corner on the exterior of its parent. Constants
on the sides of every word cell therefore agree across levels, and the
small-cell diameter bound then makes the function constant on the carpet.
-/

open Filter Function Metric Set
open scoped Topology unitInterval

namespace CarpetEnergy

private def liesOnExterior (x : CarpetPoints) : Prop :=
  ∃ j a : Fin 2, (x : Plane) j = (a.val : ℝ)

private noncomputable def northWest : CarpetPoints :=
  carpetSymmetry verticalFlip (bottomPoint 0)

private theorem northWest_x : (northWest : Plane) 0 = 0 := rfl

private theorem northWest_y : (northWest : Plane) 1 = 1 := by
  change (carpetSymmetry verticalFlip (bottomPoint 0) : Plane) 1 = 1
  rw [carpetSymmetry_verticalFlip_second]
  change (1 : ℝ) - 0 = 1
  rw [sub_zero]

private theorem bottomPoint_zero_exterior : liesOnExterior (bottomPoint 0) :=
  ⟨0, 0, rfl⟩

private theorem exists_point_on_side (j a : Fin 2) :
    ∃ x : CarpetPoints, (x : Plane) j = (a.val : ℝ) := by
  fin_cases j <;> fin_cases a
  · exact ⟨bottomPoint 0, rfl⟩
  · exact ⟨bottomPoint 1, rfl⟩
  · exact ⟨bottomPoint 0, rfl⟩
  · exact ⟨northWest, northWest_y⟩

private theorem exists_exterior_point_in_cell (i : Fin 8) :
    ∃ x : CarpetPoints, liesOnExterior x ∧ liesOnExterior (cellMap i x) := by
  obtain ⟨j, a, ha⟩ := (by decide :
    ∀ i : Fin 8, ∃ j a : Fin 2, (cellDigit i j : ℕ) = 2 * a.val) i
  obtain ⟨x, hx⟩ := exists_point_on_side j a
  refine ⟨x, ⟨j, a, hx⟩, j, a, ?_⟩
  change cellSimilarity i x j = _
  rw [cellSimilarity_coord, ← cellDigit_cast, hx, ha, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem agree_on_exterior_of_agree_on_sides (f : CarpetPoints → ℝ)
    (h : ∀ (j a : Fin 2) (x y : CarpetPoints),
      (x : Plane) j = (a.val : ℝ) → (y : Plane) j = (a.val : ℝ) → f x = f y)
    {x : CarpetPoints} (hx : liesOnExterior x) :
    f x = f (bottomPoint 0) := by
  obtain ⟨j, a, hx⟩ := hx
  fin_cases j <;> fin_cases a
  · exact h 0 0 x (bottomPoint 0) hx rfl
  · exact (h 0 1 x (bottomPoint 1) hx rfl).trans (h 1 0 (bottomPoint 1) (bottomPoint 0) rfl rfl)
  · exact h 1 0 x (bottomPoint 0) hx rfl
  · exact (h 1 1 x northWest hx northWest_y).trans (h 0 0 northWest (bottomPoint 0) northWest_x rfl)

private theorem wordMap_append_singleton (w : List (Fin 8)) (i : Fin 8) :
    wordMap (w ++ [i]) = wordMap w ∘ cellMap i := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (cellMap a ∘ ·) ih

/-- A continuous function constant on each exterior side after every word
pullback is constant on the carpet. -/
theorem constant_of_constant_on_word_sides (f : C(CarpetPoints, ℝ))
    (h : ∀ (w : List (Fin 8)) (j a : Fin 2) (x y : CarpetPoints),
      (x : Plane) j = (a.val : ℝ) → (y : Plane) j = (a.val : ℝ) →
      f (wordMap w x) = f (wordMap w y)) :
    ∀ x, f x = f (bottomPoint 0) := by
  let o := bottomPoint 0
  have hext (w : List (Fin 8)) (x : CarpetPoints) (hx : liesOnExterior x) :
      f (wordMap w x) = f (wordMap w o) :=
    agree_on_exterior_of_agree_on_sides (f ∘ wordMap w) (h w) hx
  have hw (w : List (Fin 8)) : f (wordMap w o) = f o := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w i ih =>
      obtain ⟨y, hoy, hiy⟩ := exists_exterior_point_in_cell i
      calc
        _ = f (wordMap (w ++ [i]) y) := (hext _ y hoy).symm
        _ = f (wordMap w (cellMap i y)) := by rw [wordMap_append_singleton]; rfl
        _ = f (wordMap w o) := hext _ _ hiy
        _ = _ := ih
  intro x
  have hclosed : IsClosed {y | f y = f o} := isClosed_eq f.continuous continuous_const
  suffices hx : x ∈ closure {y | f y = f o} by rwa [hclosed.closure_eq] at hx
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (tendsto_wordMap_radius.eventually_lt_const hε).exists
  obtain ⟨w, hx⟩ := exists_wordMap_range n x
  exact ⟨wordMap (List.ofFn w) o, hw _, (wordMap_dist_le n w hx (mem_range_self o)).trans_lt hn⟩

end CarpetEnergy
