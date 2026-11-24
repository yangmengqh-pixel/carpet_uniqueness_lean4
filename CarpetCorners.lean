import CarpetBoundary
import CarpetGrid

/-!
# Corners and overlap coordinates

At a fixed cell level, two local points coincide in the carpet exactly
when the sum of each local coordinate and its grid index agrees.
-/

open Set
open scoped unitInterval

namespace CarpetEnergy

private def cornerParameter (i : Fin 2) : I :=
  ⟨(i.val : ℝ), ⟨by positivity, by exact_mod_cast Nat.le_of_lt_succ i.isLt⟩⟩

/-- The corner of the carpet with coordinates i and j. -/
noncomputable def cornerPoint (i j : Fin 2) : CarpetPoints :=
  if j = 0 then bottomPoint (cornerParameter i)
  else carpetSymmetry verticalFlip (bottomPoint (cornerParameter i))

theorem cornerPoint_first (i j : Fin 2) : (cornerPoint i j : Plane) 0 = (i.val : ℝ) := by
  fin_cases j <;> rfl

theorem cornerPoint_second (i j : Fin 2) : (cornerPoint i j : Plane) 1 = (j.val : ℝ) := by
  fin_cases j
  · rfl
  · change (carpetSymmetry verticalFlip (bottomPoint (cornerParameter i)) : Plane) 1 = 1
    rw [carpetSymmetry_verticalFlip_second]
    change (1 : ℝ) - 0 = 1
    rw [sub_zero]

theorem eq_cornerPoint_of_coords {x : CarpetPoints} {i j : Fin 2}
    (hi : (x : Plane) 0 = (i.val : ℝ)) (hj : (x : Plane) 1 = (j.val : ℝ)) :
    x = cornerPoint i j := by
  apply Subtype.ext
  ext k
  fin_cases k
  · exact hi.trans (cornerPoint_first _ _).symm
  · exact hj.trans (cornerPoint_second _ _).symm

theorem wordMap_eq_iff_grid_coordinate {w v : List (Fin 8)} (hlen : w.length = v.length)
    (x y : CarpetPoints) :
    wordMap w x = wordMap v y ↔
      ∀ j : Fin 2, (gridCoordinate w j : ℝ) + (x : Plane) j =
        (gridCoordinate v j : ℝ) + (y : Plane) j := by
  constructor
  · intro h j
    rw [← wordMap_scaled_coord, ← wordMap_scaled_coord, hlen, h]
  · intro h
    have hp : (3 : ℝ) ^ w.length ≠ 0 := by positivity
    apply Subtype.ext
    ext j
    apply mul_left_cancel₀ hp
    rw [wordMap_scaled_coord, h j, ← wordMap_scaled_coord, hlen]

/-- Distinct grid indices at one coordinate force opposite endpoints
for two coincident local points. -/
theorem overlap_coord_endpoints {r s : ℕ} {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (he : (r : ℝ) + x = (s : ℝ) + y) (hne : r ≠ s) :
    ∃ a b : Fin 2, x = (a.val : ℝ) ∧ y = (b.val : ℝ) ∧ a ≠ b := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : (r : ℝ) + 1 ≤ s := by exact_mod_cast h
    refine ⟨1, 0, ?_, ?_, by decide⟩
    · change x = 1
      linarith [hx.2, hy.1]
    · change y = 0
      linarith [hx.2, hy.1]
  · have hr : (s : ℝ) + 1 ≤ r := by exact_mod_cast h
    refine ⟨0, 1, ?_, ?_, by decide⟩
    · change x = 0
      linarith [hx.1, hy.2]
    · change y = 1
      linarith [hx.1, hy.2]

end CarpetEnergy
