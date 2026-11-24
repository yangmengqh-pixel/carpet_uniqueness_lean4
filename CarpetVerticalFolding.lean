import CarpetFolding
import CarpetGrid

/-!
# Vertical folding into the bottom row of a cell level

Each strip is folded by reflecting alternately in its vertical coordinate.
The fold is continuous on the whole carpet and takes a word cell to the
bottom-row cell in the same column.
-/

open Function Set

namespace CarpetEnergy

private theorem foldCoordinate_eq_left {x : ℝ} (hx : x ≤ 1 / 3) :
    foldCoordinate x = 3 * x := by
  rw [foldCoordinate, max_eq_left (by linarith), min_eq_left (by linarith)]

private theorem foldCoordinate_eq_middle {x : ℝ} (hl : 1 / 3 ≤ x) (hr : x ≤ 2 / 3) :
    foldCoordinate x = 2 - 3 * x := by
  rw [foldCoordinate, max_eq_left (by linarith), min_eq_right (by linarith)]

private theorem foldCoordinate_eq_right {x : ℝ} (hx : 2 / 3 ≤ x) :
    foldCoordinate x = 3 * x - 2 := by
  rw [foldCoordinate, max_eq_right (by linarith), min_eq_right (by linarith)]

private theorem foldCoordinate_reflect (x : ℝ) :
    foldCoordinate (1 - x) = 1 - foldCoordinate x := by
  by_cases hl : x ≤ 1 / 3
  · rw [foldCoordinate_eq_left hl, foldCoordinate_eq_right (by linarith)]
    ring
  by_cases hr : x ≤ 2 / 3
  · rw [foldCoordinate_eq_middle (le_of_not_ge hl) hr,
      foldCoordinate_eq_middle (by linarith) (by linarith [not_le.mp hl])]
    ring
  · rw [foldCoordinate_eq_right (le_of_not_ge hr), foldCoordinate_eq_left (by linarith [not_le.mp hr])]
    ring

private theorem iterate_foldCoordinate_reflect (n : ℕ) (x : ℝ) :
    (foldCoordinate^[n]) (1 - x) = 1 - (foldCoordinate^[n]) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, foldCoordinate_reflect]

/-- The bottom digit with the same horizontal coordinate as the given digit. -/
def bottomDigit (i : Fin 8) : Fin 8 := (![0, 1, 2, 2, 2, 1, 0, 0] : Fin 8 → Fin 8) i

private theorem cellDigit_bottomDigit (i : Fin 8) :
    cellDigit (bottomDigit i) 0 = cellDigit i 0 ∧ cellDigit (bottomDigit i) 1 = 0 :=
  (by decide : ∀ i, cellDigit (bottomDigit i) 0 = cellDigit i 0 ∧ cellDigit (bottomDigit i) 1 = 0) i

/-- The bottom-row word in the same column as the given word. -/
def bottomWord (w : List (Fin 8)) : List (Fin 8) := w.map bottomDigit

theorem length_bottomWord (w : List (Fin 8)) : (bottomWord w).length = w.length :=
  List.length_map _

theorem gridCoordinate_bottomWord (w : List (Fin 8)) :
    gridCoordinate (bottomWord w) 0 = gridCoordinate w 0 ∧ gridCoordinate (bottomWord w) 1 = 0 := by
  induction w with
  | nil => exact ⟨rfl, rfl⟩
  | cons i w ih =>
    simp only [bottomWord, List.map_cons, gridCoordinate]
    rw [List.length_map, (cellDigit_bottomDigit i).1, (cellDigit_bottomDigit i).2]
    dsimp only [bottomWord] at ih
    exact ⟨by rw [ih.1], by simp [ih.2]⟩

private def verticalReflection : List (Fin 8) → Bool
  | [] => false
  | i :: w => if cellDigit i 1 = 1 then !(verticalReflection w) else verticalReflection w

/-- The vertical reflection made by the fold on the given word cell. -/
def verticalFoldSymmetry (w : List (Fin 8)) : SquareSymmetry :=
  (false, fun j ↦ j == 1 && verticalReflection w)

private theorem verticalFoldSymmetry_first (w : List (Fin 8)) (x : CarpetPoints) :
    (carpetSymmetry (verticalFoldSymmetry w) x : Plane) 0 = (x : Plane) 0 := rfl

private theorem verticalFoldSymmetry_second (w : List (Fin 8)) (x : CarpetPoints) :
    (carpetSymmetry (verticalFoldSymmetry w) x : Plane) 1 =
      if verticalReflection w then 1 - (x : Plane) 1 else (x : Plane) 1 := rfl

private theorem iterate_foldCoordinate_wordMap (w : List (Fin 8)) (x : CarpetPoints) :
    (foldCoordinate^[w.length]) ((wordMap w x : Plane) 1) =
      (carpetSymmetry (verticalFoldSymmetry w) x : Plane) 1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (foldCoordinate^[w.length + 1]) (cellSimilarity i (wordMap w x) 1) = _
    rw [Function.iterate_succ_apply, cellSimilarity_coord, ← cellDigit_cast,
      foldCoordinate_cell _ _ (carpet_coord_mem_Icc _ 1), verticalFoldSymmetry_second]
    by_cases h : cellDigit i 1 = 1
    · rw [ite_eq_left h, iterate_foldCoordinate_reflect, ih, verticalFoldSymmetry_second]
      simp only [verticalReflection, ite_eq_left h]
      cases verticalReflection w <;> simp
    · rw [ite_eq_right h, ih, verticalFoldSymmetry_second]
      simp only [verticalReflection, ite_eq_right h]

private noncomputable def verticalFoldPlane (n : ℕ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![x 0, (1 / 3 : ℝ) ^ n * (foldCoordinate^[n]) (x 1)]

private theorem continuous_verticalFoldPlane (n : ℕ) : Continuous (verticalFoldPlane n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro j
  fin_cases j
  · exact PiLp.continuous_apply 2 _ 0
  · exact continuous_const.mul ((continuous_foldCoordinate.iterate n).comp (PiLp.continuous_apply 2 _ 1))

private theorem verticalFoldPlane_wordMap (w : List (Fin 8)) (x : CarpetPoints) :
    verticalFoldPlane w.length (wordMap w x : Plane) =
      (wordMap (bottomWord w) (carpetSymmetry (verticalFoldSymmetry w) x) : Plane) := by
  apply PiLp.ext
  intro j
  have hp : 0 < (3 : ℝ) ^ w.length := by positivity
  apply (mul_left_cancel₀ hp.ne')
  have hr := wordMap_scaled_coord (bottomWord w) (carpetSymmetry (verticalFoldSymmetry w) x) j
  rw [length_bottomWord] at hr
  rw [hr]
  fin_cases j
  · change (3 : ℝ) ^ w.length * (wordMap w x : Plane) 0 =
      (gridCoordinate (bottomWord w) 0 : ℝ) + (carpetSymmetry (verticalFoldSymmetry w) x : Plane) 0
    rw [wordMap_scaled_coord, (gridCoordinate_bottomWord w).1, verticalFoldSymmetry_first]
  · change (3 : ℝ) ^ w.length * ((1 / 3 : ℝ) ^ w.length *
        (foldCoordinate^[w.length]) ((wordMap w x : Plane) 1)) =
      (gridCoordinate (bottomWord w) 1 : ℝ) + (carpetSymmetry (verticalFoldSymmetry w) x : Plane) 1
    rw [← mul_assoc, ← mul_pow, (gridCoordinate_bottomWord w).2, Nat.cast_zero, zero_add,
      iterate_foldCoordinate_wordMap]
    norm_num

/-- The continuous vertical fold into the bottom row of a given level. -/
noncomputable def verticalFoldMap (n : ℕ) : C(CarpetPoints, CarpetPoints) :=
  ⟨fun x ↦ ⟨verticalFoldPlane n x, by
    obtain ⟨w, y, hy⟩ := exists_wordMap_range n x
    have he := verticalFoldPlane_wordMap (List.ofFn w) y
    rw [List.length_ofFn] at he
    rw [← hy, he]
    exact Subtype.property _⟩,
    (continuous_verticalFoldPlane n |>.comp continuous_subtypeVal).subtype_mk _⟩

theorem verticalFoldMap_wordMap (w : List (Fin 8)) (x : CarpetPoints) :
    verticalFoldMap w.length (wordMap w x) =
      wordMap (bottomWord w) (carpetSymmetry (verticalFoldSymmetry w) x) :=
  Subtype.ext (verticalFoldPlane_wordMap w x)

theorem verticalFoldMap_first (n : ℕ) (x : CarpetPoints) :
    (verticalFoldMap n x : Plane) 0 = (x : Plane) 0 := rfl

end CarpetEnergy
