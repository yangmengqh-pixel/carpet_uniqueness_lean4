import EnergyComponentInterpolation

/-!
# Interpolation of the horizontal coordinate on word corners

Interpolating the coordinate values at the grid corners gives a sequence
whose restriction to each word cell is a translated and rescaled profile.
The difference between successive levels is a rescaled copy of a fixed
difference, at every level.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent

open CornerProfile

variable {p : ℝ} {E : SelfSimilarPEnergy p} {Q : E.SelfSimilarComponent}

private theorem coordinate_cornerData (n : ℕ) (w : Fin n → Fin 8) (i j : Fin 2) :
    cornerData (fun z ↦ (z : Plane) 0) (List.ofFn w) i j =
      ((gridCoordinate (List.ofFn w) 0 : ℝ) + i.val) / (3 : ℝ) ^ n := by
  have h := wordMap_scaled_coord (List.ofFn w) (cornerPoint i j) 0
  rw [cornerPoint_first, List.length_ofFn] at h
  change (wordMap (List.ofFn w) (cornerPoint i j) : Plane) 0 = _
  exact (eq_div_iff (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0))).mpr (by rw [mul_comm]; exact h)

/-- Interpolate the horizontal coordinate at the corners of each level. -/
theorem CornerProfile.exists_coordinate_interp (P : Q.CornerProfile) (n : ℕ) :
    ∃ g ∈ Q.continuousKernel, ∀ (w : Fin n → Fin 8) x, g (wordMap (List.ofFn w) x) =
      ((gridCoordinate (List.ofFn w) 0 : ℝ) + P.toContinuousMap x) / (3 : ℝ) ^ n := by
  obtain ⟨g, hg, h⟩ := P.exists_global_interpolate (fun z ↦ (z : Plane) 0) n
  refine ⟨g, hg, fun w x ↦ ?_⟩
  rw [h, P.interpolate_apply, coordinate_cornerData, coordinate_cornerData,
    coordinate_cornerData, coordinate_cornerData]
  have h3 : (3 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  norm_num only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  ring

private theorem wordMap_append_singleton (w : List (Fin 8)) (i : Fin 8) (x : CarpetPoints) :
    wordMap (w ++ [i]) x = wordMap w (cellMap i x) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change cellMap j (wordMap (w ++ [i]) x) = cellMap j (wordMap w (cellMap i x))
    rw [ih]

private theorem gridCoordinate_append_singleton (w : List (Fin 8)) (i : Fin 8) :
    gridCoordinate (w ++ [i]) 0 = 3 * gridCoordinate w 0 + (cellDigit i 0 : ℕ) := by
  induction w with
  | nil => simp [gridCoordinate]
  | cons j w ih =>
    simp only [List.cons_append, gridCoordinate, List.length_append, List.length_singleton, ih, pow_succ]
    ring

/-- Comparing interpolation on level `n+1` and level `1` within a word cell. -/
theorem coordinate_interp_succ (P : Q.CornerProfile) (n : ℕ)
    {g₁ g : C(CarpetPoints, ℝ)}
    (h₁ : ∀ (w : Fin 1 → Fin 8) x, g₁ (wordMap (List.ofFn w) x) =
      ((gridCoordinate (List.ofFn w) 0 : ℝ) + P.toContinuousMap x) / (3 : ℝ) ^ 1)
    (h : ∀ (w : Fin (n + 1) → Fin 8) x, g (wordMap (List.ofFn w) x) =
      ((gridCoordinate (List.ofFn w) 0 : ℝ) + P.toContinuousMap x) / (3 : ℝ) ^ (n + 1))
    (w : Fin n → Fin 8) (x : CarpetPoints) :
    g (wordMap (List.ofFn w) x) =
      ((gridCoordinate (List.ofFn w) 0 : ℝ) + g₁ x) / (3 : ℝ) ^ n := by
  obtain ⟨v, y, rfl⟩ := exists_wordMap_range 1 x
  let i := v 0
  have hv : List.ofFn v = [i] := by rw [List.ofFn_succ]; rfl
  let w' := List.ofFn w ++ [i]
  have hw : w'.length = n + 1 := by simp [w']
  let f : Fin (n + 1) → Fin 8 := fun j ↦ w'.get (Fin.cast hw.symm j)
  have hf : List.ofFn f = w' := by
    apply List.ext_get
    · exact (List.length_ofFn.trans hw.symm)
    · intro j hj hj'
      rw [List.get_ofFn]
      rfl
  rw [h₁, hv]
  have hh := h f y
  rw [hf] at hh
  change g (wordMap (List.ofFn w ++ [i]) y) = _ at hh
  rw [wordMap_append_singleton] at hh
  change g (wordMap (List.ofFn w) (cellMap i y)) = _
  rw [hh, show gridCoordinate w' 0 = _ from gridCoordinate_append_singleton _ _]
  simp only [gridCoordinate, List.length_nil, pow_zero, mul_one, add_zero, pow_one]
  push_cast
  rw [pow_succ]
  ring

/-- The coordinate interpolants converge uniformly, with error at most the cell width. -/
theorem coordinate_interp_abs_sub_le (P : Q.CornerProfile) (n : ℕ)
    (g : C(CarpetPoints, ℝ))
    (h : ∀ (w : Fin n → Fin 8) x, g (wordMap (List.ofFn w) x) =
      ((gridCoordinate (List.ofFn w) 0 : ℝ) + P.toContinuousMap x) / (3 : ℝ) ^ n)
    (z : CarpetPoints) : |g z - (z : Plane) 0| ≤ ((3 : ℝ) ^ n)⁻¹ := by
  obtain ⟨w, x, rfl⟩ := exists_wordMap_range n z
  have hscaled := wordMap_scaled_coord (List.ofFn w) x 0
  rw [List.length_ofFn] at hscaled
  have hp : 0 < (3 : ℝ) ^ n := by positivity
  have hz : (wordMap (List.ofFn w) x : Plane) 0 =
      ((gridCoordinate (List.ofFn w) 0 : ℝ) + (x : Plane) 0) / (3 : ℝ) ^ n :=
    (eq_div_iff hp.ne').mpr (by rw [mul_comm]; exact hscaled)
  rw [h, hz, ← sub_div, add_sub_add_left_eq_sub, abs_div, abs_of_pos hp]
  exact (div_le_div_of_nonneg_right (abs_le.mpr ⟨
    by linarith [(P.bounds x).1, (carpet_coord_mem_Icc x 0).2],
    by linarith [(P.bounds x).2, (carpet_coord_mem_Icc x 0).1]⟩) hp.le).trans_eq (one_div _)

end CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent
