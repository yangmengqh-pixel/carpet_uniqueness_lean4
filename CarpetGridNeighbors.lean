import CarpetGrid

/-!
# Side neighbors at a grid corner

A diagonal pair of occupied carpet squares has an occupied common side
neighbor. The recursive digit criterion reduces this to a two-by-two block
inside one parent square, or the same assertion on the coarser grid.
-/

open Function Set

namespace CarpetEnergy

private theorem gridCoordinate_snoc (w : List (Fin 8)) (i : Fin 8) (j : Fin 2) :
    gridCoordinate (w ++ [i]) j = 3 * gridCoordinate w j + (cellDigit i j : ℕ) := by
  induction w with
  | nil => simp [gridCoordinate]
  | cons a w ih =>
    rw [List.cons_append, gridCoordinate, gridCoordinate, ih, List.length_append, List.length_singleton,
      pow_succ]
    ring

private theorem exists_cellDigit_of_pair (a b : Fin 3) (h : a ≠ 1 ∨ b ≠ 1) :
    ∃ i : Fin 8, cellDigit i 0 = a ∧ cellDigit i 1 = b :=
  (by decide : ∀ a b : Fin 3, (a ≠ 1 ∨ b ≠ 1) → ∃ i, cellDigit i 0 = a ∧ cellDigit i 1 = b) a b h

private theorem cellDigit_ne_center (i : Fin 8) : cellDigit i 0 ≠ 1 ∨ cellDigit i 1 ≠ 1 :=
  (by decide : ∀ i, cellDigit i 0 ≠ 1 ∨ cellDigit i 1 ≠ 1) i

/-- The occupied squares at level n, expressed in integer grid coordinates. -/
def gridAdmissible : ℕ → ℕ → ℕ → Prop
  | 0, r, s => r = 0 ∧ s = 0
  | n + 1, r, s => gridAdmissible n (r / 3) (s / 3) ∧ (r % 3 ≠ 1 ∨ s % 3 ≠ 1)

theorem gridAdmissible_of_word (w : List (Fin 8)) :
    gridAdmissible w.length (gridCoordinate w 0) (gridCoordinate w 1) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton w i ih =>
    rw [List.length_append, List.length_singleton, gridCoordinate_snoc, gridCoordinate_snoc]
    change gridAdmissible w.length ((3 * gridCoordinate w 0 + (cellDigit i 0 : ℕ)) / 3)
      ((3 * gridCoordinate w 1 + (cellDigit i 1 : ℕ)) / 3) ∧ _
    have hdiv (j : Fin 2) : (3 * gridCoordinate w j + (cellDigit i j : ℕ)) / 3 = gridCoordinate w j := by
      have := (cellDigit i j).isLt
      omega
    have hmod (j : Fin 2) : (3 * gridCoordinate w j + (cellDigit i j : ℕ)) % 3 = (cellDigit i j : ℕ) := by
      have := (cellDigit i j).isLt
      omega
    refine ⟨by rw [hdiv, hdiv]; exact ih, ?_⟩
    rw [hmod, hmod]
    exact (cellDigit_ne_center i).imp (fun h e ↦ h (Fin.ext e)) (fun h e ↦ h (Fin.ext e))

theorem exists_word_of_gridAdmissible {n r s : ℕ} (h : gridAdmissible n r s) :
    ∃ w : List (Fin 8), w.length = n ∧ gridCoordinate w 0 = r ∧ gridCoordinate w 1 = s := by
  induction n generalizing r s with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hp, hd⟩ := h
    obtain ⟨w, hw, hr, hs⟩ := ih hp
    let a : Fin 3 := ⟨r % 3, Nat.mod_lt _ (by decide)⟩
    let b : Fin 3 := ⟨s % 3, Nat.mod_lt _ (by decide)⟩
    obtain ⟨i, hi, hj⟩ := exists_cellDigit_of_pair a b
      (hd.imp (fun hn he ↦ hn (congrArg Fin.val he)) (fun hn he ↦ hn (congrArg Fin.val he)))
    refine ⟨w ++ [i], by simp only [List.length_append, List.length_singleton, hw], ?_, ?_⟩
    · rw [gridCoordinate_snoc, hr, hi]
      change 3 * (r / 3) + r % 3 = r
      omega
    · rw [gridCoordinate_snoc, hs, hj]
      change 3 * (s / 3) + s % 3 = s
      omega

private theorem mod_ne_one_of_quotient_ne {a b : ℕ}
    (hal : a ≤ b + 1) (hau : b ≤ a + 1) (h : a / 3 ≠ b / 3) :
    a % 3 ≠ 1 ∧ b % 3 ≠ 1 := by omega

/-- In an adjacent grid block, two occupied opposite corners imply that
at least one of the cross coordinates is also occupied. -/
theorem gridAdmissible_cross {n r₀ r₁ s₀ s₁ : ℕ}
    (hr₀ : r₀ ≤ r₁ + 1) (hr₁ : r₁ ≤ r₀ + 1)
    (hs₀ : s₀ ≤ s₁ + 1) (hs₁ : s₁ ≤ s₀ + 1)
    (h₀ : gridAdmissible n r₀ s₀) (h₁ : gridAdmissible n r₁ s₁) :
    gridAdmissible n r₀ s₁ ∨ gridAdmissible n r₁ s₀ := by
  induction n generalizing r₀ r₁ s₀ s₁ with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h₀
    obtain ⟨rfl, rfl⟩ := h₁
    exact Or.inl ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h₀p, h₀d⟩ := h₀
    obtain ⟨h₁p, h₁d⟩ := h₁
    by_cases hr : r₀ / 3 = r₁ / 3
    · by_cases hs : s₀ / 3 = s₁ / 3
      · have hd : (r₀ % 3 ≠ 1 ∨ s₁ % 3 ≠ 1) ∨ (r₁ % 3 ≠ 1 ∨ s₀ % 3 ≠ 1) := by tauto
        exact hd.imp (fun h ↦ ⟨hs ▸ h₀p, h⟩) (fun h ↦ ⟨hr ▸ h₀p, h⟩)
      · exact Or.inl ⟨hr.symm ▸ h₁p, Or.inr (mod_ne_one_of_quotient_ne hs₀ hs₁ hs).2⟩
    · have hd := mod_ne_one_of_quotient_ne hr₀ hr₁ hr
      by_cases hs : s₀ / 3 = s₁ / 3
      · exact Or.inl ⟨hs ▸ h₀p, Or.inl hd.1⟩
      · have hcross := ih (by omega) (by omega) (by omega) (by omega) h₀p h₁p
        exact hcross.imp (fun h ↦ ⟨h, Or.inl hd.1⟩) (fun h ↦ ⟨h, Or.inl hd.2⟩)

/-- The coordinates of the two closed grid squares differ by at most one. -/
def GridNear (w v : List (Fin 8)) : Prop :=
  ∀ j : Fin 2, gridCoordinate w j ≤ gridCoordinate v j + 1 ∧
    gridCoordinate v j ≤ gridCoordinate w j + 1

theorem gridNear_symm {w v : List (Fin 8)} (h : GridNear w v) : GridNear v w :=
  fun j ↦ ⟨(h j).2, (h j).1⟩

theorem gridNear_refl (w : List (Fin 8)) : GridNear w w :=
  fun _ ↦ ⟨by omega, by omega⟩

theorem gridNear_of_mem_inter {w v : List (Fin 8)} (hlen : w.length = v.length)
    {x : CarpetPoints} (hw : x ∈ range (wordMap w)) (hv : x ∈ range (wordMap v)) :
    GridNear w v := by
  obtain ⟨y, hy⟩ := hw
  obtain ⟨z, hz⟩ := hv
  intro j
  have h₀ := wordMap_scaled_coord w y j
  have h₁ := wordMap_scaled_coord v z j
  rw [hy] at h₀
  rw [hz, ← hlen] at h₁
  have hyj := carpet_coord_mem_Icc y j
  have hzj := carpet_coord_mem_Icc z j
  exact ⟨by
    exact_mod_cast (show (gridCoordinate w j : ℝ) ≤ (gridCoordinate v j : ℝ) + 1 by
      linarith [hyj.1, hzj.2]), by
    exact_mod_cast (show (gridCoordinate v j : ℝ) ≤ (gridCoordinate w j : ℝ) + 1 by
      linarith [hyj.2, hzj.1])⟩

/-- The squares share a side in the grid, in either orientation. -/
def GridSideNeighbor (w v : List (Fin 8)) : Prop :=
  ∃ j : Fin 2, gridCoordinate w j.rev = gridCoordinate v j.rev ∧
    (gridCoordinate v j = gridCoordinate w j + 1 ∨ gridCoordinate w j = gridCoordinate v j + 1)

theorem gridNear_of_sideNeighbor {w v : List (Fin 8)} (h : GridSideNeighbor w v) : GridNear w v := by
  obtain ⟨j, hfixed, hstep⟩ := h
  intro k
  have hk := (by decide : ∀ k j : Fin 2, k = j ∨ k = j.rev) k j
  rcases hk with rfl | rfl
  · rcases hstep <;> omega
  · omega

private theorem gridSideNeighbor_of_same_other {w v : List (Fin 8)}
    (h : GridNear w v) (j : Fin 2) (hstep : gridCoordinate w j ≠ gridCoordinate v j)
    (hfixed : gridCoordinate w j.rev = gridCoordinate v j.rev) : GridSideNeighbor w v := by
  obtain ⟨h₁, h₂⟩ := h j
  exact ⟨j, hfixed, by omega⟩

/-- Squares meeting in the grid are equal, share a side, or have a common
side neighbor at the same level. -/
theorem eq_or_gridSideNeighbor_or_via {w v : List (Fin 8)}
    (hlen : w.length = v.length) (h : GridNear w v) :
    w = v ∨ GridSideNeighbor w v ∨
      ∃ u : List (Fin 8), u.length = w.length ∧ GridSideNeighbor w u ∧ GridSideNeighbor u v := by
  let a := gridCoordinate w 0
  let b := gridCoordinate w 1
  let c := gridCoordinate v 0
  let d := gridCoordinate v 1
  have h₀ : a ≤ c + 1 ∧ c ≤ a + 1 := h 0
  have h₁ : b ≤ d + 1 ∧ d ≤ b + 1 := h 1
  by_cases hxa : a = c
  · by_cases hyb : b = d
    · refine Or.inl (gridCoordinate_injective_of_length hlen ?_)
      intro j
      fin_cases j
      · exact hxa
      · exact hyb
    · exact Or.inr (Or.inl (gridSideNeighbor_of_same_other h 1 hyb hxa))
  by_cases hyb : b = d
  · exact Or.inr (Or.inl (gridSideNeighbor_of_same_other h 0 hxa hyb))
  have hw : gridAdmissible w.length a b := gridAdmissible_of_word w
  have hv : gridAdmissible w.length c d := hlen.symm ▸ gridAdmissible_of_word v
  have hcross := gridAdmissible_cross h₀.1 h₀.2 h₁.1 h₁.2 hw hv
  refine Or.inr (Or.inr ?_)
  rcases hcross with hcross | hcross
  · obtain ⟨u, hu, hux, huy⟩ := exists_word_of_gridAdmissible hcross
    refine ⟨u, hu, ⟨1, hux.symm, ?_⟩, ⟨0, huy, ?_⟩⟩
    · change gridCoordinate u 1 = b + 1 ∨ b = gridCoordinate u 1 + 1
      rw [huy]
      omega
    · change c = gridCoordinate u 0 + 1 ∨ gridCoordinate u 0 = c + 1
      rw [hux]
      omega
  · obtain ⟨u, hu, hux, huy⟩ := exists_word_of_gridAdmissible hcross
    refine ⟨u, hu, ⟨0, huy.symm, ?_⟩, ⟨1, hux, ?_⟩⟩
    · change gridCoordinate u 0 = a + 1 ∨ a = gridCoordinate u 0 + 1
      rw [hux]
      omega
    · change d = gridCoordinate u 1 + 1 ∨ gridCoordinate u 1 = d + 1
      rw [huy]
      omega

end CarpetEnergy
