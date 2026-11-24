import EnergySymmetry

/-!
# Folding across the first-level cells

Folding both coordinates maps every cell onto the carpet. After choosing
the reflection of the target cell, the folding map is a left inverse of
that cell embedding.
-/

open Function MeasureTheory Set

namespace CarpetEnergy

/-- The three affine pieces of the one-coordinate fold of the unit interval. -/
noncomputable def foldCoordinate (x : ℝ) : ℝ :=
  min (3 * x) (max (2 - 3 * x) (3 * x - 2))

theorem continuous_foldCoordinate : Continuous foldCoordinate := by
  unfold foldCoordinate
  fun_prop

theorem foldCoordinate_cell (d : Fin 3) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    foldCoordinate ((x + ((d : ℕ) : ℝ)) / 3) = if d = 1 then 1 - x else x := by
  obtain ⟨hx₀, hx₁⟩ := hx
  fin_cases d
  · norm_num [foldCoordinate]
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
    linarith
  · norm_num [foldCoordinate]
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
    linarith
  · norm_num [foldCoordinate]
    rw [max_eq_right (by linarith), min_eq_right (by linarith)]
    linarith

private noncomputable def planeFold (x : Plane) : Plane :=
  WithLp.toLp 2 fun j ↦ foldCoordinate (x j)

private theorem continuous_planeFold : Continuous planeFold :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    (continuous_pi fun j ↦ continuous_foldCoordinate.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) j))

private def reflectionMask (i : Fin 8) (j : Fin 2) : Bool :=
  decide (cellDigit i j = 1)

private theorem planeFold_cellSimilarity (i : Fin 8) (x : CarpetPoints) :
    planeFold (cellSimilarity i x) = planeSymmetry (false, reflectionMask i) x := by
  ext j
  change foldCoordinate (cellSimilarity i x j) =
    if reflectionMask i j then 1 - (x : Plane) j else (x : Plane) j
  rw [cellSimilarity_coord, ← cellDigit_cast,
    foldCoordinate_cell (cellDigit i j) _ (carpet_coord_mem_Icc x j)]
  simp only [reflectionMask, decide_eq_true_eq]

private noncomputable def foldCarpet (x : CarpetPoints) : CarpetPoints :=
  ⟨planeFold x, by
    obtain ⟨i, y, hy, hxy⟩ := mem_iUnion.mp (carpet_eq_iUnion.le x.property)
    rw [← hxy]
    let yK : CarpetPoints := ⟨y, hy⟩
    exact (planeFold_cellSimilarity i yK).symm ▸ (carpetSymmetry (false, reflectionMask i) yK).property⟩

private theorem continuous_foldCarpet : Continuous foldCarpet :=
  (continuous_planeFold.comp continuous_subtypeVal).subtype_mk _

private theorem foldCarpet_cellMap (i : Fin 8) (x : CarpetPoints) :
    foldCarpet (cellMap i x) = carpetSymmetry (false, reflectionMask i) x :=
  Subtype.ext (planeFold_cellSimilarity i x)

private theorem reflection_comp_reflection (a b : Fin 2 → Bool) (x : CarpetPoints) :
    carpetSymmetry (false, a) (carpetSymmetry (false, b) x) =
      carpetSymmetry (false, fun j ↦ if a j then !(b j) else b j) x := by
  apply Subtype.ext
  ext j
  let t := (x : Plane) j
  change (if a j then 1 - (if b j then 1 - t else t) else
      (if b j then 1 - t else t)) =
    (if (if a j then !(b j) else b j) then 1 - t else t)
  cases a j <;> cases b j <;> simp

/-- The continuous folding map that undoes the given first-level embedding. -/
noncomputable def cellFoldingMap (i : Fin 8) : C(CarpetPoints, CarpetPoints) :=
  ⟨carpetSymmetry (false, reflectionMask i) ∘ foldCarpet,
    (continuous_carpetSymmetry _).comp continuous_foldCarpet⟩

theorem cellFoldingMap_leftInverse (i : Fin 8) : LeftInverse (cellFoldingMap i) (cellMap i) := by
  intro x
  change carpetSymmetry (false, reflectionMask i) (foldCarpet (cellMap i x)) = x
  rw [foldCarpet_cellMap]
  exact carpetSymmetry_leftInverse (false, reflectionMask i) x

/-- The folding map targeting the middle bottom cell also inverts the middle top cell. -/
theorem cellFoldingMap_one_leftInverse_five : LeftInverse (cellFoldingMap 1) (cellMap 5) := by
  have h : reflectionMask (1 : Fin 8) = reflectionMask (5 : Fin 8) := by decide
  intro x
  change carpetSymmetry (false, reflectionMask (1 : Fin 8)) (foldCarpet (cellMap 5 x)) = x
  rw [foldCarpet_cellMap, ← h]
  exact carpetSymmetry_leftInverse (false, reflectionMask (1 : Fin 8)) x

/-- The first coordinate of the middle-column folding on the middle strip. -/
theorem cellFoldingMap_one_first_coord (x : CarpetPoints)
    (hx : (x : Plane) 0 ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    ((cellFoldingMap 1 x : CarpetPoints) : Plane) 0 = 3 * (x : Plane) 0 - 1 := by
  change 1 - foldCoordinate ((x : Plane) 0) = _
  rcases hx with ⟨h₁, h₂⟩
  rw [foldCoordinate, max_eq_left (by linarith), min_eq_right (by linarith)]
  ring

theorem exists_cellFoldingMap_comp_cellMap (i j : Fin 8) :
    ∃ σ : SquareSymmetry, cellFoldingMap i ∘ cellMap j = carpetSymmetry σ := by
  refine ⟨(false, fun k ↦ if reflectionMask i k then !(reflectionMask j k)
    else reflectionMask j k), ?_⟩
  funext x
  change carpetSymmetry (false, reflectionMask i) (foldCarpet (cellMap j x)) = _
  rw [foldCarpet_cellMap, reflection_comp_reflection]

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A continuous finite-energy function extends from any first-level cell. -/
theorem exists_continuous_extension_cell (i : Fin 8)
    (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain) :
    ∃ v : C(CarpetPoints, ℝ), continuousLp p v ∈ E.domain ∧
      (v : CarpetPoints → ℝ) ∘ cellMap i = u := by
  let v := u.comp (cellFoldingMap i)
  refine ⟨v, E.continuous_gluing v |>.mpr (fun j ↦ ?_), ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_cellFoldingMap_comp_cellMap i j
    let us := u.comp ⟨carpetSymmetry σ, continuous_carpetSymmetry σ⟩
    have hcomp : v.comp ⟨cellMap j, continuous_cellMap j⟩ = us := by
      ext x
      exact congrArg u (congrFun hσ x)
    have hpull : symmetryPullback σ (continuousLp p u) = continuousLp p us := by
      apply (symmetryPullback_isLpPullback σ (continuousLp p u)).unique
      exact (continuousLp_ae_eq p us).trans
        (((measurePreserving_carpetSymmetry σ).quasiMeasurePreserving.ae_eq_comp
          (continuousLp_ae_eq p u)).symm)
    rw [hcomp, ← hpull]
    exact (E.pullbackSymmetry σ ⟨continuousLp p u, hu⟩).property
  · funext x
    exact congrArg u (cellFoldingMap_leftInverse i x)

/-- A continuous finite-energy function extends from any finite-word cell. -/
theorem exists_continuous_extension_word (w : List (Fin 8))
    (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain) :
    ∃ v : C(CarpetPoints, ℝ), continuousLp p v ∈ E.domain ∧
      (v : CarpetPoints → ℝ) ∘ wordMap w = u := by
  induction w with
  | nil => exact ⟨u, hu, rfl⟩
  | cons i w ih =>
    obtain ⟨v, hv, hvw⟩ := ih
    obtain ⟨g, hg, hgi⟩ := E.exists_continuous_extension_cell i v hv
    refine ⟨g, hg, ?_⟩
    change (g : CarpetPoints → ℝ) ∘ (cellMap i ∘ wordMap w) = _
    rw [← Function.comp_assoc, hgi, hvw]

end SelfSimilarPEnergy
end CarpetEnergy
