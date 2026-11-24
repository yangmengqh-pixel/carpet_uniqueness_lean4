import CarpetCoding

/-!
# Square symmetries on the carpet

A square symmetry permutes the two coordinates and independently reflects each
output coordinate about (1/2). These eight actions realize the paper's D₄.
-/

open Function Set TopologicalSpace

namespace CarpetEnergy

/-- The eight symmetries of the square, parametrized by a coordinate swap and reflections. -/
abbrev SquareSymmetry := Bool × (Fin 2 → Bool)

private def symmetryIndex (σ : SquareSymmetry) (j : Fin 2) : Fin 2 :=
  if σ.1 then j.rev else j

private def digitSymmetry (σ : SquareSymmetry) (d : Fin 2 → Fin 3) (j : Fin 2) : Fin 3 :=
  if σ.2 j then 2 - d (symmetryIndex σ j) else d (symmetryIndex σ j)

private theorem exists_digitSymmetry (σ : SquareSymmetry) (i : Fin 8) :
    ∃ k, cellDigit k = digitSymmetry σ (cellDigit i) :=
  (by decide : ∀ (σ : SquareSymmetry) (i : Fin 8),
    ∃ k, cellDigit k = digitSymmetry σ (cellDigit i)) σ i

private theorem exists_digitSymmetry_preimage (σ : SquareSymmetry) (k : Fin 8) :
    ∃ i, cellDigit k = digitSymmetry σ (cellDigit i) :=
  (by decide : ∀ (σ : SquareSymmetry) (k : Fin 8),
    ∃ i, cellDigit k = digitSymmetry σ (cellDigit i)) σ k

/-- The ambient action of a square symmetry. -/
noncomputable def planeSymmetry (σ : SquareSymmetry) (x : Plane) : Plane :=
  WithLp.toLp 2 fun j ↦
    if σ.2 j then 1 - x (symmetryIndex σ j) else x (symmetryIndex σ j)

theorem continuous_planeSymmetry (σ : SquareSymmetry) : Continuous (planeSymmetry σ) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro j
  have hj := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) (symmetryIndex σ j)
  by_cases h : σ.2 j = true
  · simp only [ite_eq_left h]
    exact continuous_const.sub hj
  · simp only [ite_eq_right h]
    exact hj

private theorem cast_finThree_reflect (d : Fin 3) :
    (((2 - d : Fin 3) : ℕ) : ℝ) = 2 - ((d : ℕ) : ℝ) := by
  fin_cases d <;> norm_num [Fin.sub_def]

private theorem planeSymmetry_cellSimilarity (σ : SquareSymmetry) {i k : Fin 8}
    (hk : cellDigit k = digitSymmetry σ (cellDigit i)) (x : Plane) :
    planeSymmetry σ (cellSimilarity i x) = cellSimilarity k (planeSymmetry σ x) := by
  ext j
  have h := congrFun hk j
  have hc := congrArg (fun d : Fin 3 ↦ ((d : ℕ) : ℝ)) h
  rw [cellSimilarity_coord, ← cellDigit_cast]
  change (if σ.2 j then 1 - cellSimilarity i x (symmetryIndex σ j)
    else cellSimilarity i x (symmetryIndex σ j)) =
    ((if σ.2 j then 1 - x (symmetryIndex σ j) else x (symmetryIndex σ j)) +
      ((cellDigit k j : ℕ) : ℝ)) / 3
  rw [cellSimilarity_coord, ← cellDigit_cast]
  by_cases hj : σ.2 j = true
  · simp only [digitSymmetry, ite_eq_left hj, cast_finThree_reflect] at hc ⊢
    linarith
  · simp only [digitSymmetry, ite_eq_right hj] at hc ⊢
    linarith

theorem planeSymmetry_image_carpet (σ : SquareSymmetry) :
    planeSymmetry σ '' (carpet : Set Plane) = (carpet : Set Plane) := by
  let K : NonemptyCompacts Plane := carpet.map _ (continuous_planeSymmetry σ)
  have hK : (K : Set Plane) = ⋃ i : Fin 8, cellSimilarity i '' (K : Set Plane) := by
    change planeSymmetry σ '' (carpet : Set Plane) =
      ⋃ i : Fin 8, cellSimilarity i '' (planeSymmetry σ '' (carpet : Set Plane))
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp (carpet_eq_iUnion.le hx)
      obtain ⟨k, hk⟩ := exists_digitSymmetry σ i
      exact mem_iUnion.mpr ⟨k, planeSymmetry σ y, mem_image_of_mem _ hy,
        (planeSymmetry_cellSimilarity σ hk y).symm⟩
    · intro hz
      obtain ⟨k, _, ⟨y, hy, rfl⟩, rfl⟩ := mem_iUnion.mp hz
      obtain ⟨i, hi⟩ := exists_digitSymmetry_preimage σ k
      exact ⟨cellSimilarity i y, carpet_eq_iUnion.ge
        (mem_iUnion.mpr ⟨i, mem_image_of_mem _ hy⟩), planeSymmetry_cellSimilarity σ hi y⟩
  exact congrArg (fun A : NonemptyCompacts Plane ↦ (A : Set Plane)) (eq_carpet_of_eq_iUnion K hK)

/-- The square symmetry restricted to the carpet. -/
noncomputable def carpetSymmetry (σ : SquareSymmetry) (x : CarpetPoints) : CarpetPoints :=
  ⟨planeSymmetry σ x, (planeSymmetry_image_carpet σ).le (mem_image_of_mem _ x.property)⟩

theorem continuous_carpetSymmetry (σ : SquareSymmetry) : Continuous (carpetSymmetry σ) :=
  ((continuous_planeSymmetry σ).comp continuous_subtypeVal).subtype_mk _

/-- The inverse square symmetry. -/
def inverseSymmetry (σ : SquareSymmetry) : SquareSymmetry :=
  (σ.1, fun j ↦ σ.2 (symmetryIndex σ j))

private theorem symmetryIndex_involutive (σ : SquareSymmetry) (j : Fin 2) :
    symmetryIndex σ (symmetryIndex σ j) = j := by
  by_cases h : σ.1 = true
  · simp only [symmetryIndex, ite_eq_left h, Fin.rev_rev]
  · simp only [symmetryIndex, ite_eq_right h]

private theorem planeSymmetry_leftInverse (σ : SquareSymmetry) :
    LeftInverse (planeSymmetry (inverseSymmetry σ)) (planeSymmetry σ) := by
  intro x
  ext j
  have hi := symmetryIndex_involutive σ j
  change (if σ.2 (symmetryIndex σ j) then
    1 - (if σ.2 (symmetryIndex σ j) then 1 - x (symmetryIndex σ (symmetryIndex σ j))
      else x (symmetryIndex σ (symmetryIndex σ j)))
    else (if σ.2 (symmetryIndex σ j) then 1 - x (symmetryIndex σ (symmetryIndex σ j))
      else x (symmetryIndex σ (symmetryIndex σ j)))) = x j
  rw [hi]
  split_ifs <;> ring

theorem carpetSymmetry_leftInverse (σ : SquareSymmetry) :
    LeftInverse (carpetSymmetry (inverseSymmetry σ)) (carpetSymmetry σ) :=
  fun x ↦ Subtype.ext (planeSymmetry_leftInverse σ x)

theorem bijective_carpetSymmetry (σ : SquareSymmetry) : Bijective (carpetSymmetry σ) := by
  refine ⟨(carpetSymmetry_leftInverse σ).injective, fun y ↦ ?_⟩
  have hy : (y : Plane) ∈ planeSymmetry σ '' (carpet : Set Plane) :=
    (planeSymmetry_image_carpet σ).ge y.property
  obtain ⟨x, hx, h⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext h⟩

theorem carpetSymmetry_rightInverse (σ : SquareSymmetry) :
    RightInverse (carpetSymmetry (inverseSymmetry σ)) (carpetSymmetry σ) :=
  (carpetSymmetry_leftInverse σ).rightInverse_of_surjective (bijective_carpetSymmetry σ).2

/-- Square symmetries permute the cells and intertwine the cell embeddings. -/
theorem exists_carpetSymmetry_cellPerm (σ : SquareSymmetry) :
    ∃ e : Equiv.Perm (Fin 8), ∀ i,
      carpetSymmetry σ ∘ cellMap i = cellMap (e i) ∘ carpetSymmetry σ := by
  classical
  choose k hk using exists_digitSymmetry σ
  have hsurj : Surjective k := by
    intro j
    obtain ⟨i, hi⟩ := exists_digitSymmetry_preimage σ j
    exact ⟨i, cellDigit_injective ((hk i).trans hi.symm)⟩
  refine ⟨Equiv.ofBijective k ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩, fun i ↦ ?_⟩
  funext x
  exact Subtype.ext (planeSymmetry_cellSimilarity σ (hk i) x)

theorem carpetSymmetry_preimage_wordMap (σ : SquareSymmetry) (w : List (Fin 8)) :
    ∃ v : List (Fin 8), v.length = w.length ∧
      carpetSymmetry σ ⁻¹' range (wordMap w) = range (wordMap v) := by
  have hword (τ : SquareSymmetry) (w : List (Fin 8)) :
      ∃ v : List (Fin 8), v.length = w.length ∧
        carpetSymmetry τ '' range (wordMap w) = range (wordMap v) := by
    induction w with
    | nil => exact ⟨[], rfl, by simpa [wordMap, image_univ] using
        (range_eq_univ.mpr (bijective_carpetSymmetry τ).2)⟩
    | cons i w ih =>
      obtain ⟨v, hv, hset⟩ := ih
      obtain ⟨k, hk⟩ := exists_digitSymmetry τ i
      have hcomp : carpetSymmetry τ ∘ cellMap i = cellMap k ∘ carpetSymmetry τ :=
        funext fun x ↦ Subtype.ext (planeSymmetry_cellSimilarity τ hk x)
      refine ⟨k :: v, by simp only [List.length_cons, hv], ?_⟩
      simp only [wordMap, range_comp]
      rw [← image_comp, hcomp, image_comp, hset]
  obtain ⟨v, hv, h⟩ := hword (inverseSymmetry σ) w
  refine ⟨v, hv, ?_⟩
  rw [← h]
  have hi := carpetSymmetry_leftInverse σ
  have hs := (bijective_carpetSymmetry σ).2
  ext x
  constructor
  · intro hx
    exact ⟨carpetSymmetry σ x, hx, hi x⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := hs y
    simpa only [hi z, mem_preimage] using hy

end CarpetEnergy
