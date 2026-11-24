import CarpetMeasure

/-!
# Grid coordinates of word cells

The ternary coordinate integers distinguish all cells of a fixed level.
A set of diameter at most the level's side length can meet only a uniformly
bounded number of cells.
-/

open Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

/-- The lower grid index of a word cell in a given coordinate. -/
def gridCoordinate : List (Fin 8) → Fin 2 → ℕ
  | [], _ => 0
  | i :: w, j => ((cellDigit i j : Fin 3) : ℕ) * 3 ^ w.length + gridCoordinate w j

theorem gridCoordinate_lt (w : List (Fin 8)) (j : Fin 2) :
    gridCoordinate w j < 3 ^ w.length := by
  induction w with
  | nil => simp [gridCoordinate]
  | cons i w ih =>
    have hDigit : (cellDigit i j : ℕ) + 1 ≤ 3 := (cellDigit i j).isLt
    change (cellDigit i j : ℕ) * 3 ^ w.length + gridCoordinate w j < 3 ^ (w.length + 1)
    calc
      _ < (cellDigit i j : ℕ) * 3 ^ w.length + 3 ^ w.length := Nat.add_lt_add_left ih _
      _ = ((cellDigit i j : ℕ) + 1) * 3 ^ w.length := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ _ := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hDigit

theorem gridCoordinate_injective_of_length {w v : List (Fin 8)}
    (hlen : w.length = v.length) (hgrid : ∀ j, gridCoordinate w j = gridCoordinate v j) :
    w = v := by
  induction w generalizing v with
  | nil => exact (List.eq_nil_of_length_eq_zero hlen.symm).symm
  | cons i w ih =>
    cases v with
    | nil => simp at hlen
    | cons k v =>
      have hlen' : w.length = v.length := Nat.succ.inj hlen
      have htail (j : Fin 2) : gridCoordinate w j = gridCoordinate v j ∧ cellDigit i j = cellDigit k j := by
        have he := hgrid j
        change (cellDigit i j : ℕ) * 3 ^ w.length + gridCoordinate w j =
          (cellDigit k j : ℕ) * 3 ^ v.length + gridCoordinate v j at he
        rw [← hlen'] at he
        have hw := gridCoordinate_lt w j
        have hv := gridCoordinate_lt v j
        rw [← hlen'] at hv
        have he' : (cellDigit i j : ℕ) = (cellDigit k j : ℕ) := by
          rcases lt_trichotomy (cellDigit i j : ℕ) (cellDigit k j : ℕ) with hl | hl | hl
          · have hle := Nat.mul_le_mul_right (3 ^ w.length) (Nat.succ_le_of_lt hl)
            rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hle
            omega
          · exact hl
          · have hle := Nat.mul_le_mul_right (3 ^ w.length) (Nat.succ_le_of_lt hl)
            rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hle
            omega
        rw [he'] at he
        exact ⟨Nat.add_left_cancel he, Fin.ext he'⟩
      congr 1
      · exact cellDigit_injective (funext (fun j ↦ (htail j).2))
      · exact ih hlen' (fun j ↦ (htail j).1)

theorem wordMap_scaled_coord (w : List (Fin 8)) (x : CarpetPoints) (j : Fin 2) :
    (3 : ℝ) ^ w.length * (wordMap w x : Plane) j = (gridCoordinate w j : ℝ) + (x : Plane) j := by
  induction w with
  | nil => simp [wordMap, gridCoordinate]
  | cons i w ih =>
    change 3 ^ (w.length + 1) * cellSimilarity i (wordMap w x) j =
      (((cellDigit i j : ℕ) * 3 ^ w.length + gridCoordinate w j : ℕ) : ℝ) + (x : Plane) j
    rw [cellSimilarity_coord, ← cellDigit_cast, pow_succ']
    push_cast
    calc
      _ = 3 ^ w.length * (wordMap w x : Plane) j +
          (cellDigit i j : ℕ) * (3 : ℝ) ^ w.length := by ring
      _ = _ := by rw [ih]; ring

theorem gridCoordinate_bounds {n : ℕ} {w : Fin n → Fin 8} {x : CarpetPoints}
    (hx : x ∈ range (wordMap (List.ofFn w))) (j : Fin 2) :
    (gridCoordinate (List.ofFn w) j : ℝ) ≤ (3 : ℝ) ^ n * (x : Plane) j ∧
      (3 : ℝ) ^ n * (x : Plane) j ≤ (gridCoordinate (List.ofFn w) j : ℝ) + 1 := by
  obtain ⟨y, rfl⟩ := hx
  have he := wordMap_scaled_coord (List.ofFn w) y j
  rw [List.length_ofFn] at he
  rw [he]
  exact ⟨le_add_of_nonneg_right (carpet_coord_mem_Icc y j).1,
    add_le_add (le_refl _) (carpet_coord_mem_Icc y j).2⟩

private theorem coordinate_dist_le (x y : CarpetPoints) (j : Fin 2) :
    dist ((x : Plane) j) ((y : Plane) j) ≤ dist x y := by
  change dist ((x : Plane) j) ((y : Plane) j) ≤ dist (x : Plane) (y : Plane)
  exact PiLp.dist_apply_le (x : Plane) (y : Plane) j

private theorem gridCoordinate_le_of_small_dist {n : ℕ}
    {u v : Fin n → Fin 8} {x y : CarpetPoints}
    (hx : x ∈ range (wordMap (List.ofFn u))) (hy : y ∈ range (wordMap (List.ofFn v)))
    (h : dist x y ≤ (1 / 3 : ℝ) ^ n) (j : Fin 2) :
    gridCoordinate (List.ofFn u) j ≤ gridCoordinate (List.ofFn v) j + 2 := by
  have h₁ := (gridCoordinate_bounds hx j).1
  have h₂ := (gridCoordinate_bounds hy j).2
  have hxy : (x : Plane) j - (y : Plane) j ≤ (1 / 3 : ℝ) ^ n := by
    have hh := (coordinate_dist_le x y j).trans h
    rw [Real.dist_eq] at hh
    exact (abs_le.mp hh).2
  have hp : (3 : ℝ) ^ n * ((1 / 3 : ℝ) ^ n) = 1 := by
    rw [← mul_pow]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hxy (by positivity : (0 : ℝ) ≤ 3 ^ n)
  rw [hp, mul_sub] at hmul
  exact_mod_cast (show (gridCoordinate (List.ofFn u) j : ℝ) ≤
    (gridCoordinate (List.ofFn v) j : ℝ) + 2 by linarith)

/-- A set with small diameter has mass bounded by the total mass of at most
twenty-five cells at that level. -/
theorem carpetMeasure_le_of_small_ediam (A : Set CarpetPoints) (n : ℕ)
    (hA : ediam A ≤ ENNReal.ofReal ((1 / 3 : ℝ) ^ n)) :
    carpetMeasure A ≤ 25 * ((8 : ℝ≥0∞)⁻¹) ^ n := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · rw [measure_empty]
    exact bot_le
  obtain ⟨w₀, hw₀⟩ := exists_wordMap_range n x₀
  let C (w : Fin n → Fin 8) := range (wordMap (List.ofFn w))
  let W := {w : Fin n → Fin 8 // (A ∩ C w).Nonempty}
  have hb (w : W) (j : Fin 2) :
      gridCoordinate (List.ofFn w.val) j ≤ gridCoordinate (List.ofFn w₀) j + 2 ∧
      gridCoordinate (List.ofFn w₀) j ≤ gridCoordinate (List.ofFn w.val) j + 2 := by
    obtain ⟨x, hx, hxw⟩ := w.property
    have hd : dist x x₀ ≤ (1 / 3 : ℝ) ^ n := by
      have he := (edist_le_ediam_of_mem hx hx₀).trans hA
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)] at he
      exact he
    exact ⟨gridCoordinate_le_of_small_dist hxw hw₀ hd j,
      gridCoordinate_le_of_small_dist hw₀ hxw (dist_comm x x₀ ▸ hd) j⟩
  let F (w : W) (j : Fin 2) : Fin 5 := ⟨
    gridCoordinate (List.ofFn w.val) j + 2 - gridCoordinate (List.ofFn w₀) j, by
      obtain ⟨h₁, h₂⟩ := hb w j
      omega⟩
  have hf : Injective F := by
    intro u v huv
    apply Subtype.ext
    apply List.ofFn_injective
    apply gridCoordinate_injective_of_length (by rw [List.length_ofFn, List.length_ofFn])
    intro j
    have he := congrArg (fun f : Fin 2 → Fin 5 ↦ (f j).val) huv
    change gridCoordinate (List.ofFn u.val) j + 2 - gridCoordinate (List.ofFn w₀) j =
      gridCoordinate (List.ofFn v.val) j + 2 - gridCoordinate (List.ofFn w₀) j at he
    have hl := (hb u j).2
    have hr := (hb v j).2
    omega
  have hcard : Fintype.card W ≤ 25 := by
    have ht := Fintype.card_le_of_injective _ hf
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.reducePow] using ht
  have hcover : A ⊆ ⋃ w : W, C w.val := by
    intro x hx
    obtain ⟨w, hw⟩ := exists_wordMap_range n x
    exact mem_iUnion.mpr ⟨⟨w, x, hx, hw⟩, hw⟩
  calc
    _ ≤ carpetMeasure (⋃ w : W, C w.val) := measure_mono hcover
    _ ≤ ∑' w : W, carpetMeasure (C w.val) := measure_iUnion_le _
    _ = (Fintype.card W : ℝ≥0∞) * ((8 : ℝ≥0∞)⁻¹) ^ n := by
      simp only [C, carpetMeasure_range_wordMap, List.length_ofFn, tsum_fintype,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul' (by exact_mod_cast hcard) le_rfl

end CarpetEnergy
