import CarpetCellNeighborhoods
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth

/-!
# Repeated shapes of rescaled carpet neighborhoods

The relative grid coordinates encode a neighborhood in a fixed finite
set. Equal shapes match cells by translation and dilation.
-/

open Function Set

namespace CarpetEnergy

/-- A neighbor's grid offset, translated by the neighborhood radius
so that both coordinates are nonnegative. -/
def neighborhoodOffset {n r : ℕ} (w : Fin n → Fin 8)
    (v : {v // v ∈ cellNeighborhood w r}) (i : Fin 2) : Fin (2 * r + 1) :=
  ⟨gridCoordinate (List.ofFn v.val) i + r - gridCoordinate (List.ofFn w) i, by
    have h := (gridCoordinate_le_of_mem_cellNeighborhood v.property i).2
    omega⟩

theorem neighborhoodOffset_coordinate {n r : ℕ} (w : Fin n → Fin 8)
    (v : {v // v ∈ cellNeighborhood w r}) (i : Fin 2) :
    (neighborhoodOffset w v i : ℕ) + gridCoordinate (List.ofFn w) i =
      gridCoordinate (List.ofFn v.val) i + r := by
  have h := (gridCoordinate_le_of_mem_cellNeighborhood v.property i).1
  change gridCoordinate (List.ofFn v.val) i + r - gridCoordinate (List.ofFn w) i +
    gridCoordinate (List.ofFn w) i = _
  omega

theorem neighborhoodOffset_injective {n r : ℕ} (w : Fin n → Fin 8) :
    Injective (neighborhoodOffset (r := r) w) := by
  intro v u h
  apply Subtype.ext
  apply List.ofFn_injective
  apply gridCoordinate_injective_of_length (by simp)
  intro i
  have hv := neighborhoodOffset_coordinate w v i
  have hu := neighborhoodOffset_coordinate w u i
  have h' : (neighborhoodOffset w v i : ℕ) = (neighborhoodOffset w u i : ℕ) :=
    congrArg (fun t : Fin 2 → Fin (2 * r + 1) ↦ (t i : ℕ)) h
  omega

/-- The set of grid offsets present in a word neighborhood. -/
def neighborhoodShape {n : ℕ} (w : Fin n → Fin 8) (r : ℕ) :
    Set (Fin 2 → Fin (2 * r + 1)) :=
  range (neighborhoodOffset w)

/-- There is an infinite subsequence of any sequence of cells with the
same neighborhood shape at a fixed radius. -/
theorem exists_constant_neighborhoodShape_subseq (n : ℕ → ℕ)
    (w : ∀ j, Fin (n j) → Fin 8) (r : ℕ) :
    ∃ j : ℕ → ℕ, StrictMono j ∧
      ∀ k, neighborhoodShape (w (j k)) r = neighborhoodShape (w (j 0)) r := by
  classical
  let s (k : ℕ) := neighborhoodShape (w k) r
  obtain ⟨shape, hs⟩ := Finite.exists_infinite_fiber s
  have hf : (s ⁻¹' {shape}).Infinite := Set.infinite_coe_iff.mp hs
  let j := Nat.nth (fun k ↦ s k = shape)
  have he : {k | s k = shape} = s ⁻¹' {shape} := rfl
  have h' : {k | s k = shape}.Infinite := he.symm ▸ hf
  refine ⟨j, Nat.nth_strictMono h', fun k ↦ ?_⟩
  have hj (a : ℕ) : s (j a) = shape := Nat.nth_mem_of_infinite h' _
  exact (hj k).trans (hj 0).symm

/-- Equal shapes identify the finite sets of neighboring cells, with
the same offset in each grid. -/
noncomputable def neighborhoodEquiv {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r) :
    {v // v ∈ cellNeighborhood w r} ≃ {v // v ∈ cellNeighborhood u r} :=
  (Equiv.ofInjective (neighborhoodOffset w) (neighborhoodOffset_injective w)).trans
    ((Equiv.subtypeEquivRight (fun a ↦ by change a ∈ neighborhoodShape w r ↔ a ∈ neighborhoodShape u r; rw [h])).trans
      (Equiv.ofInjective (neighborhoodOffset u) (neighborhoodOffset_injective u)).symm)

theorem neighborhoodEquiv_offset {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r) (v : {v // v ∈ cellNeighborhood w r}) :
    neighborhoodOffset u (neighborhoodEquiv w u h v) = neighborhoodOffset w v := by
  let e := Equiv.ofInjective (neighborhoodOffset u) (neighborhoodOffset_injective (r := r) u)
  let t := Equiv.subtypeEquivRight (fun a ↦ by change a ∈ neighborhoodShape w r ↔ a ∈ neighborhoodShape u r; rw [h])
    (Equiv.ofInjective (neighborhoodOffset w) (neighborhoodOffset_injective (r := r) w) v)
  exact congrArg Subtype.val (e.apply_symm_apply t)

/-- In coordinates normalized to a neighborhood's central grid square,
corresponding cell maps agree on the entire carpet. -/
theorem neighborhoodEquiv_scaled_coord {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r)
    (v : {v // v ∈ cellNeighborhood w r}) (x : CarpetPoints) (i : Fin 2) :
    (3 : ℝ) ^ m * (wordMap (List.ofFn (neighborhoodEquiv w u h v).val) x : Plane) i -
        (gridCoordinate (List.ofFn u) i : ℝ) =
      (3 : ℝ) ^ n * (wordMap (List.ofFn v.val) x : Plane) i -
        (gridCoordinate (List.ofFn w) i : ℝ) := by
  let a := neighborhoodEquiv w u h v
  have hw := wordMap_scaled_coord (List.ofFn v.val) x i
  have hu := wordMap_scaled_coord (List.ofFn a.val) x i
  simp only [List.length_ofFn] at hw hu
  change (3 : ℝ) ^ m * (wordMap (List.ofFn a.val) x : Plane) i - _ = _
  rw [hu, hw]
  have hv := neighborhoodOffset_coordinate w v i
  have ha := neighborhoodOffset_coordinate u a i
  have he : (neighborhoodOffset u a i : ℕ) = (neighborhoodOffset w v i : ℕ) :=
    congrArg (fun t : Fin 2 → Fin (2 * r + 1) ↦ (t i : ℕ)) (neighborhoodEquiv_offset w u h v)
  have hgrid : gridCoordinate (List.ofFn a.val) i + gridCoordinate (List.ofFn w) i =
      gridCoordinate (List.ofFn v.val) i + gridCoordinate (List.ofFn u) i := by omega
  have hgrid' : (gridCoordinate (List.ofFn a.val) i : ℝ) + (gridCoordinate (List.ofFn w) i : ℝ) =
      (gridCoordinate (List.ofFn v.val) i : ℝ) + (gridCoordinate (List.ofFn u) i : ℝ) := by
    exact_mod_cast hgrid
  linarith only [hgrid']

theorem neighborhoodEquiv_center {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r) :
    neighborhoodEquiv w u h ⟨w, self_mem_cellNeighborhood w r⟩ =
      ⟨u, self_mem_cellNeighborhood u r⟩ := by
  apply neighborhoodOffset_injective u
  rw [neighborhoodEquiv_offset]
  funext i
  apply Fin.ext
  have hw := neighborhoodOffset_coordinate w ⟨w, self_mem_cellNeighborhood w r⟩ i
  have hu := neighborhoodOffset_coordinate u ⟨u, self_mem_cellNeighborhood u r⟩ i
  change (neighborhoodOffset w ⟨w, self_mem_cellNeighborhood w r⟩ i : ℕ) +
    gridCoordinate (List.ofFn w) i = gridCoordinate (List.ofFn w) i + r at hw
  change (neighborhoodOffset u ⟨u, self_mem_cellNeighborhood u r⟩ i : ℕ) +
    gridCoordinate (List.ofFn u) i = gridCoordinate (List.ofFn u) i + r at hu
  omega

theorem neighborhoodEquiv_gridNear {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r)
    (v t : {v // v ∈ cellNeighborhood w r}) :
    GridNear (List.ofFn (neighborhoodEquiv w u h v).val) (List.ofFn (neighborhoodEquiv w u h t).val) ↔
      GridNear (List.ofFn v.val) (List.ofFn t.val) := by
  let v' := neighborhoodEquiv w u h v
  let t' := neighborhoodEquiv w u h t
  have hpoint (i : Fin 2) (a : {v // v ∈ cellNeighborhood w r}) :
      gridCoordinate (List.ofFn (neighborhoodEquiv w u h a).val) i + gridCoordinate (List.ofFn w) i =
        gridCoordinate (List.ofFn a.val) i + gridCoordinate (List.ofFn u) i := by
    have h₁ := neighborhoodOffset_coordinate w a i
    have h₂ := neighborhoodOffset_coordinate u (neighborhoodEquiv w u h a) i
    rw [neighborhoodEquiv_offset] at h₂
    omega
  change GridNear (List.ofFn v'.val) (List.ofFn t'.val) ↔ GridNear (List.ofFn v.val) (List.ofFn t.val)
  constructor <;> intro hnear i
  · have hv := hpoint i v
    have ht := hpoint i t
    have he := hnear i
    change gridCoordinate (List.ofFn v'.val) i + gridCoordinate (List.ofFn w) i = _ at hv
    change gridCoordinate (List.ofFn t'.val) i + gridCoordinate (List.ofFn w) i = _ at ht
    exact ⟨by omega, by omega⟩
  · have hv := hpoint i v
    have ht := hpoint i t
    have he := hnear i
    change gridCoordinate (List.ofFn v'.val) i + gridCoordinate (List.ofFn w) i = _ at hv
    change gridCoordinate (List.ofFn t'.val) i + gridCoordinate (List.ofFn w) i = _ at ht
    exact ⟨by omega, by omega⟩

theorem cellNeighborhood_mono {n : ℕ} (w : Fin n → Fin 8) :
    Monotone (cellNeighborhood w) :=
  monotone_nat_of_le_succ (fun _ ↦ cellNeighborhood_subset_succ w)

theorem neighborhoodEquiv_mem_cellNeighborhood {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r) {s : ℕ} (hs : s ≤ r)
    (v : {v // v ∈ cellNeighborhood w r}) (hv : v.val ∈ cellNeighborhood w s) :
    (neighborhoodEquiv w u h v).val ∈ cellNeighborhood u s := by
  induction s generalizing v with
  | zero =>
    have he : v = ⟨w, self_mem_cellNeighborhood w r⟩ :=
      Subtype.ext (Finset.mem_singleton.mp hv)
    rw [he, neighborhoodEquiv_center]
    exact self_mem_cellNeighborhood u 0
  | succ s ih =>
    obtain ⟨a, ha, hnear⟩ := mem_cellNeighborhood_succ.mp hv
    let a' : {v // v ∈ cellNeighborhood w r} :=
      ⟨a, cellNeighborhood_mono w (Nat.le_of_succ_le hs) ha⟩
    have ha' := ih (Nat.le_of_succ_le hs) a' ha
    apply mem_cellNeighborhood_succ.mpr
    refine ⟨(neighborhoodEquiv w u h a').val, ha', ?_⟩
    apply (gridNear_iff_inter_wordMap_nonempty (by simp)).mp
    apply (neighborhoodEquiv_gridNear w u h a' v).mpr
    exact (gridNear_iff_inter_wordMap_nonempty (by simp)).mpr hnear

theorem neighborhoodEquiv_inverse_apply {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r) (v : {v // v ∈ cellNeighborhood w r}) :
    neighborhoodEquiv u w h.symm (neighborhoodEquiv w u h v) = v := by
  apply neighborhoodOffset_injective w
  rw [neighborhoodEquiv_offset, neighborhoodEquiv_offset]

theorem neighborhoodEquiv_mem_cellNeighborhood_iff {n m r : ℕ}
    (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r) {s : ℕ} (hs : s ≤ r)
    (v : {v // v ∈ cellNeighborhood w r}) :
    (neighborhoodEquiv w u h v).val ∈ cellNeighborhood u s ↔ v.val ∈ cellNeighborhood w s := by
  constructor
  · intro hv
    have h' := neighborhoodEquiv_mem_cellNeighborhood u w h.symm hs _ hv
    rw [neighborhoodEquiv_inverse_apply] at h'
    exact h'
  · exact neighborhoodEquiv_mem_cellNeighborhood w u h hs v

end CarpetEnergy
