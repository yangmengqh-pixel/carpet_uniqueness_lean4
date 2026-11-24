import CarpetCorners
import EnergyGridComparison

/-!
# Word-cell neighborhoods

Grid adjacency equals intersection of same-level carpet cells. The
iterated neighborhood therefore agrees with the geometric neighborhood
in (4.5), and its cardinality is bounded by the grid square about the
central cell.
-/

open Function Set

namespace CarpetEnergy

private theorem gridNear_coordinate_corners (r s : ℕ) (hrs : r ≤ s + 1) (hsr : s ≤ r + 1) :
    ∃ a b : Fin 2, r + a.val = s + b.val := by
  rcases lt_trichotomy r s with h | h | h
  · exact ⟨1, 0, by change r + 1 = s + 0; omega⟩
  · exact ⟨0, 0, by rw [h]⟩
  · exact ⟨0, 1, by change r + 0 = s + 1; omega⟩

theorem gridNear_iff_inter_wordMap_nonempty {w v : List (Fin 8)} (hlen : w.length = v.length) :
    GridNear w v ↔ (range (wordMap w) ∩ range (wordMap v)).Nonempty := by
  constructor
  · intro h
    obtain ⟨i, i', h₀⟩ := gridNear_coordinate_corners _ _ (h 0).1 (h 0).2
    obtain ⟨j, j', h₁⟩ := gridNear_coordinate_corners _ _ (h 1).1 (h 1).2
    have he : wordMap w (cornerPoint i j) = wordMap v (cornerPoint i' j') := by
      apply (wordMap_eq_iff_grid_coordinate hlen _ _).2
      intro k
      fin_cases k
      · change (gridCoordinate w 0 : ℝ) + (cornerPoint i j : Plane) 0 =
          (gridCoordinate v 0 : ℝ) + (cornerPoint i' j' : Plane) 0
        rw [cornerPoint_first, cornerPoint_first]
        exact_mod_cast h₀
      · change (gridCoordinate w 1 : ℝ) + (cornerPoint i j : Plane) 1 =
          (gridCoordinate v 1 : ℝ) + (cornerPoint i' j' : Plane) 1
        rw [cornerPoint_second, cornerPoint_second]
        exact_mod_cast h₁
    exact ⟨_, mem_range_self _, ⟨_, he.symm⟩⟩
  · rintro ⟨x, hx, hy⟩
    exact gridNear_of_mem_inter hlen hx hy

/-- The k-th grid neighborhood of a word cell, including the central cell. -/
noncomputable def cellNeighborhood {n : ℕ} (w : Fin n → Fin 8) : ℕ → Finset (Fin n → Fin 8)
  | 0 => {w}
  | k + 1 => by classical exact (cellNeighborhood w k).biUnion gridNeighbors

theorem mem_cellNeighborhood_succ {n k : ℕ} {w v : Fin n → Fin 8} :
    v ∈ cellNeighborhood w (k + 1) ↔
      ∃ u ∈ cellNeighborhood w k, (range (wordMap (List.ofFn u)) ∩
        range (wordMap (List.ofFn v))).Nonempty := by
  classical
  simp only [cellNeighborhood, Finset.mem_biUnion, mem_gridNeighbors,
    gridNear_iff_inter_wordMap_nonempty (by simp : (List.ofFn (_ : Fin n → Fin 8)).length =
      (List.ofFn (_ : Fin n → Fin 8)).length)]

theorem cellNeighborhood_subset_succ {n k : ℕ} (w : Fin n → Fin 8) :
    cellNeighborhood w k ⊆ cellNeighborhood w (k + 1) := by
  intro v hv
  exact mem_cellNeighborhood_succ.mpr ⟨v, hv, _, mem_range_self (bottomPoint 0), mem_range_self _⟩

theorem self_mem_cellNeighborhood {n : ℕ} (w : Fin n → Fin 8) (k : ℕ) :
    w ∈ cellNeighborhood w k := by
  induction k with
  | zero => exact Finset.mem_singleton_self _
  | succ k ih => exact cellNeighborhood_subset_succ w ih

theorem gridCoordinate_le_of_mem_cellNeighborhood {n k : ℕ} {w v : Fin n → Fin 8}
    (hv : v ∈ cellNeighborhood w k) (j : Fin 2) :
    gridCoordinate (List.ofFn w) j ≤ gridCoordinate (List.ofFn v) j + k ∧
      gridCoordinate (List.ofFn v) j ≤ gridCoordinate (List.ofFn w) j + k := by
  induction k generalizing v with
  | zero =>
    have he : v = w := Finset.mem_singleton.mp hv
    rw [he, add_zero]
    exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨u, hu, he⟩ := mem_cellNeighborhood_succ.mp hv
    have h := (gridNear_iff_inter_wordMap_nonempty (by simp)).2 he j
    obtain ⟨h₁, h₂⟩ := ih hu
    omega

/-- The uniform neighborhood cardinality in (4.6). -/
theorem card_cellNeighborhood_le {n : ℕ} (w : Fin n → Fin 8) (k : ℕ) :
    (cellNeighborhood w k).card ≤ (2 * k + 1) ^ 2 := by
  classical
  let W := {v : Fin n → Fin 8 // v ∈ cellNeighborhood w k}
  let F (v : W) (j : Fin 2) : Fin (2 * k + 1) :=
    ⟨gridCoordinate (List.ofFn v.val) j + k - gridCoordinate (List.ofFn w) j, by
      have h := (gridCoordinate_le_of_mem_cellNeighborhood v.property j).2
      omega⟩
  have hF : Injective F := by
    intro u v he
    apply Subtype.ext
    apply List.ofFn_injective
    apply gridCoordinate_injective_of_length (by simp)
    intro j
    have hm := congrArg (fun f : Fin 2 → Fin (2 * k + 1) ↦ (f j).val) he
    change gridCoordinate (List.ofFn u.val) j + k - gridCoordinate (List.ofFn w) j =
      gridCoordinate (List.ofFn v.val) j + k - gridCoordinate (List.ofFn w) j at hm
    have h₁ := (gridCoordinate_le_of_mem_cellNeighborhood u.property j).1
    have h₂ := (gridCoordinate_le_of_mem_cellNeighborhood v.property j).1
    omega
  have h := Fintype.card_le_of_injective F hF
  simpa only [W, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using h

/-- Following an additional adjacent cell enlarges the starting neighborhood by one step. -/
theorem cellNeighborhood_subset_of_adjacent {n : ℕ} {u v : Fin n → Fin 8}
    (huv : u ∈ gridNeighbors v) (k : ℕ) :
    cellNeighborhood u k ⊆ cellNeighborhood v (k + 1) := by
  induction k with
  | zero =>
    intro a ha
    have h : a = u := Finset.mem_singleton.mp ha
    subst a
    exact mem_cellNeighborhood_succ.mpr ⟨v, Finset.mem_singleton_self _,
      (gridNear_iff_inter_wordMap_nonempty (by simp)).mp (mem_gridNeighbors.mp huv)⟩
  | succ k ih =>
    intro a ha
    obtain ⟨b, hb, h⟩ := mem_cellNeighborhood_succ.mp ha
    exact mem_cellNeighborhood_succ.mpr ⟨b, ih hb, h⟩

theorem mem_cellNeighborhood_symm {n k : ℕ} {u v : Fin n → Fin 8} :
    v ∈ cellNeighborhood u k → u ∈ cellNeighborhood v k := by
  induction k generalizing u v with
  | zero =>
    intro h
    have he : v = u := Finset.mem_singleton.mp h
    subst v
    exact Finset.mem_singleton_self _
  | succ k ih =>
    intro h
    obtain ⟨w, hw, hnear⟩ := mem_cellNeighborhood_succ.mp h
    have hvw : w ∈ gridNeighbors v :=
      mem_gridNeighbors.mpr (gridNear_symm ((gridNear_iff_inter_wordMap_nonempty (by simp)).mpr hnear))
    exact cellNeighborhood_subset_of_adjacent hvw k (ih hw)

theorem dist_le_of_mem_cellNeighborhood {n k : ℕ} {w v : Fin n → Fin 8}
    (hv : v ∈ cellNeighborhood w k) {x y : CarpetPoints}
    (hx : x ∈ range (wordMap (List.ofFn w))) (hy : y ∈ range (wordMap (List.ofFn v))) :
    dist x y ≤ ((k : ℝ) + 1) * ((1 / 3 : ℝ) ^ n * Metric.diam (univ : Set CarpetPoints)) := by
  induction k generalizing v y with
  | zero =>
    have he : v = w := Finset.mem_singleton.mp hv
    subst v
    simpa only [Nat.cast_zero, zero_add, one_mul] using wordMap_dist_le n w hx hy
  | succ k ih =>
    obtain ⟨u, hu, z, hz, hzy⟩ := mem_cellNeighborhood_succ.mp hv
    have h1 := ih hu hz
    have h2 := wordMap_dist_le n v hzy hy
    exact (dist_triangle x z y).trans (by push_cast; linarith)

end CarpetEnergy
