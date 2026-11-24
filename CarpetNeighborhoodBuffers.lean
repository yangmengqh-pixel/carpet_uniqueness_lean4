import CarpetNeighborhoodRescaling

/-!
# Metric buffers between cell neighborhoods

Cells containing points at distance strictly less than a level's
grid width are neighbors. A sufficiently fine neighborhood centered
on any point of a coarser neighborhood stays inside the next coarser
neighborhood's open part.
-/

open Filter Function Set
open scoped Topology

namespace CarpetEnergy

theorem gridNear_of_dist_lt_word_width {n : ℕ} {u v : Fin n → Fin 8}
    {x y : CarpetPoints} (hx : x ∈ range (wordMap (List.ofFn u)))
    (hy : y ∈ range (wordMap (List.ofFn v))) (h : dist x y < (1 / 3 : ℝ) ^ n) :
    GridNear (List.ofFn u) (List.ofFn v) := by
  have hcoord {u v : Fin n → Fin 8} {x y : CarpetPoints}
      (hx : x ∈ range (wordMap (List.ofFn u))) (hy : y ∈ range (wordMap (List.ofFn v)))
      (h : dist x y < (1 / 3 : ℝ) ^ n) (j : Fin 2) :
      gridCoordinate (List.ofFn u) j ≤ gridCoordinate (List.ofFn v) j + 1 := by
    have h₁ := (gridCoordinate_bounds hx j).1
    have h₂ := (gridCoordinate_bounds hy j).2
    have hd := (PiLp.dist_apply_le (x : Plane) (y : Plane) j).trans_lt h
    rw [Real.dist_eq] at hd
    have hxy := (abs_lt.mp hd).2
    have hpos : 0 < (3 : ℝ) ^ n := by positivity
    have hm := mul_lt_mul_of_pos_left hxy hpos
    have hp : (3 : ℝ) ^ n * ((1 / 3 : ℝ) ^ n) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hp, mul_sub] at hm
    have hh : (gridCoordinate (List.ofFn u) j : ℝ) <
        (gridCoordinate (List.ofFn v) j : ℝ) + 2 := by linarith only [h₁, h₂, hm]
    have hh' : gridCoordinate (List.ofFn u) j < gridCoordinate (List.ofFn v) j + 2 := by
      exact_mod_cast hh
    omega
  exact fun j ↦ ⟨hcoord hx hy h j, hcoord hy hx (dist_comm x y ▸ h) j⟩

/-- A ball of the level's grid width about a point of a neighborhood
lies in the open part of the next neighborhood. -/
theorem wordNeighborhood_thickening_subset_open_succ {n k : ℕ} (w : Fin n → Fin 8)
    {x : CarpetPoints} (hx : x ∈ wordCellUnion (cellNeighborhood w k)) :
    Metric.ball x ((1 / 3 : ℝ) ^ n) ⊆ wordNeighborhoodOpen w (k + 1) := by
  intro y hy hn
  obtain ⟨u, hu⟩ := mem_iUnion.mp hx
  obtain ⟨huN, hxu⟩ := mem_iUnion.mp hu
  obtain ⟨v, hv⟩ := mem_iUnion.mp hn
  obtain ⟨hvN, hyv⟩ := mem_iUnion.mp hv
  have hxy : dist x y < (1 / 3 : ℝ) ^ n := dist_comm y x ▸ hy
  have hnear := gridNear_of_dist_lt_word_width hxu hyv hxy
  have hv' : v ∈ cellNeighborhood w (k + 1) := mem_cellNeighborhood_succ.mpr
    ⟨u, huN, (gridNear_iff_inter_wordMap_nonempty (by simp)).mp hnear⟩
  exact (Finset.mem_sdiff.mp hvN).2 hv'

theorem fine_wordNeighborhood_subset_open_succ {n m k j : ℕ} (w : Fin n → Fin 8)
    (v : Fin m → Fin 8) {x : CarpetPoints}
    (hx : x ∈ wordCellUnion (cellNeighborhood w k)) (hv : x ∈ range (wordMap (List.ofFn v)))
    (h : ((j : ℝ) + 1) * ((1 / 3 : ℝ) ^ m * Metric.diam (univ : Set CarpetPoints)) <
      (1 / 3 : ℝ) ^ n) :
    wordCellUnion (cellNeighborhood v j) ⊆ wordNeighborhoodOpen w (k + 1) := by
  intro y hy
  obtain ⟨a, ha⟩ := mem_iUnion.mp hy
  obtain ⟨haN, hay⟩ := mem_iUnion.mp ha
  apply wordNeighborhood_thickening_subset_open_succ w hx
  rw [Metric.mem_ball, dist_comm]
  exact (dist_le_of_mem_cellNeighborhood haN hv hay).trans_lt h

theorem exists_uniform_wordNeighborhood_stride :
    ∃ L : ℕ, 0 < L ∧ ∀ n : ℕ,
      4 * ((1 / 3 : ℝ) ^ (n + L) * Metric.diam (univ : Set CarpetPoints)) <
        (1 / 3 : ℝ) ^ n := by
  have hlim := tendsto_wordMap_radius.const_mul (4 : ℝ)
  have h' := hlim.eventually_lt_const (by norm_num : (4 : ℝ) * 0 < 1)
  obtain ⟨L, hL⟩ := (((eventually_ge_atTop (1 : ℕ)).and h')).exists
  refine ⟨L, hL.1, fun n ↦ ?_⟩
  rw [pow_add]
  calc
    _ = (1 / 3 : ℝ) ^ n * (4 * ((1 / 3 : ℝ) ^ L * Metric.diam (univ : Set CarpetPoints))) := by ring
    _ < (1 / 3 : ℝ) ^ n * 1 := mul_lt_mul_of_pos_left hL.2 (by positivity)
    _ = _ := mul_one _

/-- Choose one level cell containing a point. -/
noncomputable def centerWord (n : ℕ) (x : CarpetPoints) : Fin n → Fin 8 :=
  (exists_wordMap_range n x).choose

theorem mem_centerWord (n : ℕ) (x : CarpetPoints) :
    x ∈ range (wordMap (List.ofFn (centerWord n x))) :=
  (exists_wordMap_range n x).choose_spec

theorem mem_wordCellUnion_centerWord (n k : ℕ) (x : CarpetPoints) :
    x ∈ wordCellUnion (cellNeighborhood (centerWord n x) k) :=
  mem_iUnion.mpr ⟨centerWord n x, mem_iUnion.mpr
    ⟨self_mem_cellNeighborhood (centerWord n x) k, mem_centerWord n x⟩⟩

theorem fine_centerWord_neighborhood_subset (n L : ℕ) (x : CarpetPoints)
    (hL : 4 * ((1 / 3 : ℝ) ^ (n + L) * Metric.diam (univ : Set CarpetPoints)) <
      (1 / 3 : ℝ) ^ n) :
    wordCellUnion (cellNeighborhood (centerWord (n + L) x) 3) ⊆
      wordCellUnion (cellNeighborhood (centerWord n x) 2) := by
  refine Subset.trans (fine_wordNeighborhood_subset_open_succ (k := 1) (j := 3)
    (centerWord n x) (centerWord (n + L) x) (mem_wordCellUnion_centerWord n 1 x)
    (mem_centerWord (n + L) x) ?_) (wordNeighborhoodOpen_subset (centerWord n x))
  norm_num at hL ⊢
  exact hL

theorem ball_subset_centerWord_neighborhood (n : ℕ) (x : CarpetPoints) :
    Metric.ball x ((1 / 3 : ℝ) ^ n) ⊆ wordCellUnion (cellNeighborhood (centerWord n x) 2) :=
  (wordNeighborhood_thickening_subset_open_succ (centerWord n x)
    (mem_wordCellUnion_centerWord n 1 x)).trans (wordNeighborhoodOpen_subset (centerWord n x))

theorem dist_centerWord_neighborhood (n k : ℕ) (x : CarpetPoints) {y : CarpetPoints}
    (hy : y ∈ wordCellUnion (cellNeighborhood (centerWord n x) k)) :
    dist y x ≤ ((k : ℝ) + 1) * ((1 / 3 : ℝ) ^ n * Metric.diam (univ : Set CarpetPoints)) := by
  obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
  rw [dist_comm]
  exact dist_le_of_mem_cellNeighborhood hv (mem_centerWord n x) hyv

end CarpetEnergy
