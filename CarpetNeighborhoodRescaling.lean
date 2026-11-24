import CarpetNeighborhoodShape
import CarpetNeighborhoodMass

/-!
# Rescaling and interior nesting of word neighborhoods
-/

open Function Set

namespace CarpetEnergy

theorem isClosed_wordCellUnion {n : ℕ} (A : Finset (Fin n → Fin 8)) :
    IsClosed (wordCellUnion A) :=
  isClosed_biUnion_finset fun w _ ↦ (isCompact_range (continuous_wordMap (List.ofFn w))).isClosed

/-- The open part of a neighborhood obtained by removing all cells
outside it, including their intersections with the neighborhood. -/
noncomputable def wordNeighborhoodOpen {n : ℕ} (w : Fin n → Fin 8) (r : ℕ) : Set CarpetPoints :=
  (wordCellUnion (Finset.univ \ cellNeighborhood w r))ᶜ

theorem isOpen_wordNeighborhoodOpen {n : ℕ} (w : Fin n → Fin 8) (r : ℕ) :
    IsOpen (wordNeighborhoodOpen w r) := (isClosed_wordCellUnion _).isOpen_compl

theorem wordNeighborhoodOpen_subset {n r : ℕ} (w : Fin n → Fin 8) :
    wordNeighborhoodOpen w r ⊆ wordCellUnion (cellNeighborhood w r) := by
  intro x hx
  obtain ⟨v, hv⟩ := exists_wordMap_range n x
  by_cases h : v ∈ cellNeighborhood w r
  · exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨h, hv⟩⟩
  · exact False.elim (hx (mem_iUnion.mpr ⟨v, mem_iUnion.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩, hv⟩⟩))

theorem wordMap_notMem_wordNeighborhoodOpen {n r : ℕ} {w v : Fin n → Fin 8}
    (hv : v ∉ cellNeighborhood w r) (x : CarpetPoints) :
    wordMap (List.ofFn v) x ∉ wordNeighborhoodOpen w r := by
  intro hx
  exact hx (mem_iUnion.mpr ⟨v, mem_iUnion.mpr
    ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩, mem_range_self x⟩⟩)

theorem wordCellUnion_neighborhood_subset_open_succ {n r : ℕ} (w : Fin n → Fin 8) :
    wordCellUnion (cellNeighborhood w r) ⊆ wordNeighborhoodOpen w (r + 1) := by
  intro x hx hn
  obtain ⟨a, ha⟩ := mem_iUnion.mp hx
  obtain ⟨haA, ha⟩ := mem_iUnion.mp ha
  obtain ⟨c, hc⟩ := mem_iUnion.mp hn
  obtain ⟨hcC, hc⟩ := mem_iUnion.mp hc
  have hcB : c ∈ cellNeighborhood w (r + 1) := mem_cellNeighborhood_succ.mpr ⟨a, haA, x, ha, hc⟩
  exact (Finset.mem_sdiff.mp hcC).2 hcB

/-- Every point in a neighborhood lies in the relative interior of
the next neighborhood. A cell from the finite complement cannot
touch a cell in the smaller neighborhood. -/
theorem wordCellUnion_neighborhood_subset_interior_succ {n r : ℕ} (w : Fin n → Fin 8) :
    wordCellUnion (cellNeighborhood w r) ⊆ interior (wordCellUnion (cellNeighborhood w (r + 1))) :=
  (wordCellUnion_neighborhood_subset_open_succ w).trans
    (interior_maximal (wordNeighborhoodOpen_subset w) (isOpen_wordNeighborhoodOpen w _))

/-- The affine rescaling that identifies corresponding grid positions
in the neighborhoods centered at two possibly different levels. -/
noncomputable def neighborhoodRescale {n m : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (x : Plane) : Plane :=
  WithLp.toLp 2 fun i ↦ ((3 : ℝ) ^ n * x i - (gridCoordinate (List.ofFn w) i : ℝ) +
    (gridCoordinate (List.ofFn u) i : ℝ)) / (3 : ℝ) ^ m

theorem continuous_neighborhoodRescale {n m : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8) :
    Continuous (neighborhoodRescale w u) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  exact (((continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) i)).sub
    continuous_const).add continuous_const).div_const _

theorem neighborhoodRescale_wordMap {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r)
    (v : {v // v ∈ cellNeighborhood w r}) (x : CarpetPoints) :
    neighborhoodRescale w u (wordMap (List.ofFn v.val) x) =
      (wordMap (List.ofFn (neighborhoodEquiv w u h v).val) x : Plane) := by
  ext i
  change ((3 : ℝ) ^ n * (wordMap (List.ofFn v.val) x : Plane) i -
    (gridCoordinate (List.ofFn w) i : ℝ) + (gridCoordinate (List.ofFn u) i : ℝ)) /
    (3 : ℝ) ^ m = _
  apply (div_eq_iff (by positivity : (3 : ℝ) ^ m ≠ 0)).mpr
  have hh := neighborhoodEquiv_scaled_coord w u h v x i
  rw [mul_comm _ ((3 : ℝ) ^ m)]
  linarith only [hh]

/-- Equal shapes have homeomorphic neighborhood unions. On each cell
the homeomorphism preserves the carpet parameter before applying the
corresponding cell embedding. -/
noncomputable def neighborhoodHomeomorph {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r) :
    wordCellUnion (cellNeighborhood w r) ≃ₜ wordCellUnion (cellNeighborhood u r) := by
  let S := wordCellUnion (cellNeighborhood w r)
  let T := wordCellUnion (cellNeighborhood u r)
  have hmap {a b : ℕ} (s : Fin a → Fin 8) (t : Fin b → Fin 8)
      (he : neighborhoodShape s r = neighborhoodShape t r)
      (y : wordCellUnion (cellNeighborhood s r)) :
      ∃ z : wordCellUnion (cellNeighborhood t r),
        (z.val : Plane) = neighborhoodRescale s t y.val := by
    obtain ⟨v, hv⟩ := mem_iUnion.mp y.property
    obtain ⟨hvr, x, hx⟩ := mem_iUnion.mp hv
    let a := neighborhoodEquiv s t he ⟨v, hvr⟩
    refine ⟨⟨wordMap (List.ofFn a.val) x,
      mem_iUnion.mpr ⟨a.val, mem_iUnion.mpr ⟨a.property, mem_range_self x⟩⟩⟩, ?_⟩
    rw [← hx]
    exact (neighborhoodRescale_wordMap s t he ⟨v, hvr⟩ x).symm
  let f (x : S) : T := (hmap w u h x).choose
  let g (y : T) : S := (hmap u w h.symm y).choose
  have hf (x : S) : ((f x).val : Plane) = neighborhoodRescale w u x.val :=
    (hmap w u h x).choose_spec
  have hg (y : T) : ((g y).val : Plane) = neighborhoodRescale u w y.val :=
    (hmap u w h.symm y).choose_spec
  have hinv {a b : ℕ} (s : Fin a → Fin 8) (t : Fin b → Fin 8) (x : Plane) :
      neighborhoodRescale t s (neighborhoodRescale s t x) = x := by
    ext i
    change ((3 : ℝ) ^ b * (((3 : ℝ) ^ a * x i - (gridCoordinate (List.ofFn s) i : ℝ) +
        (gridCoordinate (List.ofFn t) i : ℝ)) / (3 : ℝ) ^ b) -
        (gridCoordinate (List.ofFn t) i : ℝ) + (gridCoordinate (List.ofFn s) i : ℝ)) /
        (3 : ℝ) ^ a = x i
    have ha : (3 : ℝ) ^ a ≠ 0 := by positivity
    have hb : (3 : ℝ) ^ b ≠ 0 := by positivity
    field_simp [ha, hb]
    ring
  refine
    { toFun := f
      invFun := g
      left_inv := fun x ↦ Subtype.ext (Subtype.ext (by rw [hg, hf, hinv]))
      right_inv := fun y ↦ Subtype.ext (Subtype.ext (by rw [hf, hg, hinv]))
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    show Continuous (fun x ↦ ((f x).val : Plane))
    simp only [hf]
    exact (continuous_neighborhoodRescale w u).comp (continuous_subtypeVal.comp continuous_subtypeVal)
  · apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    show Continuous (fun y ↦ ((g y).val : Plane))
    simp only [hg]
    exact (continuous_neighborhoodRescale u w).comp (continuous_subtypeVal.comp continuous_subtypeVal)

end CarpetEnergy
