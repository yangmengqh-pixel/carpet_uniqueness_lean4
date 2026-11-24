import CarpetMeasure
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.LocallyFinite

/-!
# Connectedness of the carpet

Adjacent first-level cells share a corner. A clopen separation would color
all sufficiently small cells by its two sides. Corner overlaps force sibling
cells to have the same color, and this propagates to the whole carpet.
-/

open Filter Function Metric Set
open scoped Topology

namespace CarpetEnergy

/-- The similarity associated with a finite word is continuous on the carpet. -/
theorem continuous_wordMap (w : List (Fin 8)) : Continuous (wordMap w) := by
  induction w with
  | nil => exact continuous_id
  | cons i w ih => exact (continuous_cellMap i).comp ih

private theorem wordMap_append_singleton (w : List (Fin 8)) (i : Fin 8) :
    wordMap (w ++ [i]) = wordMap w ∘ cellMap i := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (cellMap a ∘ ·) ih

private theorem exists_cell_range (x : CarpetPoints) :
    ∃ i : Fin 8, x ∈ range (cellMap i) := by
  obtain ⟨i, y, hy, heq⟩ := mem_iUnion.mp (carpet_eq_iUnion.le x.property)
  exact ⟨i, ⟨y, hy⟩, Subtype.ext heq⟩

private theorem center_mem_carpet (i : Fin 8) : cellCenter i ∈ (carpet : Set Plane) := by
  let s : Addresses := fun _ ↦ i
  have hs : prepend i s = s := by funext n; cases n <;> rfl
  have h := coding_prepend i s
  rw [hs] at h
  have hcoord (j : Fin 2) : (coding s : Plane) j = cellCenter i j := by
    have hj : (coding s : Plane) j = cellSimilarity i (coding s) j :=
      congrArg (fun x : CarpetPoints ↦ (x : Plane) j) h
    rw [cellSimilarity_coord] at hj
    linarith only [hj]
  have heq : (coding s : Plane) = cellCenter i := by ext j; exact hcoord j
  exact heq ▸ (coding s).property

private theorem consecutive_cells_intersect (i : Fin 7) :
    (range (cellMap i.castSucc) ∩ range (cellMap i.succ)).Nonempty := by
  let a : Fin 7 → Fin 8 := ![2, 2, 4, 4, 6, 6, 0]
  let b : Fin 7 → Fin 8 := ![0, 0, 2, 2, 4, 4, 6]
  let x : CarpetPoints := ⟨cellCenter (a i), center_mem_carpet (a i)⟩
  let y : CarpetPoints := ⟨cellCenter (b i), center_mem_carpet (b i)⟩
  refine ⟨cellMap i.castSucc x, mem_range_self x, y, ?_⟩
  apply Subtype.ext
  ext j
  change cellSimilarity i.succ (cellCenter (b i)) j =
    cellSimilarity i.castSucc (cellCenter (a i)) j
  simp only [cellSimilarity_coord]
  fin_cases i <;> fin_cases j <;>
    norm_num [a, b, cellCenter, WithLp.toLp, Fin.reduceFinMk, Fin.succ, Fin.castSucc]

private theorem parent_range_subset_of_sides (w : List (Fin 8)) (U : Set CarpetPoints)
    (h : ∀ i : Fin 8, range (wordMap (w ++ [i])) ⊆ U ∨ range (wordMap (w ++ [i])) ⊆ Uᶜ) :
    range (wordMap w) ⊆ U ∨ range (wordMap w) ⊆ Uᶜ := by
  have inter (i : Fin 7) :
      (range (wordMap (w ++ [i.castSucc])) ∩ range (wordMap (w ++ [i.succ]))).Nonempty := by
    obtain ⟨x, ⟨a, ha⟩, ⟨b, hb⟩⟩ := consecutive_cells_intersect i
    rw [wordMap_append_singleton, wordMap_append_singleton]
    exact ⟨wordMap w x, ⟨a, congrArg (wordMap w) ha⟩, ⟨b, congrArg (wordMap w) hb⟩⟩
  have grow (S : Set CarpetPoints)
      (hs : ∀ i : Fin 8, range (wordMap (w ++ [i])) ⊆ S ∨ range (wordMap (w ++ [i])) ⊆ Sᶜ)
      (h0 : range (wordMap (w ++ [0])) ⊆ S) : range (wordMap w) ⊆ S := by
    have hall (i : Fin 8) : range (wordMap (w ++ [i])) ⊆ S := by
      induction i using Fin.induction with
      | zero => exact h0
      | succ i ih =>
        rcases hs i.succ with h₁ | h₁
        · exact h₁
        · obtain ⟨x, hx₁, hx₂⟩ := inter i
          exact (h₁ hx₂ (ih hx₁)).elim
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, y, hy⟩ := exists_cell_range x
    apply hall i
    rw [wordMap_append_singleton]
    exact ⟨y, congrArg (wordMap w) hy⟩
  rcases h 0 with h0 | h0
  · exact Or.inl (grow U h h0)
  · exact Or.inr (grow Uᶜ (fun i ↦ by simpa only [compl_compl] using (h i).symm) h0)

private theorem range_wordMap_le_diam (w : List (Fin 8)) {x y : CarpetPoints}
    (hx : x ∈ range (wordMap w)) (hy : y ∈ range (wordMap w)) :
    dist x y ≤ (1 / 3 : ℝ) ^ w.length * diam (univ : Set CarpetPoints) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [dist_wordMap]
  exact mul_le_mul_of_nonneg_left
    (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ a) (mem_univ b)) (by positivity)

/-- The Sierpiński carpet is preconnected. -/
instance : PreconnectedSpace CarpetPoints := by
  apply preconnectedSpace_iff_clopen.mpr
  intro U hU
  obtain ⟨ε, hε, hthick⟩ := hU.isClosed.isCompact.exists_thickening_subset_open hU.isOpen
    (Subset.rfl : U ⊆ U)
  obtain ⟨n, hn⟩ := (tendsto_wordMap_radius.eventually_lt_const hε).exists
  have hlevel : ∀ w : List (Fin 8), w.length = n → range (wordMap w) ⊆ U ∨
      range (wordMap w) ⊆ Uᶜ := by
    intro w hw
    by_cases h : (U ∩ range (wordMap w)).Nonempty
    · obtain ⟨x, hxU, hxw⟩ := h
      refine Or.inl fun y hy ↦ hthick (mem_thickening_iff.mpr ⟨x, hxU, ?_⟩)
      exact (range_wordMap_le_diam w hy hxw).trans_lt (hw.symm ▸ hn)
    · exact Or.inr fun x hx hxu ↦ h ⟨x, hxu, hx⟩
  have descend (n : ℕ) (h : ∀ w : List (Fin 8), w.length = n → range (wordMap w) ⊆ U ∨
      range (wordMap w) ⊆ Uᶜ) : range (wordMap []) ⊆ U ∨ range (wordMap []) ⊆ Uᶜ := by
    induction n with
    | zero => exact h [] rfl
    | succ n ih =>
      apply ih
      intro w hw
      apply parent_range_subset_of_sides w U
      intro i
      apply h
      rw [List.length_append, hw]
      rfl
  rcases descend n hlevel with h | h
  · exact Or.inr (eq_univ_of_forall fun x ↦ h (mem_range_self x))
  · exact Or.inl (eq_empty_iff_forall_notMem.mpr fun x ↦ h (mem_range_self x))

/-- Finite unions of small cells through a point give compact connected neighborhoods. -/
theorem exists_compact_preconnected_mem_nhds (x : CarpetPoints)
    {U : Set CarpetPoints} (hxU : U ∈ 𝓝 x) :
    ∃ V ∈ 𝓝 x, IsCompact V ∧ IsPreconnected V ∧ V ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hxU
  obtain ⟨n, hn⟩ := (tendsto_wordMap_radius.eventually_lt_const hε).exists
  let K (w : Fin n → Fin 8) := range (wordMap (List.ofFn w))
  let V := ⋃ w : {w // x ∈ K w}, K w
  let W := ⋃ w : {w // x ∉ K w}, K w
  have hpre (w : Fin n → Fin 8) : IsPreconnected (K w) := by
    change IsPreconnected (range (wordMap (List.ofFn w)))
    rw [← image_univ]
    exact isPreconnected_univ.image _ (continuous_wordMap _).continuousOn
  have hW : IsClosed W := (locallyFinite_of_finite _).isClosed_iUnion fun w ↦
    (isCompact_range (continuous_wordMap (List.ofFn w.val))).isClosed
  have hxW : x ∉ W := fun hx ↦ by
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    exact w.property hw
  have hWV : Wᶜ ⊆ V := fun y hy ↦ by
    obtain ⟨w, hw⟩ := exists_wordMap_range n y
    by_cases hx : x ∈ K w
    · exact mem_iUnion.mpr ⟨⟨w, hx⟩, hw⟩
    · exact (hy (mem_iUnion.mpr ⟨⟨w, hx⟩, hw⟩)).elim
  refine ⟨V, Filter.mem_of_superset (hW.isOpen_compl.mem_nhds hxW) hWV, ?_, ?_, ?_⟩
  · exact isCompact_iUnion fun w ↦ isCompact_range (continuous_wordMap (List.ofFn w.val))
  · exact isPreconnected_iUnion ⟨x, mem_iInter.mpr fun w ↦ w.property⟩ fun w ↦ hpre w
  · intro y hy
    obtain ⟨w, hyw⟩ := mem_iUnion.mp hy
    exact hball (mem_ball.mpr ((wordMap_dist_le n w.val hyw w.property).trans_lt hn))

instance : LocallyConnectedSpace CarpetPoints := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro x U hxU
  obtain ⟨V, hV, _, hconn, hsub⟩ := exists_compact_preconnected_mem_nhds x hxU
  exact ⟨V, hV, hconn, hsub⟩

/-- Any two points of a connected open set in the carpet belong to a
compact connected subset of that open set. -/
theorem exists_compact_preconnected_subset_of_isOpen {U : Set CarpetPoints}
    (hU : IsOpen U) (hc : IsPreconnected U) {a b : CarpetPoints} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ V ⊆ U, IsCompact V ∧ IsPreconnected V ∧ a ∈ V ∧ b ∈ V := by
  let W : Set CarpetPoints := {x | ∃ V ⊆ U, IsCompact V ∧ IsPreconnected V ∧ a ∈ V ∧ x ∈ V}
  have hW : W ⊆ U := by
    rintro x ⟨V, hV, _, _, _, hx⟩
    exact hV hx
  have haW : a ∈ W := ⟨{a}, singleton_subset_iff.mpr ha, isCompact_singleton,
    isPreconnected_singleton, rfl, rfl⟩
  have hopenW : IsOpen W := isOpen_iff_mem_nhds.mpr fun x hx ↦ by
    obtain ⟨V, hV, hVc, hVp, haV, hxV⟩ := hx
    obtain ⟨B, hB, hBc, hBp, hBU⟩ := exists_compact_preconnected_mem_nhds x (hU.mem_nhds (hV hxV))
    refine Filter.mem_of_superset hB fun y hy ↦ ?_
    exact ⟨V ∪ B, union_subset hV hBU, hVc.union hBc,
      hVp.union x hxV (mem_of_mem_nhds hB) hBp, Or.inl haV, Or.inr hy⟩
  have hopen' : IsOpen (U \ W) := isOpen_iff_mem_nhds.mpr fun x hx ↦ by
    obtain ⟨B, hB, hBc, hBp, hBU⟩ := exists_compact_preconnected_mem_nhds x (hU.mem_nhds hx.1)
    refine Filter.mem_of_superset hB fun y hy ↦ ⟨hBU hy, ?_⟩
    rintro ⟨V, hV, hVc, hVp, haV, hyV⟩
    exact hx.2 ⟨V ∪ B, union_subset hV hBU, hVc.union hBc,
      hVp.union y hyV hy hBp, Or.inl haV, Or.inr (mem_of_mem_nhds hB)⟩
  have hcov : U ⊆ W ∪ (U \ W) := fun x hx ↦ by
    by_cases hw : x ∈ W
    · exact Or.inl hw
    · exact Or.inr ⟨hx, hw⟩
  rcases hc.subset_or_subset hopenW hopen' disjoint_sdiff_right hcov with h | h
  · exact h hb
  · exact False.elim ((h ha).2 haW)

end CarpetEnergy
