import CarpetBoundary
import CarpetConnected
import Mathlib.Topology.Separation.Regular

/-!
# Connected crossings in first-level cells

A compact subset of a side cell can be separated into two compact pieces
when none of its connected components meets both connection sides.
-/

open Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

private theorem exists_clopen_disjoint_of_component_disjoint
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {B : Set X} (hB : IsCompact B) {a : X} (ha : Disjoint B (connectedComponent a)) :
    ∃ U : Set X, IsClopen U ∧ a ∈ U ∧ Disjoint B U := by
  rw [connectedComponent_eq_iInter_isClopen a] at ha
  let S := {s : Set X // IsClopen s ∧ a ∈ s}
  obtain ⟨J, hJ⟩ := hB.elim_finite_subfamily_closed
    (fun s : S ↦ s.val) (fun s ↦ s.property.1.1) ha
  refine ⟨⋂ s ∈ J, s.val, isClopen_biInter_finset (fun s _ ↦ s.property.1), ?_, hJ⟩
  exact mem_iInter₂.mpr fun s _ ↦ s.property.2

private theorem exists_clopen_separation
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (h : ∀ a ∈ A, Disjoint B (connectedComponent a)) :
    ∃ U : Set X, IsClopen U ∧ A ⊆ U ∧ Disjoint B U := by
  classical
  choose V hVc hVa hVB using fun a : A ↦ exists_clopen_disjoint_of_component_disjoint hB (h a a.property)
  have hcov : A ⊆ ⋃ a, V a := fun a ha ↦ mem_iUnion.mpr ⟨⟨a, ha⟩, hVa ⟨a, ha⟩⟩
  obtain ⟨J, hJ⟩ := hA.elim_finite_subcover V (fun a ↦ (hVc a).2) hcov
  refine ⟨⋃ a ∈ J, V a, isClopen_biUnion_finset (fun a _ ↦ hVc a), hJ, ?_⟩
  exact Set.disjoint_left.mpr fun x hx hV ↦ by
    obtain ⟨a, _, ha⟩ := mem_iUnion₂.mp hV
    exact Set.disjoint_left.mp (hVB a) hx ha

/-- If no connected component of a compact set meets two designated closed
subsets, it splits into compact pieces containing those subsets. -/
theorem exists_compact_partition_of_no_crossing
    {X : Type*} [TopologicalSpace X] [T2Space X] {K L R : Set X}
    (hK : IsCompact K) (hL : IsClosed L) (hR : IsClosed R)
    (h : ∀ l ∈ K ∩ L, ∀ r ∈ K ∩ R, r ∉ connectedComponentIn K l) :
    ∃ U V : Set X, IsCompact U ∧ IsCompact V ∧ Disjoint U V ∧
      U ∪ V = K ∧ K ∩ L ⊆ U ∧ K ∩ R ⊆ V := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let L' : Set K := Subtype.val ⁻¹' L
  let R' : Set K := Subtype.val ⁻¹' R
  have hLc : IsCompact L' := (hL.preimage continuous_subtypeVal).isCompact
  have hRc : IsCompact R' := (hR.preimage continuous_subtypeVal).isCompact
  have hd (l : K) (hl : l ∈ L') : Disjoint R' (connectedComponent l) := by
    apply Set.disjoint_left.mpr
    intro r hr hrl
    exact h l.val ⟨l.property, hl⟩ r.val ⟨r.property, hr⟩
      (connectedComponentIn_eq_image l.property ▸ mem_image_of_mem Subtype.val hrl)
  obtain ⟨W, hWc, hWL, hWR⟩ := exists_clopen_separation hLc hRc hd
  refine ⟨Subtype.val '' W, Subtype.val '' Wᶜ,
    hWc.1.isCompact.image continuous_subtypeVal, hWc.compl.1.isCompact.image continuous_subtypeVal,
    Set.disjoint_image_of_injective Subtype.val_injective disjoint_compl_right, ?_, ?_, ?_⟩
  · rw [← image_union, union_compl_self, image_univ, Subtype.range_coe]
  · exact fun x hx ↦ ⟨⟨x, hx.1⟩, hWL hx.2, rfl⟩
  · exact fun x hx ↦ ⟨⟨x, hx.1⟩, fun hxW ↦ Set.disjoint_left.mp hWR hx.2 hxW, rfl⟩

/-- The four corner cells in cyclic order. -/
def cornerCell (i : Fin 4) : Fin 8 := ⟨2 * i.val, by omega⟩

/-- The side cell between the i-th corner and its successor. -/
def sideCell (i : Fin 4) : Fin 8 := ⟨2 * i.val + 1, by omega⟩

/-- The corner attached to one of a side cell's two connection faces. -/
def sideCorner (i : Fin 4) (r : Fin 2) : Fin 4 := i + ⟨r.val, by omega⟩

/-- The axis parallel to the two-corner direction of a side cell. -/
def sideAxis (i : Fin 4) : Fin 2 := ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩

private def sideFaceDigit (i : Fin 4) (r : Fin 2) : ℕ :=
  if i.val < 2 then 1 + r.val else 2 - r.val

/-- A connection face of the side cell, in the ambient carpet. -/
def sideFace (i : Fin 4) (r : Fin 2) : Set CarpetPoints :=
  {x | 3 * (x : Plane) (sideAxis i) = sideFaceDigit i r}

theorem isClosed_sideFace (i : Fin 4) (r : Fin 2) : IsClosed (sideFace i r) := by
  apply isClosed_eq _ continuous_const
  exact continuous_const.mul
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) (sideAxis i)).comp continuous_subtypeVal)

/-- The portion of a cell in the interior of its ambient square. -/
def cellOpenPart (i : Fin 8) : Set CarpetPoints :=
  {x | ∀ j : Fin 2, ((cellDigit i j : ℕ) : ℝ) < 3 * (x : Plane) j ∧
    3 * (x : Plane) j < ((cellDigit i j : ℕ) : ℝ) + 1}

theorem isOpen_cellOpenPart (i : Fin 8) : IsOpen (cellOpenPart i) := by
  rw [show cellOpenPart i = ⋂ j : Fin 2,
    {x : CarpetPoints | ((cellDigit i j : ℕ) : ℝ) < 3 * (x : Plane) j ∧
      3 * (x : Plane) j < ((cellDigit i j : ℕ) : ℝ) + 1} by
    ext x
    simp only [cellOpenPart, mem_ofPred_eq, mem_iInter]]
  apply isOpen_iInter_of_finite
  intro j
  have h : Continuous (fun x : CarpetPoints ↦ 3 * (x : Plane) j) := continuous_const.mul
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) j).comp continuous_subtypeVal)
  exact (isOpen_lt (f := fun _ ↦ ((cellDigit i j : ℕ) : ℝ)) continuous_const h).inter
    (isOpen_lt h (continuous_const (y := ((cellDigit i j : ℕ) : ℝ) + 1)))

private theorem cell_coordinate_bounds {i : Fin 8} {x : CarpetPoints} (hx : x ∈ range (cellMap i))
    (j : Fin 2) : ((cellDigit i j : ℕ) : ℝ) ≤ 3 * (x : Plane) j ∧
      3 * (x : Plane) j ≤ ((cellDigit i j : ℕ) : ℝ) + 1 := by
  obtain ⟨y, rfl⟩ := hx
  change _ ≤ 3 * cellSimilarity i y j ∧ 3 * cellSimilarity i y j ≤ _
  rw [cellSimilarity_coord, ← cellDigit_cast]
  have h := carpet_coord_mem_Icc y j
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem cellOpenPart_disjoint_other_cell {i j : Fin 8} (h : i ≠ j) :
    Disjoint (cellOpenPart i) (range (cellMap j)) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hne : cellDigit i ≠ cellDigit j := fun he ↦ h (cellDigit_injective he)
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hne
  have hi := hxi q
  have hj := cell_coordinate_bounds hxj q
  rcases lt_or_gt_of_ne (show (cellDigit i q : ℕ) ≠ (cellDigit j q : ℕ) from
    fun he ↦ hq (Fin.ext he)) with hlt | hlt
  · have hle : (((cellDigit i q : ℕ) + 1 : ℕ) : ℝ) ≤ (cellDigit j q : ℕ) := by
      exact_mod_cast hlt
    push_cast at hle
    linarith [hi.2, hj.1]
  · have hle : (((cellDigit j q : ℕ) + 1 : ℕ) : ℝ) ≤ (cellDigit i q : ℕ) := by
      exact_mod_cast hlt
    push_cast at hle
    linarith [hi.1, hj.2]

private theorem exists_cellMap_range (x : CarpetPoints) :
    ∃ i : Fin 8, x ∈ range (cellMap i) := by
  obtain ⟨i, y, hy, heq⟩ := mem_iUnion.mp (carpet_eq_iUnion.le x.property)
  exact ⟨i, ⟨y, hy⟩, Subtype.ext heq⟩

theorem cellOpenPart_subset_cell (i : Fin 8) : cellOpenPart i ⊆ range (cellMap i) := by
  intro x hx
  obtain ⟨j, hj⟩ := exists_cellMap_range x
  by_cases h : i = j
  · rwa [h]
  · exact False.elim (Set.disjoint_left.mp (cellOpenPart_disjoint_other_cell h) hx hj)

/-- The cell interior has the same reference mass as its closed cell. -/
theorem carpetMeasure_cellOpenPart (i : Fin 8) :
    carpetMeasure (cellOpenPart i) = (8 : ℝ≥0∞)⁻¹ := by
  have hnull : carpetMeasure (range (cellMap i) \ cellOpenPart i) = 0 := by
    let B (j : Fin 2) : Set CarpetPoints :=
      {x | (x : Plane) j = ((cellDigit i j : ℕ) : ℝ) / 3} ∪
      {x | (x : Plane) j = (((cellDigit i j : ℕ) : ℝ) + 1) / 3}
    have hB (j : Fin 2) : carpetMeasure (B j) = 0 :=
      measure_union_null (carpetMeasure_coordinateLevel _ _) (carpetMeasure_coordinateLevel _ _)
    apply measure_mono_null ?_ (measure_iUnion_null hB)
    intro x hx
    have hn : ¬ ∀ j : Fin 2, ((cellDigit i j : ℕ) : ℝ) < 3 * (x : Plane) j ∧
        3 * (x : Plane) j < ((cellDigit i j : ℕ) : ℝ) + 1 := hx.2
    obtain ⟨j, hj⟩ := not_forall.mp hn
    have hb := cell_coordinate_bounds hx.1 j
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rcases not_and_or.mp hj with hj | hj
    · exact Or.inl (show (x : Plane) j = _ by linarith [hb.1, not_lt.mp hj])
    · exact Or.inr (show (x : Plane) j = _ by linarith [hb.2, not_lt.mp hj])
  have he := measure_inter_add_sdiff (μ := carpetMeasure) (range (cellMap i))
    (isOpen_cellOpenPart i).measurableSet
  rw [inter_eq_right.mpr (cellOpenPart_subset_cell i), hnull, add_zero] at he
  rw [he, ← image_univ, carpetMeasure_image_cellMap i MeasurableSet.univ, measure_univ, mul_one]

private def boxesMeet (i j : Fin 8) : Prop :=
  ∀ q : Fin 2, (cellDigit i q : ℕ) ≤ (cellDigit j q : ℕ) + 1 ∧
    (cellDigit j q : ℕ) ≤ (cellDigit i q : ℕ) + 1

private instance (i j : Fin 8) : Decidable (boxesMeet i j) :=
  inferInstanceAs (Decidable (∀ q : Fin 2, (cellDigit i q : ℕ) ≤ (cellDigit j q : ℕ) + 1 ∧
    (cellDigit j q : ℕ) ≤ (cellDigit i q : ℕ) + 1))

private theorem boxesMeet_of_mem_inter {i j : Fin 8} {x : CarpetPoints}
    (hi : x ∈ range (cellMap i)) (hj : x ∈ range (cellMap j)) : boxesMeet i j := by
  intro q
  obtain ⟨hil, hiu⟩ := cell_coordinate_bounds hi q
  obtain ⟨hjl, hju⟩ := cell_coordinate_bounds hj q
  exact ⟨by exact_mod_cast hil.trans hju, by exact_mod_cast hjl.trans hiu⟩

private def boxesFix (i j : Fin 8) (q : Fin 2) (d : ℕ) : Prop :=
  ((cellDigit i q : ℕ) = d ∨ (cellDigit j q : ℕ) = d) ∧
    ((cellDigit i q : ℕ) + 1 = d ∨ (cellDigit j q : ℕ) + 1 = d)

private instance (i j : Fin 8) (q : Fin 2) (d : ℕ) : Decidable (boxesFix i j q d) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem boxesFix_eq_of_mem_inter {i j : Fin 8} {q : Fin 2} {d : ℕ} {x : CarpetPoints}
    (h : boxesFix i j q d) (hi : x ∈ range (cellMap i)) (hj : x ∈ range (cellMap j)) :
    3 * (x : Plane) q = d := by
  obtain ⟨hil, hiu⟩ := cell_coordinate_bounds hi q
  obtain ⟨hjl, hju⟩ := cell_coordinate_bounds hj q
  have hlo : (d : ℝ) ≤ 3 * (x : Plane) q := by
    rcases h.1 with hl | hl
    · exact_mod_cast (hl ▸ hil)
    · exact_mod_cast (hl ▸ hjl)
  have hhi : 3 * (x : Plane) q ≤ (d : ℝ) := by
    rcases h.2 with hu | hu
    · have hu' : ((cellDigit i q : ℕ) : ℝ) + 1 = d := by exact_mod_cast hu
      exact hiu.trans_eq hu'
    · have hu' : ((cellDigit j q : ℕ) : ℝ) + 1 = d := by exact_mod_cast hu
      exact hju.trans_eq hu'
  exact hhi.antisymm hlo

private def boxCornerContact (i j : Fin 8) (k : Fin 4) : Prop :=
  i = cornerCell k ∨ ∃ (s : Fin 4) (r : Fin 2), i = sideCell s ∧ k = sideCorner s r ∧
    boxesFix i j (sideAxis s) (sideFaceDigit s r)

private instance (i j : Fin 8) (k : Fin 4) : Decidable (boxCornerContact i j k) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem exists_boxCornerContact :
    ∀ i j : Fin 8, i ≠ j → boxesMeet i j →
      ∃ k : Fin 4, boxCornerContact i j k ∧ boxCornerContact j i k := by decide

private def cellCornerContact (i : Fin 8) (k : Fin 4) (x : CarpetPoints) : Prop :=
  i = cornerCell k ∨ ∃ (s : Fin 4) (r : Fin 2), i = sideCell s ∧ k = sideCorner s r ∧
    x ∈ sideFace s r

private theorem exists_cellCornerContact {i j : Fin 8} {x : CarpetPoints} (hne : i ≠ j)
    (hi : x ∈ range (cellMap i)) (hj : x ∈ range (cellMap j)) :
    ∃ k, cellCornerContact i k x ∧ cellCornerContact j k x := by
  obtain ⟨k, hik, hjk⟩ := exists_boxCornerContact i j hne (boxesMeet_of_mem_inter hi hj)
  have transfer {i j : Fin 8} (hx : x ∈ range (cellMap i)) (hy : x ∈ range (cellMap j))
      (h : boxCornerContact i j k) : cellCornerContact i k x := by
    rcases h with h | ⟨s, r, hs, hr, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, r, hs, hr, boxesFix_eq_of_mem_inter h hx hy⟩
  exact ⟨k, transfer hi hj hik, transfer hj hi hjk⟩

/-- A compact connected subset in a side cell that meets both connection faces. -/
def HasSideCrossing (A : Set CarpetPoints) (i : Fin 4) : Prop :=
  ∃ B ⊆ A ∩ range (cellMap (sideCell i)), IsCompact B ∧ IsPreconnected B ∧
    (B ∩ sideFace i 0).Nonempty ∧ (B ∩ sideFace i 1).Nonempty

private theorem compact_connectedComponentIn {K : Set CarpetPoints} (hK : IsCompact K)
    {x : CarpetPoints} (hx : x ∈ K) : IsCompact (connectedComponentIn K x) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtypeVal

private theorem exists_side_pieces {A : Set CarpetPoints} (hA : IsCompact A)
    (c : Fin 4 → Bool) (i : Fin 4)
    (hbad : c (sideCorner i 0) ≠ c (sideCorner i 1) → ¬ HasSideCrossing A i) :
    ∃ P : Fin 2 → Set CarpetPoints,
      (∀ r, IsCompact (P r)) ∧ P 0 ∪ P 1 = A ∩ range (cellMap (sideCell i)) ∧
      (∀ r, (A ∩ range (cellMap (sideCell i))) ∩ sideFace i r ⊆ P r) ∧
      (c (sideCorner i 0) ≠ c (sideCorner i 1) → Disjoint (P 0) (P 1)) := by
  let K := A ∩ range (cellMap (sideCell i))
  have hK : IsCompact K := hA.inter_right (isCompact_range (continuous_cellMap _)).isClosed
  by_cases he : c (sideCorner i 0) = c (sideCorner i 1)
  · exact ⟨fun _ ↦ K, fun _ ↦ hK, union_self _, fun _ ↦ inter_subset_left,
      fun h ↦ (h he).elim⟩
  have hnc : ∀ l ∈ K ∩ sideFace i 0, ∀ r ∈ K ∩ sideFace i 1, r ∉ connectedComponentIn K l := by
    intro l hl r hr hrl
    apply hbad he
    exact ⟨connectedComponentIn K l, connectedComponentIn_subset _ _,
      compact_connectedComponentIn hK hl.1, isPreconnected_connectedComponentIn,
      ⟨l, mem_connectedComponentIn hl.1, hl.2⟩, ⟨r, hrl, hr.2⟩⟩
  obtain ⟨L, R, hL, hR, hd, hcov, hl, hr⟩ :=
    exists_compact_partition_of_no_crossing hK (isClosed_sideFace i 0) (isClosed_sideFace i 1) hnc
  refine ⟨![L, R], ?_, hcov, ?_, fun _ ↦ hd⟩
  · intro r
    fin_cases r
    · exact hL
    · exact hR
  · intro r
    fin_cases r
    · exact hl
    · exact hr

private theorem exists_separating_corner_color :
    ∀ i j : Fin 4, i ≠ j → ∃ c : Fin 4 → Bool,
      (∃ k, c k = false) ∧ (∃ k, c k = true) ∧
      (∀ s, c (sideCorner s 0) ≠ c (sideCorner s 1) → s = i ∨ s = j) := by decide

private theorem cornerCell_injective : Injective cornerCell := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change 2 * i.val = 2 * j.val at hv
  omega

theorem sideCell_injective : Injective sideCell := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change 2 * i.val + 1 = 2 * j.val + 1 at hv
  omega

private theorem cornerCell_ne_sideCell (i j : Fin 4) : cornerCell i ≠ sideCell j := by
  intro h
  have hv := congrArg Fin.val h
  change 2 * i.val = 2 * j.val + 1 at hv
  omega

private theorem sidePiece_color_eq
    (c : Fin 4 → Bool) (P : Fin 4 → Fin 2 → Set CarpetPoints)
    (hd : ∀ i, c (sideCorner i 0) ≠ c (sideCorner i 1) → Disjoint (P i 0) (P i 1))
    {i : Fin 4} {r s : Fin 2} {x : CarpetPoints} (hr : x ∈ P i r) (hs : x ∈ P i s) :
    c (sideCorner i r) = c (sideCorner i s) := by
  fin_cases r <;> fin_cases s
  · rfl
  · by_contra h
    exact Set.disjoint_left.mp (hd i h) hr hs
  · by_contra h
    exact Set.disjoint_left.mp (hd i (Ne.symm h)) hs hr
  · rfl

/-- A compact connected set meeting all four corner interiors crosses at
least one of any two distinct side cells. -/
theorem hasSideCrossing_or_of_corner_intersections
    {A : Set CarpetPoints} (hA : IsCompact A) (hAc : IsPreconnected A)
    (hcorners : ∀ k : Fin 4, (A ∩ cellOpenPart (cornerCell k)).Nonempty)
    {i j : Fin 4} (hij : i ≠ j) : HasSideCrossing A i ∨ HasSideCrossing A j := by
  by_contra! hb
  obtain ⟨c, ⟨k₀, hk₀⟩, ⟨k₁, hk₁⟩, hc⟩ := exists_separating_corner_color i j hij
  have hbad (s : Fin 4) (h : c (sideCorner s 0) ≠ c (sideCorner s 1)) : ¬ HasSideCrossing A s := by
    rcases hc s h with rfl | rfl
    · exact hb.1
    · exact hb.2
  choose P hPc hPcov hPface hPd using fun s ↦ exists_side_pieces hA c s (hbad s)
  let J := Fin 4 ⊕ (Fin 4 × Fin 2)
  let κ : J → Fin 4 := Sum.elim id (fun sr ↦ sideCorner sr.1 sr.2)
  let m : J → Fin 8 := Sum.elim cornerCell (fun sr ↦ sideCell sr.1)
  let S : J → Set CarpetPoints := Sum.elim (fun k ↦ A ∩ range (cellMap (cornerCell k)))
    (fun sr ↦ P sr.1 sr.2)
  have hSc (a : J) : IsCompact (S a) := by
    cases a with
    | inl a => exact hA.inter_right (isCompact_range (continuous_cellMap _)).isClosed
    | inr a => exact hPc a.1 a.2
  have hSsub (a : J) : S a ⊆ A ∩ range (cellMap (m a)) := by
    cases a with
    | inl a => exact subset_rfl
    | inr a =>
      obtain ⟨s, r⟩ := a
      change P s r ⊆ A ∩ range (cellMap (sideCell s))
      rw [← hPcov s]
      fin_cases r
      · exact subset_union_left
      · exact subset_union_right
  have hcontact {a : J} {k : Fin 4} {x : CarpetPoints} (hx : x ∈ S a)
      (h : cellCornerContact (m a) k x) : c (κ a) = c k := by
    cases a with
    | inl a =>
      rcases h with he | ⟨s, r, he, _, _⟩
      · exact congrArg c (cornerCell_injective he)
      · exact (cornerCell_ne_sideCell a s he).elim
    | inr a =>
      obtain ⟨s, r⟩ := a
      rcases h with he | ⟨t, u, he, rfl, hface⟩
      · exact (cornerCell_ne_sideCell k s he.symm).elim
      · have heq : s = t := sideCell_injective he
        subst t
        exact sidePiece_color_eq c P hPd hx (hPface s u ⟨hSsub (.inr (s, r)) hx, hface⟩)
  have hsame {a b : J} {x : CarpetPoints} (ha : x ∈ S a) (hb : x ∈ S b)
      (he : m a = m b) : c (κ a) = c (κ b) := by
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg c (cornerCell_injective he)
      | inr b => exact (cornerCell_ne_sideCell a b.1 he).elim
    | inr a =>
      cases b with
      | inl b => exact (cornerCell_ne_sideCell b a.1 he.symm).elim
      | inr b =>
        obtain ⟨s, r⟩ := a
        obtain ⟨t, u⟩ := b
        have heq : s = t := sideCell_injective he
        subst t
        exact sidePiece_color_eq c P hPd ha hb
  have hcolor {a b : J} {x : CarpetPoints} (ha : x ∈ S a) (hb : x ∈ S b) :
      c (κ a) = c (κ b) := by
    by_cases he : m a = m b
    · exact hsame ha hb he
    obtain ⟨k, hka, hkb⟩ := exists_cellCornerContact he (hSsub a ha).2 (hSsub b hb).2
    exact (hcontact ha hka).trans (hcontact hb hkb).symm
  let U (q : Bool) := ⋃ a : {a : J // c (κ a) = q}, S a.val
  have hUc (q : Bool) : IsClosed (U q) := by
    apply IsCompact.isClosed
    exact isCompact_iUnion fun (a : {a : J // c (κ a) = q}) ↦ hSc a.val
  have hUd : Disjoint (U false) (U true) := Set.disjoint_left.mpr fun x h₀ h₁ ↦ by
    obtain ⟨a, ha⟩ := mem_iUnion.mp h₀
    obtain ⟨b, hb⟩ := mem_iUnion.mp h₁
    exact Bool.false_ne_true (a.property.symm.trans ((hcolor ha hb).trans b.property))
  have hcov : A ⊆ U false ∪ U true := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_cellMap_range x
    have hi' : ∃ k, i = cornerCell k ∨ i = sideCell k := (by decide :
      ∀ i : Fin 8, ∃ k, i = cornerCell k ∨ i = sideCell k) i
    have hasPiece : ∃ a : J, x ∈ S a := by
      obtain ⟨k, rfl | rfl⟩ := hi'
      · exact ⟨.inl k, hx, hi⟩
      · have he : x ∈ P k 0 ∪ P k 1 := hPcov k ▸ (show x ∈ A ∩ range (cellMap (sideCell k)) from ⟨hx, hi⟩)
        rcases he with he | he
        · exact ⟨.inr (k, 0), he⟩
        · exact ⟨.inr (k, 1), he⟩
    obtain ⟨a, ha⟩ := hasPiece
    cases h : c (κ a)
    · exact Or.inl (mem_iUnion.mpr ⟨⟨a, h⟩, ha⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨a, h⟩, ha⟩)
  have hnonempty (k : Fin 4) (q : Bool) (hk : c k = q) : (A ∩ U q).Nonempty := by
    obtain ⟨x, hx, hkx⟩ := hcorners k
    exact ⟨x, hx, mem_iUnion.mpr ⟨⟨.inl k, hk⟩, hx, cellOpenPart_subset_cell _ hkx⟩⟩
  obtain ⟨x, _, hx, hy⟩ := isPreconnected_closed_iff.mp hAc (U false) (U true)
    (hUc false) (hUc true) hcov (hnonempty k₀ false hk₀) (hnonempty k₁ true hk₁)
  exact Set.disjoint_left.mp hUd hx hy

private theorem exists_compact_preconnected_meeting_corners
    {U : Set CarpetPoints} (hU : IsOpen U) (hc : IsPreconnected U)
    (hcorners : ∀ k : Fin 4, (U ∩ cellOpenPart (cornerCell k)).Nonempty) :
    ∃ A ⊆ U, IsCompact A ∧ IsPreconnected A ∧
      ∀ k : Fin 4, (A ∩ cellOpenPart (cornerCell k)).Nonempty := by
  choose x hx using hcorners
  choose V hVU hVc hVp hV₀ hVx using fun k ↦
    exists_compact_preconnected_subset_of_isOpen hU hc (hx 0).1 (hx k).1
  refine ⟨⋃ k, V k, iUnion_subset hVU, isCompact_iUnion hVc, ?_, ?_⟩
  · exact isPreconnected_iUnion ⟨x 0, mem_iInter.mpr hV₀⟩ hVp
  · exact fun k ↦ ⟨x k, mem_iUnion.mpr ⟨k, hVx k⟩, (hx k).2⟩

/-- A connected open set meeting all four corner interiors crosses at least
one of any two distinct side cells. -/
theorem hasSideCrossing_or_of_isOpen
    {U : Set CarpetPoints} (hU : IsOpen U) (hc : IsPreconnected U)
    (hcorners : ∀ k : Fin 4, (U ∩ cellOpenPart (cornerCell k)).Nonempty)
    {i j : Fin 4} (hij : i ≠ j) : HasSideCrossing U i ∨ HasSideCrossing U j := by
  obtain ⟨A, hAU, hA, hAc, hAi⟩ := exists_compact_preconnected_meeting_corners hU hc hcorners
  have lift {i : Fin 4} (h : HasSideCrossing A i) : HasSideCrossing U i := by
    obtain ⟨B, hB, hBc, hBp, hB₀, hB₁⟩ := h
    exact ⟨B, hB.trans (inter_subset_inter_left _ hAU), hBc, hBp, hB₀, hB₁⟩
  exact (hasSideCrossing_or_of_corner_intersections hA hAc hAi hij).imp lift lift

/-- Orient the side cell so its first connection face corresponds to the left side. -/
def sideOrientation (i : Fin 4) : SquareSymmetry :=
  (![ (false, fun _ ↦ false), axisSwap, (false, ![true, false]), (true, ![false, true]) ] :
    Fin 4 → SquareSymmetry) i

/-- The map onto a side cell with the connections oriented left to right. -/
noncomputable def orientedSideMap (i : Fin 4) : CarpetPoints → CarpetPoints :=
  cellMap (sideCell i) ∘ carpetSymmetry (sideOrientation i)

theorem continuous_orientedSideMap (i : Fin 4) : Continuous (orientedSideMap i) :=
  (continuous_cellMap _).comp (continuous_carpetSymmetry _)

theorem injective_orientedSideMap (i : Fin 4) : Injective (orientedSideMap i) :=
  (injective_cellMap _).comp (bijective_carpetSymmetry _).1

theorem range_orientedSideMap (i : Fin 4) : range (orientedSideMap i) = range (cellMap (sideCell i)) := by
  rw [orientedSideMap, range_comp, (bijective_carpetSymmetry _).2.range_eq, image_univ]

theorem orientedSideMap_mem_sideFace_iff (i : Fin 4) (r : Fin 2) (x : CarpetPoints) :
    orientedSideMap i x ∈ sideFace i r ↔ (x : Plane) 0 = (r.val : ℝ) := by
  have hd : cellDigit (sideCell i) (sideAxis i) = 1 := (by decide :
    ∀ i, cellDigit (sideCell i) (sideAxis i) = 1) i
  have hs : (carpetSymmetry (sideOrientation i) x : Plane) (sideAxis i) =
      if i.val < 2 then (x : Plane) 0 else 1 - (x : Plane) 0 := by
    fin_cases i <;> rfl
  change 3 * cellSimilarity (sideCell i) (carpetSymmetry (sideOrientation i) x : Plane) (sideAxis i)
    = (sideFaceDigit i r : ℝ) ↔ _
  rw [cellSimilarity_coord, ← cellDigit_cast, hd, hs]
  by_cases hi : i.val < 2
  · simp only [sideFaceDigit, ite_eq_left hi, Fin.val_one, Nat.cast_one, Nat.cast_add]
    constructor <;> intro h <;> linarith
  · simp only [sideFaceDigit, ite_eq_right hi, Fin.val_one, Nat.cast_one,
      Nat.cast_sub (show r.val ≤ 2 by omega), Nat.cast_ofNat]
    constructor <;> intro h <;> linarith

end CarpetEnergy
