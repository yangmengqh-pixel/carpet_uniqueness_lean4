import CarpetSymmetry
import Mathlib.Topology.Order.Compact

/-!
# Exterior sides of the carpet

The bottom side is covered by its three first-level images. A maximum of
the distance from that side to the compact carpet is therefore at most a
third of itself. The other exterior sides follow from square symmetries.
-/

open Function Metric Set
open scoped unitInterval

namespace CarpetEnergy

private noncomputable def bottomPlane (t : ℝ) : Plane :=
  WithLp.toLp 2 ![t, 0]

private theorem continuous_bottomPlane : Continuous bottomPlane := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_id
  · exact continuous_const

private theorem bottomPlane_cellSimilarity (i : Fin 8) {j : ℕ}
    (hx : (cellDigit i 0 : ℕ) = j) (hy : cellDigit i 1 = 0) (t : ℝ) :
    cellSimilarity i (bottomPlane t) = bottomPlane ((t + j) / 3) := by
  ext k
  rw [cellSimilarity_coord, ← cellDigit_cast]
  fin_cases k
  · change ((t : ℝ) + (cellDigit i 0 : ℕ)) / 3 = (t + j) / 3
    rw [hx]
  · change ((0 : ℝ) + (cellDigit i 1 : ℕ)) / 3 = 0
    rw [hy]
    norm_num

private theorem exists_bottomPlane_preimage (t : I) :
    ∃ (i : Fin 8) (s : I), cellSimilarity i (bottomPlane s) = bottomPlane t := by
  let x := (t : ℝ)
  have h₀ := t.property.1
  have h₁ := t.property.2
  by_cases hx₁ : x ≤ 1 / 3
  · let s : I := ⟨3 * x, ⟨by change 0 ≤ 3 * (t : ℝ); linarith,
      by change 3 * x ≤ 1; linarith⟩⟩
    refine ⟨0, s, ?_⟩
    rw [bottomPlane_cellSimilarity 0 (j := 0) (by decide) (by decide)]
    congr 1
    change (3 * x + (0 : ℕ)) / 3 = x
    ring
  by_cases hx₂ : x ≤ 2 / 3
  · let s : I := ⟨3 * x - 1, ⟨by linarith [lt_of_not_ge hx₁], by linarith⟩⟩
    refine ⟨1, s, ?_⟩
    rw [bottomPlane_cellSimilarity 1 (j := 1) (by decide) (by decide)]
    congr 1
    change (3 * x - 1 + (1 : ℕ)) / 3 = x
    ring
  · let s : I := ⟨3 * x - 2, ⟨by linarith [lt_of_not_ge hx₂],
      by change 3 * (t : ℝ) - 2 ≤ 1; linarith⟩⟩
    refine ⟨2, s, ?_⟩
    rw [bottomPlane_cellSimilarity 2 (j := 2) (by decide) (by decide)]
    congr 1
    change (3 * x - 2 + (2 : ℕ)) / 3 = x
    ring

private theorem bottomPlane_mem_carpet (t : I) : bottomPlane t ∈ (carpet : Set Plane) := by
  let K : Set Plane := carpet
  let d (s : I) := infDist (bottomPlane s) K
  have hd : Continuous d :=
    (continuous_infDist_pt K).comp (continuous_bottomPlane.comp continuous_subtypeVal)
  obtain ⟨s, _, hs⟩ := isCompact_univ.exists_isMaxOn (f := d) univ_nonempty hd.continuousOn
  obtain ⟨i, v, hiv⟩ := exists_bottomPlane_preimage s
  obtain ⟨y, hy, hyd⟩ := carpet.isCompact.exists_infDist_eq_dist carpet.nonempty (bottomPlane v)
  have hyi : cellSimilarity i y ∈ K :=
    carpet_eq_iUnion.ge (mem_iUnion.mpr ⟨i, mem_image_of_mem _ hy⟩)
  have hstep : d s ≤ (1 / 3 : ℝ) * d v := by
    change infDist (bottomPlane s) K ≤ _
    rw [← hiv]
    refine (infDist_le_dist_of_mem hyi).trans_eq ?_
    rw [dist_cellSimilarity, ← hyd]
  have hv : d v ≤ d s := hs (mem_univ v)
  have ht : d t ≤ d s := hs (mem_univ t)
  have hds : 0 ≤ d s := infDist_nonneg
  have hdt : 0 ≤ d t := infDist_nonneg
  exact (carpet.isCompact.isClosed.mem_iff_infDist_zero carpet.nonempty).mpr
    (show d t = 0 by linarith)

/-- The point at horizontal coordinate t on the bottom side of the carpet. -/
noncomputable def bottomPoint (t : I) : CarpetPoints :=
  ⟨bottomPlane t, bottomPlane_mem_carpet t⟩

theorem continuous_bottomPoint : Continuous bottomPoint := by
  apply Continuous.subtype_mk
  exact continuous_bottomPlane.comp continuous_subtypeVal

/-- The bottom side of the square, as a subset of the carpet. -/
def carpetBottom : Set CarpetPoints := {x | (x : Plane) 1 = 0}

/-- The top side of the square, as a subset of the carpet. -/
def carpetTop : Set CarpetPoints := {x | (x : Plane) 1 = 1}

theorem carpetBottom_eq_range : carpetBottom = range bottomPoint := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨(x : Plane) 0, carpet_coord_mem_Icc x 0⟩, ?_⟩
    apply Subtype.ext
    ext j
    fin_cases j
    · rfl
    · exact hx.symm
  · rintro ⟨t, rfl⟩
    rfl

theorem isPreconnected_carpetBottom : IsPreconnected carpetBottom := by
  rw [carpetBottom_eq_range]
  exact isPreconnected_range continuous_bottomPoint

theorem carpetBottom_nonempty : carpetBottom.Nonempty := by
  rw [carpetBottom_eq_range]
  exact range_nonempty _

/-- Reflection in the horizontal middle line of the square. -/
def verticalFlip : SquareSymmetry := (false, fun j ↦ j == 1)

/-- Reflection in the increasing diagonal of the square. -/
def axisSwap : SquareSymmetry := (true, fun _ ↦ false)

theorem carpetSymmetry_verticalFlip_second (x : CarpetPoints) :
    (carpetSymmetry verticalFlip x : Plane) 1 = 1 - (x : Plane) 1 := rfl

theorem carpetSymmetry_axisSwap_second (x : CarpetPoints) :
    (carpetSymmetry axisSwap x : Plane) 1 = (x : Plane) 0 := rfl

theorem carpetTop_eq_image_carpetBottom : carpetTop = carpetSymmetry verticalFlip '' carpetBottom := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (bijective_carpetSymmetry verticalFlip).2 x
    refine ⟨y, ?_, rfl⟩
    change (y : Plane) 1 = 0
    change (carpetSymmetry verticalFlip y : Plane) 1 = 1 at hx
    rw [carpetSymmetry_verticalFlip_second] at hx
    linarith
  · rintro ⟨y, hy, rfl⟩
    change (y : Plane) 1 = 0 at hy
    change (carpetSymmetry verticalFlip y : Plane) 1 = 1
    rw [carpetSymmetry_verticalFlip_second, hy, sub_zero]

theorem isPreconnected_carpetTop : IsPreconnected carpetTop := by
  rw [carpetTop_eq_image_carpetBottom]
  exact isPreconnected_carpetBottom.image _ (continuous_carpetSymmetry _).continuousOn

theorem carpetTop_nonempty : carpetTop.Nonempty := by
  rw [carpetTop_eq_image_carpetBottom]
  exact carpetBottom_nonempty.image _

end CarpetEnergy
