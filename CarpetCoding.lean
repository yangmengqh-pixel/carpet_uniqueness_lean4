import Carpet
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order

/-!
# The symbolic coding of the carpet

The coding is the fixed point of the contraction that applies the cell indexed
by the first symbol to the coding of the remaining symbols.
-/

open Function Metric Set TopologicalSpace
open scoped NNReal BoundedContinuousFunction

namespace CarpetEnergy

/-- The space of infinite words on the eight cells. -/
abbrev Addresses := ℕ → Fin 8

/-- The first symbol followed by the given address. -/
def prepend (i : Fin 8) (s : Addresses) : Addresses
  | 0 => i
  | n + 1 => s n

private def tail (s : Addresses) : Addresses := fun n ↦ s (n + 1)

private def unitSquare : Set Plane := {x | ∀ j, x j ∈ Icc (0 : ℝ) 1}

private abbrev Square := ↥unitSquare

private theorem isCompact_unitSquare : IsCompact unitSquare := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)
  have h : unitSquare = e.symm '' (Set.univ.pi fun _ : Fin 2 ↦ Icc (0 : ℝ) 1) := by
    ext x
    rw [Homeomorph.image_symm, mem_preimage, Set.mem_pi]
    change (∀ j, x j ∈ Icc (0 : ℝ) 1) ↔ _
    exact ⟨fun h j _ ↦ h j, fun h j ↦ h j (mem_univ j)⟩
  rw [h]
  exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).image e.symm.continuous

private instance : CompactSpace Square := isCompact_iff_compactSpace.mp isCompact_unitSquare

private instance : Nonempty Square := ⟨⟨0, fun _ ↦ ⟨le_rfl, zero_le_one⟩⟩⟩

/-- The ternary offsets of the eight cells, in the paper's order. -/
def cellDigit (i : Fin 8) (j : Fin 2) : Fin 3 :=
  ![![0, 0], ![1, 0], ![2, 0], ![2, 1],
    ![2, 2], ![1, 2], ![0, 2], ![0, 1]] i j

theorem cellDigit_cast (i : Fin 8) (j : Fin 2) :
    ((cellDigit i j : ℕ) : ℝ) = 2 * cellCenter i j := by
  fin_cases i <;> fin_cases j <;> norm_num [cellDigit, cellCenter, WithLp.toLp, Fin.reduceFinMk]

theorem cellDigit_injective : Injective cellDigit := by
  decide

theorem cellCenter_mem_Icc (i : Fin 8) (j : Fin 2) :
    cellCenter i j ∈ Icc (0 : ℝ) 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [cellCenter, WithLp.toLp, Fin.reduceFinMk]

theorem cellSimilarity_coord (i : Fin 8) (x : Plane) (j : Fin 2) :
    cellSimilarity i x j = (x j + 2 * cellCenter i j) / 3 := by
  change (1 / 3 : ℝ) * (x j - cellCenter i j) + cellCenter i j = _
  ring

private noncomputable def squareCell (i : Fin 8) (x : Square) : Square :=
  ⟨cellSimilarity i x, fun j ↦ by
    rw [cellSimilarity_coord]
    have hx := x.property j
    have hc := cellCenter_mem_Icc i j
    exact ⟨by linarith [hx.1, hc.1], by linarith [hx.2, hc.2]⟩⟩

private theorem continuous_squareCell : Continuous (fun a : Fin 8 × Square ↦ squareCell a.1 a.2) := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  apply Continuous.subtype_mk
  exact (LipschitzWith.of_dist_le_mul (K := (1 / 3 : ℝ≥0)) (f := cellSimilarity i)
    (fun x y ↦ by simpa using (dist_cellSimilarity i x y).le)).continuous.comp
    continuous_subtypeVal

private noncomputable def codingStep (f : Addresses →ᵇ Square) (s : Addresses) : Square :=
  squareCell (s 0) (f (tail s))

private theorem continuous_codingStep (f : Addresses →ᵇ Square) :
    Continuous (codingStep f) := by
  have hhead : Continuous (fun s : Addresses ↦ s 0) := continuous_apply 0
  have htail : Continuous tail := continuous_pi fun n ↦ continuous_apply (n + 1)
  have hpair : Continuous (fun s : Addresses ↦ (s 0, f (tail s))) :=
    hhead.prodMk (f.continuous.comp htail)
  change Continuous
    ((fun a : Fin 8 × Square ↦ squareCell a.1 a.2) ∘ (fun s : Addresses ↦ (s 0, f (tail s))))
  exact continuous_squareCell.comp hpair

private noncomputable def codingOperator (f : Addresses →ᵇ Square) : Addresses →ᵇ Square :=
  BoundedContinuousFunction.mkOfCompact ⟨codingStep f, continuous_codingStep f⟩

private theorem contracting_codingOperator :
    ContractingWith (1 / 3 : ℝ≥0) codingOperator := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun f g ↦ ?_⟩
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro s
  change dist (cellSimilarity (s 0) (f (tail s))) (cellSimilarity (s 0) (g (tail s))) ≤ _
  rw [dist_cellSimilarity]
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) (tail s)) (by norm_num)

private instance : Nonempty (Addresses →ᵇ Square) :=
  ⟨BoundedContinuousFunction.const Addresses ⟨0, fun _ ↦ ⟨le_rfl, zero_le_one⟩⟩⟩

private noncomputable def squareCoding : Addresses →ᵇ Square :=
  contracting_codingOperator.fixedPoint codingOperator

private theorem squareCoding_prepend (i : Fin 8) (s : Addresses) :
    squareCoding (prepend i s) = squareCell i (squareCoding s) :=
  (congrArg (fun f : Addresses →ᵇ Square ↦ f (prepend i s))
    contracting_codingOperator.fixedPoint_isFixedPt.eq).symm

private noncomputable def planeCoding (s : Addresses) : Plane := squareCoding s

private theorem range_planeCoding : range planeCoding = (carpet : Set Plane) := by
  let K : NonemptyCompacts Plane :=
    ⟨⟨range planeCoding, isCompact_range
      (continuous_subtypeVal.comp squareCoding.continuous)⟩, range_nonempty _⟩
  have hK : (K : Set Plane) = ⋃ i : Fin 8, cellSimilarity i '' (K : Set Plane) := by
    change range planeCoding = ⋃ i : Fin 8, cellSimilarity i '' range planeCoding
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      have hs : prepend (s 0) (tail s) = s := by funext n; cases n <;> rfl
      exact mem_iUnion.mpr ⟨s 0, planeCoding (tail s), mem_range_self _,
        by
          change (squareCell (s 0) (squareCoding (tail s)) : Plane) = (squareCoding s : Plane)
          rw [← squareCoding_prepend, hs]⟩
    · intro hx
      obtain ⟨i, y, ⟨s, rfl⟩, rfl⟩ := mem_iUnion.mp hx
      exact ⟨prepend i s, congrArg (fun x : Square ↦ (x : Plane)) (squareCoding_prepend i s)⟩
  exact congrArg (fun A : NonemptyCompacts Plane ↦ (A : Set Plane)) (eq_carpet_of_eq_iUnion K hK)

/-- Continuous address map onto the standard carpet. -/
noncomputable def coding (s : Addresses) : CarpetPoints :=
  ⟨planeCoding s, range_planeCoding ▸ mem_range_self s⟩

theorem continuous_coding : Continuous coding :=
  (continuous_subtypeVal.comp squareCoding.continuous).subtype_mk _

theorem surjective_coding : Surjective coding := by
  intro x
  obtain ⟨s, hs⟩ := show (x : Plane) ∈ range planeCoding from range_planeCoding.symm ▸ x.property
  exact ⟨s, Subtype.ext hs⟩

theorem coding_prepend (i : Fin 8) (s : Addresses) :
    coding (prepend i s) = cellMap i (coding s) :=
  Subtype.ext (congrArg (fun x : Square ↦ (x : Plane)) (squareCoding_prepend i s))

theorem carpet_coord_mem_Icc (x : CarpetPoints) (j : Fin 2) :
    (x : Plane) j ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨s, rfl⟩ := surjective_coding x
  exact (squareCoding s).property j

end CarpetEnergy
