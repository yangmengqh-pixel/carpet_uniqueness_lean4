import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The standard Sierpiński carpet

The eight similarities and the compact fixed point from Section 2 of
Meng Yang's *On the uniqueness of p-energy on the Sierpiński carpet*.
-/

open Function Metric Set TopologicalSpace
open scoped NNReal

namespace CarpetEnergy

private def compactUnionImages {X I : Type*} [MetricSpace X] [Finite I] [Nonempty I]
    (f : I → X → X) (hf : ∀ i, Continuous (f i))
    (A : NonemptyCompacts X) : NonemptyCompacts X :=
  ⟨⟨⋃ i, f i '' (A : Set X), isCompact_iUnion (fun i ↦ A.isCompact.image (hf i))⟩,
    let ⟨i⟩ := ‹Nonempty I›
    (A.nonempty.image (f i)).mono (subset_iUnion (fun i ↦ f i '' (A : Set X)) i)⟩

private theorem lipschitz_compactUnionImages {X I : Type*} [MetricSpace X] [Finite I]
    [Nonempty I] {k : ℝ≥0} (f : I → X → X) (hf : ∀ i, LipschitzWith k (f i)) :
    LipschitzWith k (compactUnionImages f (fun i ↦ (hf i).continuous)) := by
  have matchPoint (A B : NonemptyCompacts X) (z : X)
      (hz : z ∈ ⋃ i, f i '' (A : Set X)) :
      ∃ w ∈ ⋃ i, f i '' (B : Set X), dist z w ≤ (k : ℝ) * dist A B := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := hi
    obtain ⟨y, hy, hxy⟩ := B.isCompact.exists_infDist_eq_dist B.nonempty x
    refine ⟨f i y, mem_iUnion.mpr ⟨i, mem_image_of_mem _ hy⟩, ?_⟩
    have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded
      A.nonempty B.nonempty A.isCompact.isBounded B.isCompact.isBounded
    calc
      dist (f i x) (f i y) ≤ (k : ℝ) * dist x y := (hf i).dist_le_mul x y
      _ = (k : ℝ) * infDist x (B : Set X) := by rw [hxy]
      _ ≤ (k : ℝ) * dist A B :=
        mul_le_mul_of_nonneg_left (infDist_le_hausdorffDist_of_mem hx hfin) k.coe_nonneg
  apply LipschitzWith.of_dist_le_mul
  intro A B
  rw [TopologicalSpace.NonemptyCompacts.dist_eq]
  exact hausdorffDist_le_of_mem_dist (mul_nonneg k.coe_nonneg dist_nonneg)
    (matchPoint A B) (dist_comm B A ▸ matchPoint B A)

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Centers of the eight similarities, in the paper's cyclic order. -/
noncomputable def cellCenter (i : Fin 8) : Plane :=
  WithLp.toLp 2
    (![![0, 0], ![1 / 2, 0], ![1, 0], ![1, 1 / 2],
      ![1, 1], ![1 / 2, 1], ![0, 1], ![0, 1 / 2]] i)

/-- The ambient similarity of ratio one third fixing the given center. -/
noncomputable def cellSimilarity (i : Fin 8) (x : Plane) : Plane :=
  (1 / 3 : ℝ) • (x - cellCenter i) + cellCenter i

theorem dist_cellSimilarity (i : Fin 8) (x y : Plane) :
    dist (cellSimilarity i x) (cellSimilarity i y) = (1 / 3 : ℝ) * dist x y := by
  rw [cellSimilarity, cellSimilarity, dist_add_right, dist_smul₀, dist_sub_right, Real.norm_eq_abs]
  norm_num

private theorem lipschitz_cellSimilarity (i : Fin 8) :
    LipschitzWith (1 / 3) (cellSimilarity i) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [dist_cellSimilarity, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]

private noncomputable def carpetOperator (A : NonemptyCompacts Plane) : NonemptyCompacts Plane :=
  compactUnionImages cellSimilarity (fun i ↦ (lipschitz_cellSimilarity i).continuous) A

private theorem contracting_carpetOperator : ContractingWith (1 / 3) carpetOperator :=
  ⟨by norm_num, lipschitz_compactUnionImages cellSimilarity lipschitz_cellSimilarity⟩

/-- The standard carpet as a nonempty compact subset of the Euclidean plane. -/
noncomputable def carpet : NonemptyCompacts Plane :=
  contracting_carpetOperator.fixedPoint carpetOperator

theorem carpet_eq_iUnion :
    (carpet : Set Plane) = ⋃ i : Fin 8, cellSimilarity i '' (carpet : Set Plane) :=
  congrArg (fun A : NonemptyCompacts Plane ↦ (A : Set Plane))
    contracting_carpetOperator.fixedPoint_isFixedPt.eq.symm

theorem eq_carpet_of_eq_iUnion (K : NonemptyCompacts Plane)
    (hK : (K : Set Plane) = ⋃ i : Fin 8, cellSimilarity i '' (K : Set Plane)) :
    K = carpet :=
  contracting_carpetOperator.fixedPoint_unique (TopologicalSpace.NonemptyCompacts.ext hK.symm)

abbrev CarpetPoints := ↥(carpet : Set Plane)

/-- A first-level similarity as a self-map of the carpet. -/
noncomputable def cellMap (i : Fin 8) (x : CarpetPoints) : CarpetPoints :=
  ⟨cellSimilarity i x, carpet_eq_iUnion.ge
    (mem_iUnion.mpr ⟨i, mem_image_of_mem _ x.property⟩)⟩

theorem continuous_cellMap (i : Fin 8) : Continuous (cellMap i) :=
  ((lipschitz_cellSimilarity i).continuous.comp continuous_subtypeVal).subtype_mk _

theorem injective_cellMap (i : Fin 8) : Injective (cellMap i) := by
  intro x y h
  have hdist : dist (cellSimilarity i x) (cellSimilarity i y) = 0 :=
    dist_eq_zero.mpr (congrArg Subtype.val h)
  rw [dist_cellSimilarity, mul_eq_zero] at hdist
  exact Subtype.ext (dist_eq_zero.mp (hdist.resolve_left (by norm_num)))

theorem measurableEmbedding_cellMap (i : Fin 8) : MeasurableEmbedding (cellMap i) := by
  have : CompactSpace CarpetPoints := isCompact_iff_compactSpace.mp carpet.isCompact
  exact ((continuous_cellMap i).isClosedEmbedding (injective_cellMap i)).measurableEmbedding

/-- The cell map for a finite word, composed in the manuscript's order. -/
noncomputable def wordMap : List (Fin 8) → CarpetPoints → CarpetPoints
  | [] => id
  | i :: w => cellMap i ∘ wordMap w

theorem measurableEmbedding_wordMap (w : List (Fin 8)) : MeasurableEmbedding (wordMap w) := by
  induction w with
  | nil => exact MeasurableEmbedding.id
  | cons i w ih => exact (measurableEmbedding_cellMap i).comp ih

end CarpetEnergy
