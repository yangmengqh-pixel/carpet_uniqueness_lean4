import EnergyMorreyCompactness
import EnergyZeroOneReduction
import EnergyMorreyNeighborhoodBounds
import EnergyNeighborhoodPasteBounds
import EnergyNeighborhoodVariation
import EnergyLocalHarmonicLimit

/-!
# Harmonic blowup compactness in the Morrey regime

Equal-shape neighborhoods are pasted into a fixed target with a cutoff
that equals one on its first neighborhood. The ratio bound controls all
pasted profiles in the graph norm. Morrey compactness gives a uniform
subsequence, and local harmonic Cauchy convergence gives the graph limit
on the central cell.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1800000 in
theorem hasInteriorHarmonicCompactness_of_scalingFactor_gt_one (hρ : 1 < E.scalingFactor) :
    E.HasInteriorHarmonicCompactness := by
  classical
  intro f hf n w _hlevels hpos hratio hinside
  obtain ⟨F, hF⟩ := E.exists_continuous_version_of_scalingFactor_gt_one hρ f
  have hdom : continuousLp p F ∈ E.domain := hF.symm ▸ f.property
  let f' : E.continuousCore := ⟨F, hdom⟩
  have hff : E.continuousCoreToDomain f' = f := Subtype.ext hF
  obtain ⟨a, ha, hgood⟩ := hratio
  let a₁ : ℝ≥0∞ := min a 1
  have ha₁ : 0 < a₁ := lt_min ha one_pos
  have haFin : a₁ ≠ ⊤ := ne_of_lt ((min_le_right a 1).trans_lt ENNReal.one_lt_top)
  let b : ℝ≥0 := a₁.toNNReal
  have hbcoe : (b : ℝ≥0∞) = a₁ := ENNReal.coe_toNNReal haFin
  have hb : 0 < b := ENNReal.coe_pos.mp (hbcoe.symm ▸ ha₁)
  have hratio' (j : ℕ) : (b : ℝ≥0∞) * E.energyMeasure f (wordCellUnion (cellNeighborhood (w j) 3)) ≤
      E.energyMeasure f (range (wordMap (List.ofFn (w j)))) := by
    rw [hbcoe]
    exact (mul_le_mul' (min_le_left _ _) le_rfl).trans (hgood j)
  obtain ⟨B, hB, hbounds⟩ := E.exists_morrey_normalized_neighborhood_bounds hρ 3 b hb
  obtain ⟨i, hi, hshape⟩ := exists_constant_neighborhoodShape_subseq n w 3
  let u := w (i 0)
  let U := wordNeighborhoodOpen u 1
  let v (j : ℕ) := w (i j)
  have hs (j : ℕ) : neighborhoodShape u 3 = neighborhoodShape (v j) 3 := (hshape j).symm
  have hkRegion : wordCellUnion (cellNeighborhood u 1) ⊆ wordNeighborhoodOpen u 3 := by
    refine Subset.trans ?_ (wordCellUnion_neighborhood_subset_open_succ (r := 2) u)
    intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp hx
    obtain ⟨hz1, hz⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨cellNeighborhood_mono u (by decide) hz1, hz⟩⟩
  obtain ⟨k, hk, hk1, _⟩ := E.exists_core_cutoff (isOpen_wordNeighborhoodOpen u 3)
    (isClosed_wordCellUnion _) hkRegion
  let q (j : ℕ) := E.globallyNormalizedCore (List.ofFn (v j)) f'
  choose g hg hg0 using fun j ↦ E.exists_neighborhood_paste u (v j) (hs j) (q j) k hk
  have hm (j : ℕ) (z : {z // z ∈ cellNeighborhood u 3}) (hz : z.val ∈ cellNeighborhood u 1) :
      E.wordPullbackCore (List.ofFn z.val) (g j) =
        E.wordPullbackCore (List.ofFn (neighborhoodEquiv u (v j) (hs j) z).val) (q j) := by
    rw [hg j z]
    apply Subtype.ext
    ext x
    rw [E.mulCore_apply, E.wordPullbackCore_apply,
      hk1 _ (mem_iUnion.mpr ⟨z.val, mem_iUnion.mpr ⟨hz, mem_range_self x⟩⟩), one_mul]
  have hharm (j : ℕ) : E.IsHarmonicOn U (g j) :=
    E.isHarmonicOn_of_neighborhood_pullbacks u (v j) (hs j) (q j) (g j)
      (E.globallyNormalizedCore_harmonic _ f' (hff.symm ▸ hf)) (hinside (i j)) (hm j)
  obtain ⟨R, hR⟩ := E.exists_graph_bound_of_neighborhood_paste u k hB.le
  have hRg (j : ℕ) : E.graphSeminorm (E.continuousCoreToDomain (g j)) ≤ R := by
    apply hR (v j) (hs j) (q j) (g j) _ (hg j) (hg0 j)
    intro z
    exact hbounds (n (i j)) (v j) f' (hff.symm ▸ hpos (i j)) (hff.symm ▸ hratio' (i j))
      z.val z.property
  obtain ⟨J, _Fℓ, hJ, hlim⟩ := E.exists_uniform_subseq_of_graph_bounded_morrey hρ g hRg
  have hseq := hlim.cauchySeq
  have hclose : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ l m, N ≤ l → N ≤ m →
      ∀ x ∈ range (wordMap (List.ofFn u)), |(g (J l)).val x - (g (J m)).val x| ≤ δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hseq δ hδ
    refine ⟨N, fun l m hl hm x _ ↦ ?_⟩
    have hd := hN l hl m hm
    rw [dist_eq_norm] at hd
    rw [← Real.norm_eq_abs]
    exact (((g (J l)).val - (g (J m)).val).norm_coe_le_norm x).trans hd.le
  have hU : IsOpen U := isOpen_wordNeighborhoodOpen u 1
  have hwU : range (wordMap (List.ofFn u)) ⊆ U := by
    apply Subset.trans _ (wordCellUnion_neighborhood_subset_open_succ (r := 0) u)
    intro x hx
    exact mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨self_mem_cellNeighborhood u 0, hx⟩⟩
  obtain ⟨G, H, hH, hgraph⟩ := E.exists_graph_limit_of_uniform_cauchy_on_harmonic_cell hU (List.ofFn u)
    hwU (g ∘ J) (fun j ↦ hharm (J j))
    (fun j ↦ (E.rootSeminorm_le_graphSeminorm _).trans (hRg (J j))) hclose
  refine ⟨i ∘ J, G, H, hi.comp hJ, hH, ?_⟩
  have hcentral (j : ℕ) : E.pullbackWord (List.ofFn u) (E.continuousCoreToDomain (g j)) =
      E.normalizedWordPullback (List.ofFn (w (i j))) f := by
    have h := hm j ⟨u, self_mem_cellNeighborhood u 3⟩ (self_mem_cellNeighborhood u 1)
    rw [neighborhoodEquiv_center] at h
    have hd := congrArg E.continuousCoreToDomain h
    simp only [E.continuousCoreToDomain_wordPullbackCore] at hd
    rw [hd]
    exact (E.globallyNormalizedCore_pullback (List.ofFn (v j)) f').trans
      (congrArg (E.normalizedWordPullback (List.ofFn (v j))) hff)
  simpa only [Function.comp_apply, hcentral] using hgraph

/-- The invariant-set zero-one law in the Morrey regime. -/
theorem zeroOne_of_scalingFactor_gt_one (hρ : 1 < E.scalingFactor)
    (μ : Measure CarpetPoints) (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (hmin : ∀ ν : Measure CarpetPoints, (∀ f, E.energyMeasure f ≪ ν) → μ ≪ ν) :
    HasZeroOneLaw μ (Sum.elim cellMap carpetSymmetry) :=
  E.zeroOne_of_interiorHarmonicCompactness
    (E.hasInteriorHarmonicCompactness_of_scalingFactor_gt_one hρ) μ hdom hmin

end CarpetEnergy.SelfSimilarPEnergy
