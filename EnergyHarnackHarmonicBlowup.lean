import EnergyDomainNormalization
import EnergyHarmonicNeighborhoodVersion
import EnergyLocalNeighborhoodPasting
import EnergyNeighborhoodPasteBounds
import EnergyNeighborhoodVariation
import EnergyLocalHarmonicLimit
import UniformCarpetSubsequence
import EnergyZeroOneReduction

/-!
# Harmonic blowup compactness from neighborhood Harnack

Normalize on each central cell, take an equal-shape subsequence,
and paste the continuous local versions into a fixed neighborhood.
The Harnack modulus gives compactness of the central pullbacks.
Harmonicity of the pastes upgrades uniform convergence to graph
convergence on the central cell.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 5200000 in
/-- Proposition 4.2 for a generalized-contraction energy satisfying
the neighborhood Harnack inequality. -/
theorem hasInteriorHarmonicCompactness_of_neighborhoodHarnack {H : ℝ} (hH : 1 ≤ H)
    (hHar : E.HasNeighborhoodHarnack H)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ))) :
    E.HasInteriorHarmonicCompactness := by
  classical
  intro f hf n w _hlevel hpos hratio hinside
  have hp := zero_lt_one.trans E.one_lt_p
  have hρ := E.isScalingFactor_scalingFactor.1
  obtain ⟨a, ha, hgood⟩ := hratio
  let b₀ : ℝ≥0∞ := min a 1
  have hb₀ : 0 < b₀ := lt_min ha one_pos
  have hbfin : b₀ ≠ ⊤ := ne_of_lt ((min_le_right a 1).trans_lt ENNReal.one_lt_top)
  let b : ℝ≥0 := b₀.toNNReal
  have hbcoe : (b : ℝ≥0∞) = b₀ := ENNReal.coe_toNNReal hbfin
  have hb : 0 < b := ENNReal.coe_pos.mp (hbcoe.symm ▸ hb₀)
  have hgood' (j : ℕ) : (b : ℝ≥0∞) * E.energyMeasure f (wordCellUnion (cellNeighborhood (w j) 3)) ≤
      E.energyMeasure f (range (wordMap (List.ofFn (w j)))) := by
    rw [hbcoe]
    exact (mul_le_mul' (min_le_left _ _) le_rfl).trans (hgood j)
  obtain ⟨i, hi, hshape⟩ := exists_constant_neighborhoodShape_subseq n w 3
  let u := w (i 0)
  let v (j : ℕ) := w (i j)
  let q (j : ℕ) := E.globallyNormalizedDomain (List.ofFn (v j)) f
  let W (j : ℕ) := wordCellUnion (cellNeighborhood (v j) 2)
  have hs (j : ℕ) : neighborhoodShape u 3 = neighborhoodShape (v j) 3 := (hshape j).symm
  have hq (j : ℕ) : E.IsInteriorHarmonic (q j) := E.globallyNormalizedDomain_harmonic _ hf
  have hdist (j : ℕ) : Disjoint (wordCellUnion (cellNeighborhood (v j) 3)) carpetOuterBoundary :=
    disjoint_left.mpr (hinside (i j))
  obtain ⟨L, hL, C, hC, hprofile⟩ := E.exists_continuous_harmonic_neighborhood_version hH hHar hG
  choose F hF hFcenter hFosc using fun j : ℕ ↦
    hprofile (n (i j)) (v j) (hdist j) (q j) (hq j)
  let A := (b : ℝ)⁻¹
  have hA : 0 < A := inv_pos.mpr (NNReal.coe_pos.mpr hb)
  let M := C * A ^ p⁻¹
  have hM : 0 < M := mul_pos hC (Real.rpow_pos_of_pos hA _)
  have hsum (j : ℕ) : (∑ z ∈ cellNeighborhood (v j) 3,
      (E.energy (E.pullbackWord (List.ofFn z) (q j)) : ℝ)) ≤ A :=
    E.sum_normalizedDomain_pullback_energy_le (v j) f b hb (hpos (i j)) (hgood' (i j))
  let R (j : ℕ) := C * ((E.scalingFactor ^ n (i j))⁻¹ *
    E.cellUnionEnergy (cellNeighborhood (v j) 3) (q j)) ^ p⁻¹
  have hR (j : ℕ) : R j ≤ M := by
    dsimp only [R, cellUnionEnergy]
    rw [← mul_assoc (E.scalingFactor ^ n (i j))⁻¹, inv_mul_cancel₀ (pow_ne_zero _ hρ.ne'), one_mul]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (Finset.sum_nonneg (fun _ _ ↦ NNReal.coe_nonneg _)) (hsum j) (inv_nonneg.mpr hp.le)) hC.le
  have hFsup (j : ℕ) (x : W j) : |F j x| ≤ M := by
    have h := hFcenter j x
    rw [E.globallyNormalizedDomain_wordMean, sub_zero] at h
    exact h.trans (hR j)
  obtain ⟨k, hk, hk1, _⟩ := E.exists_core_cutoff (isOpen_wordNeighborhoodOpen u 2)
    (isClosed_wordCellUnion _) (wordCellUnion_neighborhood_subset_open_succ (r := 1) u)
  choose g P hPdom hPval hg hg0 using fun j : ℕ ↦
    E.exists_neighborhood_paste_local u (v j) (hs j) (by decide : 2 ≤ 3) (q j) (F j) (hF j) k hk
  have hmatchCore (j : ℕ) (z : {a // a ∈ cellNeighborhood u 2}) (hz : z.val ∈ cellNeighborhood u 1) :
      E.wordPullbackCore (List.ofFn z.val) (g j) = P j (neighborhoodInnerImage u (v j) (hs j) (by decide) z) := by
    rw [hg j z]
    apply Subtype.ext
    ext x
    rw [E.mulCore_apply, E.wordPullbackCore_apply,
      hk1 _ (mem_iUnion₂.mpr ⟨z.val, hz, mem_range_self x⟩), one_mul]
  have hmatch (j : ℕ) (z : {a // a ∈ cellNeighborhood u 3}) (hz : z.val ∈ cellNeighborhood u 1) :
      E.pullbackWord (List.ofFn z.val) (E.continuousCoreToDomain (g j)) =
        E.pullbackWord (List.ofFn (neighborhoodEquiv u (v j) (hs j) z).val) (q j) := by
    let z' : {a // a ∈ cellNeighborhood u 2} := ⟨z.val, cellNeighborhood_subset_succ u hz⟩
    rw [← E.continuousCoreToDomain_wordPullbackCore, hmatchCore j z' hz, hPdom]
    rfl
  let U := wordNeighborhoodOpen u 1
  have hharm (j : ℕ) : E.IsHarmonicOn U (g j) :=
    E.isHarmonicOn_of_neighborhood_pullbacks_domain u (v j) (hs j) (q j) (g j) (hq j)
      (hinside (i j)) (hmatch j)
  let B := max (A ^ p⁻¹) M
  have hB : 0 ≤ B := hM.le.trans (le_max_right _ _)
  have hPlim (j : ℕ) (z : {a // a ∈ cellNeighborhood (v j) 2}) :
      E.rootSeminorm (E.continuousCoreToDomain (P j z)) ≤ B ∧ ‖(P j z).val‖ ≤ B := by
    refine ⟨?_, (ContinuousMap.norm_le _ hB).mpr fun x ↦ ?_⟩
    · rw [hPdom, E.rootSeminorm_apply]
      have hE : (E.energy (E.pullbackWord (List.ofFn z.val) (q j)) : ℝ) ≤ A :=
        (Finset.single_le_sum (f := fun a ↦ (E.energy (E.pullbackWord (List.ofFn a) (q j)) : ℝ))
          (fun _ _ ↦ NNReal.coe_nonneg _)
          (cellNeighborhood_subset_succ (v j) z.property)).trans (hsum j)
      exact (Real.rpow_le_rpow (NNReal.coe_nonneg _) hE (inv_nonneg.mpr hp.le)).trans (le_max_left _ _)
    · rw [Real.norm_eq_abs, hPval]
      exact (hFsup j _).trans (le_max_right _ _)
  obtain ⟨D, hD⟩ := E.exists_graph_bound_of_cellwise_paste u k hB
  have hgBound (j : ℕ) : E.graphSeminorm (E.continuousCoreToDomain (g j)) ≤ D :=
    hD (fun z ↦ P j (neighborhoodInnerImage u (v j) (hs j) (by decide) z)) (g j)
      (fun z ↦ hPlim j _) (hg j) (hg0 j)
  let gCentral (j : ℕ) := E.wordPullbackCore (List.ofFn u) (g j)
  have hGc (j : ℕ) : gCentral j = P j ⟨v j, self_mem_cellNeighborhood (v j) 2⟩ := by
    have hh := hmatchCore j ⟨u, self_mem_cellNeighborhood u 2⟩ (self_mem_cellNeighborhood u 1)
    have he : neighborhoodInnerImage u (v j) (hs j) (by decide : 2 ≤ 3)
        ⟨u, self_mem_cellNeighborhood u 2⟩ = ⟨v j, self_mem_cellNeighborhood (v j) 2⟩ := by
      apply Subtype.ext
      have hh := congrArg Subtype.val (neighborhoodEquiv_center u (v j) (hs j))
      exact hh
    rw [he] at hh
    exact hh
  have hGcSup (j : ℕ) (x : CarpetPoints) : |(gCentral j).val x| ≤ M := by
    rw [hGc, hPval]
    exact hFsup j _
  have hGcMod : ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ j x y, dist x y < d →
      |(gCentral j).val x - (gCentral j).val y| ≤ ε := by
    intro ε hε
    have hlim : Tendsto (fun l ↦ harnackOscillationFactor H ^ l * (2 * M)) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (harnackOscillationFactor_nonneg H) (harnackOscillationFactor_lt_one hH)).mul_const (2 * M)
    obtain ⟨l, hl⟩ := (hlim.eventually_lt_const hε).exists
    let d := (1 / 3 : ℝ) ^ (L + L + L * l) / 2
    refine ⟨d, by dsimp [d]; positivity, fun j x y hxy ↦ ?_⟩
    let X : W j := ⟨wordMap (List.ofFn (v j)) x, mem_iUnion₂.mpr
      ⟨v j, self_mem_cellNeighborhood (v j) 2, mem_range_self x⟩⟩
    let Y : W j := ⟨wordMap (List.ofFn (v j)) y, mem_iUnion₂.mpr
      ⟨v j, self_mem_cellNeighborhood (v j) 2, mem_range_self y⟩⟩
    have hXY : dist X Y < (1 / 3 : ℝ) ^ harmonicOscillationLevel (n (i j)) L l / 2 := by
      change dist (wordMap (List.ofFn (v j)) x) (wordMap (List.ofFn (v j)) y) < _
      rw [dist_wordMap, List.length_ofFn, show harmonicOscillationLevel (n (i j)) L l =
        n (i j) + (L + L + L * l) by simp only [harmonicOscillationLevel, add_assoc], pow_add, mul_div_assoc]
      exact mul_lt_mul_of_pos_left hxy (by positivity)
    have ho := hFosc j l X Y hXY
    have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hR j) (by norm_num : (0 : ℝ) ≤ 2))
      (pow_nonneg (harnackOscillationFactor_nonneg H) l)
    rw [hGc, hPval, hPval]
    exact (ho.trans hb').trans hl.le
  obtain ⟨J, F₀, hJ, hlim⟩ := exists_uniform_subseq_of_equicontinuous_carpet_sequence
    (fun j ↦ (gCentral j).val) hGcSup hGcMod
  have hclose : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ l m, N ≤ l → N ≤ m →
      ∀ x ∈ range (wordMap (List.ofFn u)), |(g (J l)).val x - (g (J m)).val x| ≤ δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq δ hδ
    refine ⟨N, fun l m hl hm x hx ↦ ?_⟩
    obtain ⟨y, rfl⟩ := hx
    have hd := hN l hl m hm
    rw [dist_eq_norm] at hd
    rw [← Real.norm_eq_abs, ← E.wordPullbackCore_apply, ← E.wordPullbackCore_apply]
    exact (((gCentral (J l)).val - (gCentral (J m)).val).norm_coe_le_norm y).trans hd.le
  have hwU : range (wordMap (List.ofFn u)) ⊆ U := by
    apply Subset.trans _ (wordCellUnion_neighborhood_subset_open_succ (r := 0) u)
    exact fun _ hx ↦ mem_iUnion₂.mpr ⟨u, self_mem_cellNeighborhood u 0, hx⟩
  obtain ⟨g₀, u₀, hu₀, hgraph⟩ := E.exists_graph_limit_of_uniform_cauchy_on_harmonic_cell
    (isOpen_wordNeighborhoodOpen u 1) (List.ofFn u) hwU (g ∘ J) (fun j ↦ hharm (J j))
    (fun j ↦ (E.rootSeminorm_le_graphSeminorm _).trans (hgBound (J j))) hclose
  refine ⟨i ∘ J, g₀, u₀, hi.comp hJ, hu₀, ?_⟩
  have hcentral (j : ℕ) : E.pullbackWord (List.ofFn u) (E.continuousCoreToDomain (g j)) =
      E.normalizedWordPullback (List.ofFn (v j)) f := by
    have hh := hmatch j ⟨u, self_mem_cellNeighborhood u 3⟩ (self_mem_cellNeighborhood u 1)
    rw [neighborhoodEquiv_center] at hh
    exact hh.trans (E.globallyNormalizedDomain_pullback _ f)
  simpa only [Function.comp_apply, hcentral] using hgraph

/-- Neighborhood Harnack and generalized contraction imply the zero-one
law for minimal energy-dominant measures. -/
theorem zeroOne_of_neighborhoodHarnack {H : ℝ} (hH : 1 ≤ H)
    (hHar : E.HasNeighborhoodHarnack H)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (μ : Measure CarpetPoints) (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (hmin : ∀ ν : Measure CarpetPoints, (∀ f, E.energyMeasure f ≪ ν) → μ ≪ ν) :
    HasZeroOneLaw μ (Sum.elim cellMap carpetSymmetry) :=
  E.zeroOne_of_interiorHarmonicCompactness
    (E.hasInteriorHarmonicCompactness_of_neighborhoodHarnack hH hHar hG) μ hdom hmin

end CarpetEnergy.SelfSimilarPEnergy
