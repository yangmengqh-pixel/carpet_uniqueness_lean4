import CarpetCellProjections
import CarpetCellNeighborhoods
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import EnergyGammaCompactness

/-!
# Contractions of the discrete and limiting carpet energies

The finite graph has a vertex for each level cell, with an edge between
distinct cells meeting at that level. Composition after lifting the cell
averages contracts the discrete energy. The lifts converge in Lp, so the
contraction passes to every subsequential Γ-limit.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

/-- The rescaled energy of the graph of intersecting level cells,
using one half of the sum over oriented edges. -/
noncomputable def discreteCellEnergy (p ρ : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (n : ℕ) (f : CarpetLp p) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (ρ ^ n / 2 * (∑ w : Fin n → Fin 8,
    ∑ v ∈ Finset.univ.filter (fun v ↦ v ≠ w ∧
      (range (wordMap (List.ofFn w)) ∩ range (wordMap (List.ofFn v))).Nonempty),
      |ambientWordMean p (List.ofFn w) f - ambientWordMean p (List.ofFn v) f| ^ p))

theorem ambientWordMean_eq_of_ae_eq_on_openWordCell {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {n : ℕ} (w : Fin n → Fin 8) {f : CarpetLp p} {a : ℝ}
    (hf : (f : CarpetPoints → ℝ) =ᵐ[carpetMeasure.restrict (openWordCell w)] fun _ ↦ a) :
    ambientWordMean p (List.ofFn w) f = a := by
  change (8 : ℝ) ^ (List.ofFn w).length *
    (∫ x in range (wordMap (List.ofFn w)), f x ∂carpetMeasure) = a
  rw [List.length_ofFn, ← carpetMeasure_restrict_openWordCell, integral_congr_ae hf,
    integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    carpetMeasure_openWordCell, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    smul_eq_mul, inv_pow, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

theorem ambientWordMean_compLp_cellAveraging {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {φ : ℝ → ℝ} {L : NNReal} (hφ : LipschitzWith L φ) (hzero : φ 0 = 0)
    {n : ℕ} (w : Fin n → Fin 8) (f : CarpetLp p) :
    ambientWordMean p (List.ofFn w) (hφ.compLp hzero (cellAveraging p n f)) =
      φ (ambientWordMean p (List.ofFn w) f) := by
  apply ambientWordMean_eq_of_ae_eq_on_openWordCell w
  have h₁ : ∀ᵐ x ∂carpetMeasure.restrict (openWordCell w),
      (hφ.compLp hzero (cellAveraging p n f)) x = φ ((cellAveraging p n f) x) :=
    ae_restrict_of_ae (hφ.coeFn_compLp hzero (cellAveraging p n f))
  have h₂ := cellAveraging_ae_eq_on_openWordCell n f w
  filter_upwards [h₁, h₂] with x h₁ h₂
  exact h₁.trans (congrArg φ h₂)

theorem discreteCellEnergy_compLp_cellAveraging_le {p ρ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 ≤ p) (hρ : 0 ≤ ρ)
    {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (hzero : φ 0 = 0) (n : ℕ) (f : CarpetLp p) :
    discreteCellEnergy p ρ n (hφ.compLp hzero (cellAveraging p n f)) ≤ discreteCellEnergy p ρ n f := by
  classical
  unfold discreteCellEnergy
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro w _
  apply Finset.sum_le_sum
  intro v _
  rw [ambientWordMean_compLp_cellAveraging, ambientWordMean_compLp_cellAveraging]
  apply Real.rpow_le_rpow (abs_nonneg _) _ hp
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (lipschitzWith_iff_dist_le_mul.mp hφ _ _)

theorem IsGammaLimit.discreteCellEnergy_compLp_le {p ρ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p) (hρ : 0 ≤ ρ)
    {j : ℕ → ℕ} (hj : StrictMono j) {E : CarpetLp p → ℝ≥0∞}
    (hE : IsGammaLimit (fun n ↦ discreteCellEnergy p ρ (j n)) E)
    {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (hzero : φ 0 = 0) (f : CarpetLp p) :
    E (hφ.compLp hzero f) ≤ E f := by
  apply hE.apply_le_of_approximate_contraction
    (fun n g ↦ hφ.compLp hzero (cellAveraging p (j n) g)) (hφ.compLp hzero) _ _ f
  · intro x U hU
    have hpU : (hφ.compLp hzero) ⁻¹' U ∈ 𝓝 x :=
      (hφ.continuous_compLp hzero).tendsto x hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpU
    refine ⟨Metric.ball x (ε / 2), Metric.ball_mem_nhds x (half_pos hε), ?_⟩
    have ht := (cellAveraging_tendsto hp x).comp hj.tendsto_atTop
    filter_upwards [ht (Metric.ball_mem_nhds x (half_pos hε))] with n hn z hz
    apply hball
    change cellAveraging p (j n) x ∈ Metric.ball x (ε / 2) at hn
    rw [Metric.mem_ball] at hn hz ⊢
    let P := cellAveraging p (j n)
    change dist (P z) x < ε
    have hc : dist (P z) (P x) ≤ dist z x := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact norm_cellAveraging_le hp _ _
    exact (dist_triangle (P z) (P x) x).trans_lt (by linarith)
  · intro n x
    exact discreteCellEnergy_compLp_cellAveraging_le (zero_le_one.trans hp) hρ hφ hzero _ x


theorem discreteCellEnergy_eq_grid {p ρ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (n : ℕ) (f : CarpetLp p) :
    discreteCellEnergy p ρ n f = ENNReal.ofReal (ρ ^ n / 2 *
      ∑ w : Fin n → Fin 8, ∑ v ∈ gridNeighbors w,
        |ambientWordMean p (List.ofFn w) f - ambientWordMean p (List.ofFn v) f| ^ p) := by
  classical
  unfold discreteCellEnergy
  congr 2
  apply Finset.sum_congr rfl
  intro w _
  let m (v : Fin n → Fin 8) := ambientWordMean p (List.ofFn v) f
  have hs : Finset.univ.filter (fun v : Fin n → Fin 8 ↦ v ≠ w ∧
      (range (wordMap (List.ofFn w)) ∩ range (wordMap (List.ofFn v))).Nonempty) =
      (gridNeighbors w).erase w := by
    ext v
    rw [Finset.mem_filter, Finset.mem_erase, mem_gridNeighbors,
      gridNear_iff_inter_wordMap_nonempty (by simp)]
    simp only [Finset.mem_univ, true_and]
  rw [hs]
  have h := Finset.sum_erase_add (gridNeighbors w) (fun v ↦ |m w - m v| ^ p)
    (mem_gridNeighbors.mpr (gridNear_refl _))
  simpa only [m, sub_self, abs_zero, Real.zero_rpow hp.ne', add_zero] using h

theorem continuous_discreteCellEnergy {p ρ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (n : ℕ) : Continuous (discreteCellEnergy p ρ n) := by
  rw [show discreteCellEnergy p ρ n = fun f ↦ ENNReal.ofReal (ρ ^ n / 2 *
    ∑ w : Fin n → Fin 8, ∑ v ∈ gridNeighbors w,
      |ambientWordMean p (List.ofFn w) f - ambientWordMean p (List.ofFn v) f| ^ p) from
    funext (discreteCellEnergy_eq_grid hp n)]
  apply ENNReal.continuous_ofReal.comp
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro w _
  apply continuous_finsetSum
  intro v _
  exact (Real.continuous_rpow_const hp.le).comp
    (((ambientWordMean p (List.ofFn w)).continuous.sub
      (ambientWordMean p (List.ofFn v)).continuous).abs)

/-- The rescaled cell graphs have a subsequential Γ-limit on the ambient Lp space. -/
theorem exists_discreteCellEnergy_gammaLimit (p ρ : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ (j : ℕ → ℕ) (E : CarpetLp p → ℝ≥0∞),
      StrictMono j ∧ IsGammaLimit (fun n ↦ discreteCellEnergy p ρ (j n)) E := by
  let : Fact (ENNReal.ofReal p ≠ ∞) := ⟨ENNReal.ofReal_ne_top⟩
  exact exists_gammaLimit_subseq (discreteCellEnergy p ρ)

end CarpetEnergy
