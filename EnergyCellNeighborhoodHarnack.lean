import CarpetNeighborhoodBallCover
import EnergyBallHarnack
import EnergyNeighborhoodHarnackEstimate
import EnergyNonnegativeLocalMinimizer
import HarnackOpenCover

/-!
# Elliptic Harnack inequality on cell neighborhoods
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 3700000 in
/-- Lemma 4.7 in the regime in which the walk dimension is at most
the volume dimension, for energies with uniform first variations. -/
theorem exists_neighborhood_harnack_of_scalingFactor_le_one [Fact (1 ≤ ENNReal.ofReal p)]
    (hρ : E.scalingFactor ≤ 1) (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (hs : HasUniformSymmetricIncrement (fun f ↦ (E.energy f : ℝ))) :
    ∃ H ≥ (1 : ℝ), E.HasNeighborhoodHarnack H := by
  classical
  obtain ⟨A, H, hA, hH, hball⟩ := E.exists_ball_harnack_ae hρ h hc hs
  have hA₀ : 0 < A := zero_lt_one.trans hA
  let t : ℝ := 1 / (4 * A)
  have ht : 0 < t := by dsimp only [t]; positivity
  obtain ⟨L, hcover⟩ := exists_uniform_wordNeighborhood_ball_cover ht
  let N : ℕ := 25 * 8 ^ L
  refine ⟨H ^ N, one_le_pow₀ hH, fun n w hw f hf hf₀ ↦ ?_⟩
  let S := cellNeighborhood w 3
  let W := wordCellUnion (cellNeighborhood w 2)
  have hsub : W ⊆ wordCellUnion S := wordCellUnion_mono (cellNeighborhood_subset_succ w)
  obtain ⟨g, hg₀, hfg, hg⟩ := E.exists_nonnegative_minimizer_ae_eq_on_wordCellUnion S f hf hf₀
  have hproper : S ≠ Finset.univ := cellNeighborhood_ne_univ_of_disjoint_outerBoundary w hw
  have hextpos := carpetMeasure_wordCellUnion_compl_ne_zero hproper
  obtain ⟨z, hz, hcov⟩ := hcover n w
  let I := {u // u ∈ cellNeighborhood w 2} × (Fin L → Fin 8)
  let d := (1 / 3 : ℝ) ^ n
  let R := d / (2 * A)
  let B (i : I) := ball (z i) (R / 2)
  have hd₀ : 0 < d := by dsimp only [d]; positivity
  have hd₁ : d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hR : 0 < R := div_pos hd₀ (mul_pos (by norm_num) hA₀)
  have hR₁ : R ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hA₀)).mpr
    linarith
  have hAR : A * R = d / 2 := by
    dsimp only [R]
    field_simp [hA₀.ne']
  have hsame : R / 2 = t * d := by
    dsimp only [R, t]
    ring
  have hlarge (i : I) : ball (z i) (A * R) ⊆ (wordCellUnion Sᶜ)ᶜ := by
    rw [hAR]
    refine (ball_subset_ball (half_le_self hd₀.le)).trans ?_
    have hh := wordNeighborhood_thickening_subset_open_succ (k := 2) w (hz i)
    simpa only [wordNeighborhoodOpen, S, Finset.compl_eq_univ_sdiff] using hh
  have hlocal (i : I) :
      ∀ᵐ x ∂carpetMeasure.restrict (B i), ∀ᵐ y ∂carpetMeasure.restrict (B i),
        (g : CarpetLp p) x ≤ H * (g : CarpetLp p) y := by
    have hES : wordCellUnion Sᶜ ⊆ (ball (z i) (A * R))ᶜ :=
      fun _ hy hyB ↦ hlarge i hyB hy
    have hsmall : ball (z i) R ⊆ ball (z i) (A * R) :=
      ball_subset_ball (le_mul_of_one_le_left hR.le hA.le)
    have hne : carpetMeasure (ball (z i) R)ᶜ ≠ 0 := by
      intro hh
      exact hextpos (measure_mono_null (hES.trans (compl_subset_compl.mpr hsmall)) hh)
    exact hball (z i) R hR hR₁ hne g (MinimizesWithExterior.mono E hES hg) hg₀
  have hcov' : W ⊆ ⋃ i, B i := by simpa only [B, hsame] using hcov
  have hmeet (i : I) : (W ∩ B i).Nonempty := ⟨z i, hz i, mem_ball_self (half_pos hR)⟩
  have hcomparison := ae_pair_le_of_finite_openCover B (fun _ ↦ isOpen_ball)
    (isPreconnected_wordCellUnion_cellNeighborhood w 2) hcov' hmeet (g : CarpetLp p) hg₀ hH hlocal
  have hcard : Fintype.card I ≤ N := by
    simp only [I, N, Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (card_cellNeighborhood_le w 2)
  have hgW := hfg.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hcomparison, hgW] with x hx hx'
  filter_upwards [hx, hgW, ae_restrict_of_ae (s := W) hg₀] with y hy hy' hgy
  rw [← hx', ← hy']
  exact hy.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH hcard) hgy)

end CarpetEnergy.SelfSimilarPEnergy
