import EnergyPairDependence
import EnergyPiecewiseHarmonic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Reduction of pairwise dependence to piecewise harmonic functions

Energy convergence implies convergence in measure of the density roots
of the differences. Passing to almost-everywhere convergent subsequences
then transfers rational approximate relations from approximants to
the original pair.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)
variable (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
variable (hdom : ∀ f, E.energyMeasure f ≪ μ)
include hdom

theorem eLpNorm_energyDensityRoot (v : E.domain) :
    eLpNorm (E.energyDensityRoot μ v) (ENNReal.ofReal p) μ =
      ENNReal.ofReal (E.rootSeminorm v) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top (E.measurable_energyDensityRoot μ v).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  let : (E.energyMeasure v).HaveLebesgueDecomposition μ :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  have he : (∫⁻ x, ‖E.energyDensityRoot μ v x‖ₑ ^ p ∂μ) = E.energyMeasure v univ := by
    rw [← Measure.lintegral_rnDeriv (hdom v)]
    apply lintegral_congr_ae
    filter_upwards [(E.energyMeasure v).rnDeriv_lt_top μ] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (E.energyDensityRoot_nonneg μ v x),
      ENNReal.ofReal_rpow_of_nonneg (E.energyDensityRoot_nonneg μ v x) hp.le]
    exact E.ofReal_energyDensityRoot_pow μ v hx.ne
  rw [he, E.energyMeasure_univ, E.rootSeminorm_apply, one_div]
  have hr := ENNReal.ofReal_rpow_of_nonneg (NNReal.coe_nonneg (E.energy v)) (inv_nonneg.mpr hp.le)
  simpa only [ENNReal.ofReal_coe_nnreal] using hr


theorem tendstoInMeasure_energyDensityRoot_zero (v : ℕ → E.domain)
    (hv : Tendsto (fun n ↦ E.rootSeminorm (v n)) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ↦ E.energyDensityRoot μ (v n)) atTop (fun _ ↦ 0) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := ENNReal.ofReal p)
    (ENNReal.ofReal_ne_zero_iff.mpr hp)
  simp only [show (fun _ : CarpetPoints ↦ (0 : ℝ)) = 0 from rfl, sub_zero,
    E.eLpNorm_energyDensityRoot μ hdom]
  have ht := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hv
  change Tendsto (fun n ↦ ENNReal.ofReal (E.rootSeminorm (v n))) atTop (𝓝 (ENNReal.ofReal 0)) at ht
  rwa [ENNReal.ofReal_zero] at ht

private theorem ae_energyDensityRoot_pair_approximation (f g u v : E.domain) :
    ∀ᵐ x ∂μ, ∀ a b : ℚ, E.energyDensityRoot μ (a • f + b • g) x ≤
      E.energyDensityRoot μ (a • u + b • v) x +
        ‖a‖ * E.energyDensityRoot μ (f - u) x + ‖b‖ * E.energyDensityRoot μ (g - v) x := by
  refine ae_all_iff.mpr fun a ↦ ae_all_iff.mpr fun b ↦ ?_
  let A := a • u + b • v
  let B := a • (f - u)
  let C := b • (g - v)
  have he : a • f + b • g = A + (B + C) := by dsimp only [A, B, C]; simp only [smul_sub]; abel
  have hA := E.ae_energyDensityRoot_add_le μ hdom A (B + C)
  have hBC := E.ae_energyDensityRoot_add_le μ hdom B C
  have hB := E.ae_energyDensityRoot_smul μ (a : ℝ) (f - u)
  have hC := E.ae_energyDensityRoot_smul μ (b : ℝ) (g - v)
  rw [Rat.cast_smul_eq_qsmul, ← Real.norm_eq_abs, Rat.norm_cast_real] at hB hC
  filter_upwards [hA, hBC, hB, hC] with x hA hBC hB hC
  rw [he]
  change E.energyDensityRoot μ B x = _ at hB
  change E.energyDensityRoot μ C x = _ at hC
  linarith only [hA, hBC, hB, hC]

/-- The pairwise dependence inequality is closed under convergence in the
energy seminorm of both components. -/
theorem ae_pairDependence_of_energy_approximation (f g : E.domain)
    (u v : ℕ → E.domain)
    (hu : Tendsto (fun n ↦ E.rootSeminorm (f - u n)) atTop (𝓝 0))
    (hv : Tendsto (fun n ↦ E.rootSeminorm (g - v n)) atTop (𝓝 0))
    (h : ∀ n, ∀ᵐ x ∂μ, ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
      E.energyDensityRoot μ (a • u n + b • v n) x ≤ ε * (‖a‖ + ‖b‖)) :
    ∀ᵐ x ∂μ, ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
      E.energyDensityRoot μ (a • f + b • g) x ≤ ε * (‖a‖ + ‖b‖) := by
  obtain ⟨i, hi, hui⟩ := (E.tendstoInMeasure_energyDensityRoot_zero μ hdom _ hu).exists_seq_tendsto_ae
  obtain ⟨j, hj, hvj⟩ :=
    ((E.tendstoInMeasure_energyDensityRoot_zero μ hdom _ hv).comp hi.tendsto_atTop).exists_seq_tendsto_ae
  have ha := ae_all_iff.mpr (fun n ↦ E.ae_energyDensityRoot_pair_approximation μ hdom f g (u n) (v n))
  filter_upwards [hui, hvj, ha, ae_all_iff.mpr h] with x hux hvx hax hx
  intro ε hε
  have ht₁ := (hux.comp hj.tendsto_atTop).eventually_lt_const (half_pos hε)
  have ht₂ := hvx.eventually_lt_const (half_pos hε)
  obtain ⟨n, hn₁, hn₂⟩ := (ht₁.and ht₂).exists
  let k := i (j n)
  obtain ⟨a, b, hpos, hab⟩ := hx k (ε / 2) (half_pos hε)
  refine ⟨a, b, hpos, (hax k a b).trans ?_⟩
  have h₁ := mul_le_mul_of_nonneg_left hn₁.le (norm_nonneg a)
  have h₂ := mul_le_mul_of_nonneg_left hn₂.le (norm_nonneg b)
  change ‖a‖ * E.energyDensityRoot μ (f - u k) x ≤ _ at h₁
  change ‖b‖ * E.energyDensityRoot μ (g - v k) x ≤ _ at h₂
  linarith only [hab, h₁, h₂]

/-- Proposition 5.4 in rational density-root form. It suffices to prove
pairwise dependence on the piecewise harmonic core. -/
theorem hasPairwiseEnergyDependence_of_piecewiseHarmonic
    (h : ∀ f g : E.domain,
      (∃ n : ℕ, ∀ w : Fin n → Fin 8, E.IsInteriorHarmonic (E.pullbackWord (List.ofFn w) f)) →
      (∃ n : ℕ, ∀ w : Fin n → Fin 8, E.IsInteriorHarmonic (E.pullbackWord (List.ofFn w) g)) →
      ∀ᵐ x ∂μ, ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
        E.energyDensityRoot μ (a • f + b • g) x ≤ ε * (‖a‖ + ‖b‖)) :
    E.HasPairwiseEnergyDependence μ := by
  intro f g
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hd (f : E.domain) :
      ∃ u : ℕ → E.domain,
        (∀ n, ∃ k : ℕ, ∀ w : Fin k → Fin 8, E.IsInteriorHarmonic (E.pullbackWord (List.ofFn w) (u n))) ∧
        Tendsto (fun n ↦ E.rootSeminorm (f - u n)) atTop (𝓝 0) := by
    choose k u hu he using fun n ↦ E.exists_piecewiseHarmonic_graph_approximation f _ (hε n)
    refine ⟨u, fun n ↦ ⟨k n, hu n⟩, ?_⟩
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ apply_nonneg _ _)
    intro n
    change E.rootSeminorm (f - u n) ≤ ε n
    rw [map_sub_rev]
    exact (E.rootSeminorm_le_graphSeminorm _).trans (he n).le
  obtain ⟨u, hpu, hu⟩ := hd f
  obtain ⟨v, hpv, hv⟩ := hd g
  exact E.ae_pairDependence_of_energy_approximation μ hdom f g u v hu hv
    (fun n ↦ h (u n) (v n) (hpu n) (hpv n))

end CarpetEnergy.SelfSimilarPEnergy
