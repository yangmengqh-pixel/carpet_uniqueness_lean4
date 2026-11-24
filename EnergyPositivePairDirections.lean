import EnergyCellDependence

/-!
# A positive-measure set of independent directions

Failure of pairwise dependence yields one positive threshold valid on
a positive-measure Borel set. This gives a simultaneous lower bound
for the Radon–Nikodym derivatives of all rational combinations.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem exists_positive_pair_direction_bound (f g : E.domain)
    (h : ¬ (∀ᵐ x ∂(E.energyMeasure f + E.energyMeasure g),
      ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
        E.energyDensityRoot (E.energyMeasure f + E.energyMeasure g) (a • f + b • g) x ≤
          ε * (‖a‖ + ‖b‖))) :
    ∃ (A : Set CarpetPoints) (d : ℝ), MeasurableSet A ∧
      0 < (E.energyMeasure f + E.energyMeasure g) A ∧ 0 < d ∧
      ∀ x ∈ A, ∀ a b : ℚ, ENNReal.ofReal ((d * (‖a‖ + ‖b‖)) ^ p) ≤
        (E.energyMeasure (a • f + b • g)).rnDeriv (E.energyMeasure f + E.energyMeasure g) x := by
  classical
  let μ := E.energyMeasure f + E.energyMeasure g
  let c (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hc (n : ℕ) : 0 < c n := by dsimp only [c]; positivity
  have hlim : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let A (n : ℕ) : Set CarpetPoints := {x | ∀ a b : ℚ, 0 < ‖a‖ + ‖b‖ →
    c n * (‖a‖ + ‖b‖) < E.energyDensityRoot μ (a • f + b • g) x}
  have hmeas (n : ℕ) : MeasurableSet (A n) := by
    rw [show A n = ⋂ a : ℚ, ⋂ b : ℚ, ⋂ _ : 0 < ‖a‖ + ‖b‖,
      {x | c n * (‖a‖ + ‖b‖) < E.energyDensityRoot μ (a • f + b • g) x} from
        by ext x; simp [A]]
    exact MeasurableSet.iInter fun a ↦ MeasurableSet.iInter fun b ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_lt measurable_const (E.measurable_energyDensityRoot _ _)
  have hex : ∃ n, 0 < μ (A n) := by
    by_contra! hn
    have hae : ∀ᵐ x ∂μ, ∀ n, x ∉ A n := ae_all_iff.mpr fun n ↦
      measure_eq_zero_iff_ae_notMem.mp (nonpos_iff_eq_zero.mp (hn n))
    apply h
    filter_upwards [hae] with x hx
    intro ε hε
    obtain ⟨n, hnε⟩ := (hlim.eventually_lt_const hε).exists
    have hb := hx n
    change ¬ ∀ a b : ℚ, 0 < ‖a‖ + ‖b‖ →
      c n * (‖a‖ + ‖b‖) < E.energyDensityRoot μ (a • f + b • g) x at hb
    push Not at hb
    obtain ⟨a, b, hab, hle⟩ := hb
    exact ⟨a, b, hab, hle.trans (mul_le_mul_of_nonneg_right hnε.le hab.le)⟩
  obtain ⟨n, hn⟩ := hex
  refine ⟨A n, c n, hmeas n, hn, hc n, fun x hx a b ↦ ?_⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  by_cases hab : 0 < ‖a‖ + ‖b‖
  · by_cases ht : (E.energyMeasure (a • f + b • g)).rnDeriv μ x = ∞
    · exact ht.symm ▸ le_top
    rw [← E.ofReal_energyDensityRoot_pow μ _ ht]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (mul_nonneg (hc n).le hab.le)
      (show c n * (‖a‖ + ‖b‖) ≤ _ from (hx a b hab).le) hp.le)
  · have hz : ‖a‖ + ‖b‖ = 0 := le_antisymm (le_of_not_gt hab) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [hz, mul_zero, Real.zero_rpow hp.ne', ENNReal.ofReal_zero]
    exact bot_le

end CarpetEnergy.SelfSimilarPEnergy
