import EnergyApproximateCrossingPairs
import EnergyApproximateLogBound
import EnergyBallCapacityUpper
import EnergyLogSeparation
import EnergyNonnegativeGraphApproximation

/-!
# The Harnack comparison of upper and lower thresholds in a ball
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 5200000 in
/-- A large positive upper level and a small lower level cannot both
occur on positive measure in an inner ball of a minimizing profile. -/
theorem exists_ball_harnack_threshold_ratio
    (hρ : E.scalingFactor ≤ 1) (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (hs : HasUniformSymmetricIncrement (fun f ↦ (E.energy f : ℝ))) :
    ∃ A H : ℝ, 1 < A ∧ 1 ≤ H ∧
      ∀ (x : CarpetPoints) (R : ℝ), 0 < R → R ≤ 1 / 2 →
        carpetMeasure (ball x R)ᶜ ≠ 0 →
        ∀ f : E.domain, E.MinimizesWithExterior (ball x (A * R))ᶜ f →
          (∀ᵐ y ∂carpetMeasure, 0 ≤ (f : CarpetLp p) y) →
          ∀ a b : ℝ, 0 ≤ a → a < b →
            0 < (∫ y in ball x (R / 2), max (a - (f : CarpetLp p) y) 0 ∂carpetMeasure) →
            0 < (∫ y in ball x (R / 2), max ((f : CarpetLp p) y - b) 0 ∂carpetMeasure) →
            b ≤ H * a := by
  obtain ⟨A₀, c, hA₀, hc₀, hsep⟩ := E.exists_energy_lower_of_distance_spanning_gap hρ
  obtain ⟨A₁, C, hA₁, hC, hcut⟩ := E.exists_ball_capacity_cutoff
  obtain ⟨m, hm⟩ := exists_nat_ge p
  let s := carpetSimilarityDimension - E.walkDimension
  let A := A₁ * A₀
  let Q := ((2 * (m : ℝ)) / (p - 1)) ^ p
  let K := max 1 (Q * C * A₀ ^ s)
  let L := (K / c) ^ p⁻¹
  let H := Real.exp L
  have hA : 1 < A := hA₁.trans_le (le_mul_of_one_le_right (zero_lt_one.trans hA₁).le hA₀)
  have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
  have hL : 0 ≤ L := Real.rpow_nonneg (div_nonneg hK.le hc₀.le) _
  have hH : 1 ≤ H := Real.one_le_exp hL
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  refine ⟨A, H, hA, hH, fun x R hR hR₁ hout f hf hf₀ a b ha hab hlow hhigh ↦ ?_⟩
  let U := ball x (A * R)
  let V := ball x (A₀ * R)
  have hUV : ball x R ⊆ U := ball_subset_ball (le_mul_of_one_le_left hR.le hA.le)
  have hf' := MinimizesWithExterior.mono E (compl_subset_compl.mpr hUV) hf
  obtain ⟨u, hu₀, hu⟩ := E.exists_nonnegative_core_graph_approximation f hf₀
  have hsets := E.eventually_exists_distance_spanning_level_sets hR hout f hf' u hu a b hlow hhigh
  have hscale : 0 < A₀ * R := mul_pos (zero_lt_one.trans_le hA₀) hR
  obtain ⟨χ, hχ₁, hχs, hχ01, hχE⟩ := hcut x (A₀ * R) hscale
  have hχV (y : CarpetPoints) (hy : y ∈ V) : χ.val y = 1 :=
    hχ₁ y (ball_subset_ball (by linarith) hy)
  have hχU (y : CarpetPoints) (hy : y ∉ U) : χ.val y = 0 := by
    by_contra hne
    apply hy
    have hh := hχs (subset_tsupport _ (mem_support.mpr hne))
    simpa only [U, A, mul_assoc] using hh
  have hRp : 0 < R ^ s := Real.rpow_pos_of_pos hR _
  have hεbound (ε : ℝ) (hε : 0 < ε) : b + ε ≤ H * (a + ε) := by
    have hlogs := E.eventually_exists_log_core_energy_le h hc hs
      (show MeasurableSet U from isOpen_ball.measurableSet) (show IsOpen V from isOpen_ball)
      f hf u hu₀ hu χ hχ01 hχV hχU hε hRp m hm
    obtain ⟨n, hsetsn, hlogsn⟩ := (hsets.and hlogs).exists
    obtain ⟨S, T, hS, hT, hSd, hTd, hhigh', hlow'⟩ := hsetsn
    obtain ⟨g, hg, hgE⟩ := hlogsn
    have haε : 0 < a + ε := add_pos_of_nonneg_of_pos ha hε
    have hbε : 0 < b + ε := add_pos_of_nonneg_of_pos (ha.trans hab.le) hε
    have hloglt := Real.log_lt_log haε (show a + ε < b + ε by linarith)
    have hSlog (y : CarpetPoints) (hy : y ∈ S) : Real.log (b + ε) ≤ g.val y := by
      rw [hg]
      exact Real.log_le_log hbε (add_le_add (hhigh' y hy) le_rfl)
    have hTlog (y : CarpetPoints) (hy : y ∈ T) : g.val y ≤ Real.log (a + ε) := by
      rw [hg]
      exact Real.log_le_log (add_pos_of_nonneg_of_pos (hu₀ n y) hε) (add_le_add (hlow' y hy) le_rfl)
    let Δ := Real.log (b + ε) - Real.log (a + ε)
    have hΔ : 0 < Δ := sub_pos.mpr hloglt
    have hcost : c * R ^ s * Δ ^ p ≤ (E.energyMeasure (E.continuousCoreToDomain g)).real V :=
      hsep x R hR hR₁ S T hS hT hSd hTd g _ _ hloglt hSlog hTlog
    have hupper : (E.energyMeasure (E.continuousCoreToDomain g)).real V ≤ K * R ^ s := by
      apply hgE.trans
      change max (R ^ s) (Q * (E.energy (E.continuousCoreToDomain χ) : ℝ)) ≤ _
      apply max_le
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (Q * C * A₀ ^ s)) hRp.le
      · have hQ : 0 ≤ Q := Real.rpow_nonneg (div_nonneg (by positivity) (sub_nonneg.mpr E.one_lt_p.le)) _
        refine (mul_le_mul_of_nonneg_left hχE hQ).trans ?_
        rw [Real.mul_rpow (zero_le_one.trans hA₀) hR.le]
        have hh := mul_le_mul_of_nonneg_right (le_max_right 1 (Q * C * A₀ ^ s)) hRp.le
        convert hh using 1
        ring
    have hpow : Δ ^ p ≤ K / c := by
      apply (le_div_iff₀ hc₀).mpr
      apply (mul_le_mul_iff_left₀ hRp).mp
      calc
        Δ ^ p * c * R ^ s = c * R ^ s * Δ ^ p := by ring
        _ ≤ K * R ^ s := hcost.trans hupper
    have hdL := Real.rpow_le_rpow (Real.rpow_nonneg hΔ.le _) hpow (inv_nonneg.mpr hp.le)
    rw [Real.rpow_rpow_inv hΔ.le hp.ne'] at hdL
    have hh := Real.exp_le_exp.mpr hdL
    change Real.exp (Real.log (b + ε) - Real.log (a + ε)) ≤ H at hh
    rw [Real.exp_sub, Real.exp_log hbε, Real.exp_log haε] at hh
    exact (div_le_iff₀ haε).mp hh
  have hδ : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply le_of_tendsto_of_tendsto (b := atTop) (f := fun n : ℕ ↦ b + 1 / ((n : ℝ) + 1))
    (g := fun n : ℕ ↦ H * (a + 1 / ((n : ℝ) + 1)))
  · simpa only [add_zero] using hδ.const_add b
  · simpa only [add_zero] using (hδ.const_add a).const_mul H
  · exact Eventually.of_forall fun n ↦ hεbound _ (by positivity)

end CarpetEnergy.SelfSimilarPEnergy
