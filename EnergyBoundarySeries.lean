import EnergyBottomStrip

/-!
# Summing boundary-scale corrections

The boundary strip estimates give uniform convergence and convergence
in the energy graph norm for the same series.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private noncomputable def continuousLpCLM [Fact (1 ≤ ENNReal.ofReal p)] :
    C(CarpetPoints, ℝ) →L[ℝ] CarpetLp p :=
  (continuousLpLinear p).mkContinuous 1 fun f ↦ by
    rw [one_mul]
    exact norm_carpetLp_le_of_ae_bound _ (norm_nonneg _)
      ((continuousLp_ae_eq p f).mono fun x hx ↦ by
        change ‖continuousLp p f x‖ ≤ ‖f‖
        rw [hx]
        exact f.norm_coe_le_norm x)

/-- The sum of a sequence of scaled bottom-strip corrections is a continuous
domain function. Both modes of convergence follow from geometric bounds. -/
theorem exists_hasSum_bottom_strips (δ : C(CarpetPoints, ℝ)) (hδ : continuousLp p δ ∈ E.domain)
    (u : ℕ → C(CarpetPoints, ℝ)) (hu : ∀ n, continuousLp p (u n) ∈ E.domain)
    (hL : ∀ n, ‖u n‖ ≤ ((3 : ℝ) ^ n)⁻¹ * ‖δ‖)
    (hE : ∀ n, (E.energy ⟨continuousLp p (u n), hu n⟩ : ℝ) ≤
      (E.scalingFactor * (3 : ℝ) ^ (1 - p)) ^ n * (E.energy ⟨continuousLp p δ, hδ⟩ : ℝ)) :
    ∃ v : C(CarpetPoints, ℝ), continuousLp p v ∈ E.domain ∧ HasSum u v := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let q := E.scalingFactor * (3 : ℝ) ^ (1 - p)
  have hq₀ : 0 ≤ q := mul_nonneg E.isScalingFactor_scalingFactor.1.le (Real.rpow_nonneg (by norm_num) _)
  have hq₁ : q < 1 := E.scalingFactor_mul_three_rpow_lt_one
  let b := max ((3 : ℝ)⁻¹) (q ^ p⁻¹)
  have hb₀ : 0 ≤ b := (show 0 ≤ (3 : ℝ)⁻¹ by norm_num).trans (le_max_left _ _)
  have hb₁ : b < 1 := max_lt (by norm_num) (Real.rpow_lt_one hq₀ hq₁ (inv_pos.mpr hp))
  let d : E.domain := ⟨continuousLp p δ, hδ⟩
  let g (n : ℕ) : E.domain := ⟨continuousLp p (u n), hu n⟩
  have hnorm (n : ℕ) : ‖u n‖ ≤ b ^ n * ‖δ‖ := by
    have hcoef : ((3 : ℝ) ^ n)⁻¹ ≤ b ^ n := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by norm_num) (le_max_left _ _) _
    exact (hL n).trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
  have hroot (n : ℕ) : E.rootSeminorm (g n) ≤ b ^ n * E.rootSeminorm d := by
    rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
    have hh := Real.rpow_le_rpow (NNReal.coe_nonneg (E.energy (g n))) (hE n)
      (inv_nonneg.mpr hp.le)
    rw [Real.mul_rpow (pow_nonneg hq₀ _) (NNReal.coe_nonneg (E.energy d)),
      ← Real.rpow_natCast_mul hq₀, mul_comm (n : ℝ), Real.rpow_mul_natCast hq₀] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.rpow_nonneg hq₀ _) (le_max_right _ _) _)
      (Real.rpow_nonneg (NNReal.coe_nonneg _) _))
  let M := ((E.rootSeminorm d) ^ p + ‖δ‖ ^ p) ^ p⁻¹
  have hgraph (n : ℕ) : ‖E.toGraph (g n)‖ ≤ b ^ n * M := by
    have hm : ‖(g n : CarpetLp p)‖ ≤ b ^ n * ‖δ‖ :=
      (norm_carpetLp_le_of_ae_bound _ (norm_nonneg _)
        ((continuousLp_ae_eq p (u n)).mono fun x hx ↦ by
          rw [hx]
          exact (u n).norm_coe_le_norm x)).trans (hnorm n)
    apply (E.graphSeminorm_le_of_le (g n) hm (hroot n)).trans_eq
    have hn : 0 ≤ b ^ n := pow_nonneg hb₀ _
    rw [Real.mul_rpow hn (apply_nonneg _ _), Real.mul_rpow hn (norm_nonneg _),
      ← mul_add, Real.mul_rpow (Real.rpow_nonneg hn _) (by positivity),
      Real.rpow_rpow_inv hn hp.ne']
  have hs := summable_geometric_of_lt_one hb₀ hb₁
  have hgu : Summable (fun n ↦ E.toGraph (g n)) := (hs.mul_right M).of_norm_bounded hgraph
  have hsu : Summable u := (hs.mul_right ‖δ‖).of_norm_bounded hnorm
  let v := ∑' n, u n
  let z := ∑' n, E.toGraph (g n)
  have h₁ : HasSum (fun n ↦ continuousLp p (u n)) (continuousLp p v) :=
    (continuousLpCLM (p := p)).hasSum hsu.hasSum
  have h₂ : HasSum (fun n ↦ continuousLp p (u n)) (E.graphToDomain z : CarpetLp p) :=
    E.graphInclusion.hasSum hgu.hasSum
  exact ⟨v, (h₁.unique h₂).symm ▸ (E.graphToDomain z).property, hsu.hasSum⟩

end CarpetEnergy.SelfSimilarPEnergy
