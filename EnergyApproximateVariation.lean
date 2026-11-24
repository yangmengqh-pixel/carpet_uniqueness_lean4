import EnergyApproximateMinimum

/-!
# Vanishing first variations along graph approximations of minimizers
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 3600000 in
/-- Bounded admissible directions have vanishing first variations along
graph approximations of a constrained minimizer, even when the direction
varies with the approximant. -/
theorem tendsto_variation_zero_of_graph_tendsto
    (h : E.HasLinearFirstVariations)
    (hs : HasUniformSymmetricIncrement (fun f ↦ (E.energy f : ℝ)))
    {A : Set CarpetPoints} (f : E.domain) (hf : E.MinimizesWithExterior A f)
    (u v : ℕ → E.domain)
    (hu : Tendsto (fun n ↦ E.toGraph (u n)) atTop (𝓝 (E.toGraph f)))
    (hv : ∀ n, ∀ᵐ x ∂carpetMeasure.restrict A, (v n : CarpetLp p) x = 0)
    {G : ℝ} (hG : ∀ᶠ n in atTop, E.rootSeminorm (v n) ≤ G) :
    Tendsto (fun n ↦ E.variation h (u n) (v n)) atTop (𝓝 0) := by
  let δ (n : ℕ) := ‖E.toGraph (u n) - E.toGraph f‖
  let B := max G (E.rootSeminorm f + 1)
  let K := 2 * p * (2 * B + 1) ^ (p - 1)
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hu
  have hfB : E.rootSeminorm f ≤ B := (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hB₀ : 0 ≤ B := (apply_nonneg E.rootSeminorm _).trans hfB
  have henergy (g : E.domain) (hg : E.rootSeminorm g ≤ B) : (E.energy g : ℝ) ≤ B ^ p := by
    have hh := Real.rpow_le_rpow (apply_nonneg E.rootSeminorm _) hg hp.le
    rwa [E.rootSeminorm_apply, Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'] at hh
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let a := p * η / (4 * (B ^ p + 1))
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨t, ht, ht₁, hdef⟩ := E.abs_variation_le_of_two_sided_defect h hs ha
  have hd : Tendsto (fun n ↦ K * δ n / t) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (tendsto_const_nhds.mul hδ).div_const t
  filter_upwards [hG, hδ.eventually_lt_const zero_lt_one,
    hd.eventually_lt_const (half_pos (mul_pos hp hη))] with n hvn hδn hdₙ
  have hgap : E.rootSeminorm (u n - f) ≤ δ n := by
    change _ ≤ ‖E.toGraph (u n - f)‖
    rw [E.norm_toGraph]
    exact E.rootSeminorm_le_graphSeminorm _
  have huB : E.rootSeminorm (u n) ≤ B := by
    have hsum := map_add_le_add E.rootSeminorm (u n - f) f
    rw [sub_add_cancel] at hsum
    exact (show E.rootSeminorm (u n) ≤ E.rootSeminorm f + 1 by linarith).trans (le_max_right _ _)
  have hvB : E.rootSeminorm (v n) ≤ B := hvn.trans (le_max_left _ _)
  have hdir (s : ℝ) (hs' : |s| ≤ 1) :
      (E.energy (u n) : ℝ) ≤ (E.energy (u n + s • v n) : ℝ) + K * δ n := by
    have hzero : ∀ᵐ x ∂carpetMeasure.restrict A, ((s • v n : E.domain) : CarpetLp p) x = 0 := by
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul s (v n : CarpetLp p)), hv n] with x hx hzero
      exact hx.trans (by rw [Pi.smul_apply, hzero, smul_zero])
    have hr : E.rootSeminorm (s • v n) ≤ B := by
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (apply_nonneg E.rootSeminorm _) hs').trans hvB
    have hh := E.energy_le_perturbation_add_defect f (u n) (s • v n) hf hzero hfB huB hr hgap hδn.le
    convert hh using 1
    dsimp only [K]
    ring
  have hP := hdir t (by rwa [abs_of_pos ht])
  have hM := hdir (-t) (by rwa [abs_neg, abs_of_pos ht])
  have htneg : (-t) • v n = -(t • v n) := by
    apply Subtype.ext
    change (-t) • (v n : CarpetLp p) = -(t • (v n : CarpetLp p))
    exact neg_smul _ _
  rw [htneg, ← sub_eq_add_neg] at hM
  have hV := hdef (u n) (v n) (K * δ n) hP hM
  have hcoef : a * ((E.energy (u n) : ℝ) + (E.energy (v n) : ℝ)) ≤ p * η / 2 := by
    calc
      _ ≤ a * (2 * (B ^ p + 1)) := mul_le_mul_of_nonneg_left
        (by linarith only [henergy (u n) huB, henergy (v n) hvB]) ha.le
      _ = _ := by
        dsimp only [a]
        have hh : B ^ p + 1 ≠ 0 := by positivity
        field_simp [hh]
        ring
  rw [Real.dist_eq, sub_zero]
  exact (mul_lt_mul_iff_right₀ hp).mp (by linarith only [hV, hcoef, hdₙ])

end CarpetEnergy.SelfSimilarPEnergy
