import EnergyFoldingAmplification

/-!
# Uniform convexity of the energy root on the continuous core

The rescaled folding maps are linear and their graph norms converge to
the energy root. The graph norm's midpoint deficit is uniform, so it
persists in the limit.
-/

open Filter Function Set
open scoped Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem exists_root_midpoint_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ f g : E.continuousCore,
      E.rootSeminorm (E.continuousCoreToDomain f) ≤ 1 →
      E.rootSeminorm (E.continuousCoreToDomain g) ≤ 1 →
      ε ≤ E.rootSeminorm (E.continuousCoreToDomain (f - g)) →
      E.rootSeminorm (E.continuousCoreToDomain ((1 / 2 : ℝ) • (f + g))) ≤ 1 - δ := by
  obtain ⟨δ, hδ, hUC⟩ := exists_forall_closed_ball_dist_add_le_two_sub E.GraphDomain
    (show 0 < ε / 4 by positivity)
  refine ⟨δ / 2, half_pos hδ, fun f g hf hg hd ↦ ?_⟩
  let u (n : ℕ) := E.scaledFold n f
  let v (n : ℕ) := E.scaledFold n g
  let r (n : ℕ) := max 1 (max ‖u n‖ ‖v n‖)
  have hr : Tendsto r atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).max
      ((E.scaledFold_norm_tendsto f).max (E.scaledFold_norm_tendsto g))
    simpa only [max_eq_left (max_le hf hg)] using h
  have hu (n : ℕ) : ‖u n‖ ≤ r n := (le_max_left _ _).trans (le_max_right _ _)
  have hv (n : ℕ) : ‖v n‖ ≤ r n := (le_max_right _ _).trans (le_max_right _ _)
  have hr₀ (n : ℕ) : 0 < r n := zero_lt_one.trans_le (le_max_left _ _)
  have hdist : Tendsto (fun n ↦ ‖u n - v n‖) atTop
      (𝓝 (E.rootSeminorm (E.continuousCoreToDomain (f - g)))) := by
    simpa only [map_sub, u, v] using E.scaledFold_norm_tendsto (f - g)
  have hε' : ε / 2 < E.rootSeminorm (E.continuousCoreToDomain (f - g)) :=
    (half_lt_self hε).trans_le hd
  have hmid : Tendsto (fun n ↦ ‖(1 / 2 : ℝ) • (u n + v n)‖) atTop
      (𝓝 (E.rootSeminorm (E.continuousCoreToDomain ((1 / 2 : ℝ) • (f + g))))) := by
    simpa only [map_smul, map_add, u, v] using E.scaledFold_norm_tendsto ((1 / 2 : ℝ) • (f + g))
  have hb : ∀ᶠ n in atTop, ‖(1 / 2 : ℝ) • (u n + v n)‖ ≤ r n * (1 - δ / 2) := by
    filter_upwards [hr.eventually_lt_const (by norm_num : (1 : ℝ) < 2), hdist.eventually_const_lt hε']
      with n hr₂ ht
    have hleft : ‖(r n)⁻¹ • u n‖ ≤ 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.mpr (hr₀ n).le), inv_mul_le_iff₀ (hr₀ n), mul_one]
      exact hu n
    have hright : ‖(r n)⁻¹ • v n‖ ≤ 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.mpr (hr₀ n).le), inv_mul_le_iff₀ (hr₀ n), mul_one]
      exact hv n
    have hsep : ε / 4 ≤ ‖(r n)⁻¹ • u n - (r n)⁻¹ • v n‖ := by
      rw [← smul_sub, norm_smul_of_nonneg (inv_nonneg.mpr (hr₀ n).le), ← div_eq_inv_mul]
      apply (le_div_iff₀ (hr₀ n)).mpr
      have hh := mul_le_mul_of_nonneg_left hr₂.le (show 0 ≤ ε / 4 by positivity)
      linarith only [hh, ht]
    have hh := hUC hleft hright hsep
    rw [← smul_add, norm_smul_of_nonneg (inv_nonneg.mpr (hr₀ n).le), ← div_eq_inv_mul] at hh
    have hh' := (div_le_iff₀ (hr₀ n)).mp hh
    rw [norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith only [hh']
  have hz := le_of_tendsto_of_tendsto hmid (hr.mul_const (1 - δ / 2)) hb
  simpa only [one_mul] using hz

theorem root_midpoint_lt_one (f g : E.continuousCore)
    (hf : E.rootSeminorm (E.continuousCoreToDomain f) ≤ 1)
    (hg : E.rootSeminorm (E.continuousCoreToDomain g) ≤ 1)
    (hd : 0 < E.rootSeminorm (E.continuousCoreToDomain (f - g))) :
    E.rootSeminorm (E.continuousCoreToDomain ((1 / 2 : ℝ) • (f + g))) < 1 := by
  obtain ⟨δ, hδ, h⟩ := E.exists_root_midpoint_gap _ hd
  exact (h f g hf hg le_rfl).trans_lt (sub_lt_self _ hδ)

end CarpetEnergy.SelfSimilarPEnergy
