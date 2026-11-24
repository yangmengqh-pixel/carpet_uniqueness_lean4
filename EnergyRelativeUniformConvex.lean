import EnergyRelativeGraphSeminorm
import EnergyRelativeMidpoint
import SeminormPowerUniformConvex
import CarpetLpMidpoint

/-!
# Uniform convexity of the renormalized graph norm
-/

open Filter
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

theorem renormalizedGammaLimit_graph_uniformConvex
    {j : ℕ → ℕ} (hj : StrictMono j) {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F)
    {l : Filter ℕ} [l.NeBot] {G : E.domain → ℝ}
    (hlim : ∀ f, Tendsto (fun n ↦ renormalizationMean E.scalingFactor E.pullback
      (fun v : E.domain ↦ (F v).toReal) n f) l (𝓝 (G f)))
    (S : Seminorm ℝ E.domain) (hS : ∀ f, G f = S f ^ p)
    (T : Seminorm ℝ E.domain) (hT : T = E.relativeGraphSeminorm S) :
    letI := T.toAddGroupSeminorm.toSeminormedAddCommGroup
    UniformConvexSpace E.domain := by
  have hp := zero_lt_one.trans E.one_lt_p
  apply uniformConvexSpace_of_power_midpoint T E.one_lt_p
  intro ε hε
  obtain ⟨C, hC, hscalar⟩ := exists_abs_rpow_midpoint_deficit E.one_lt_p hε
  have hG := E.renormalizedGammaLimit_midpoint_deficit hj hF hlim hε.le hC hscalar
  have hpow (f : E.domain) : T f ^ p = G f + ‖(f : CarpetLp p)‖ ^ p := by
    rw [hT, E.relativeGraphSeminorm_apply, Real.rpow_inv_rpow
      (add_nonneg (Real.rpow_nonneg (apply_nonneg S _) _) (Real.rpow_nonneg (norm_nonneg _) _)) hp.ne', hS]
  refine ⟨C, hC, fun f g ↦ ?_⟩
  simp only [hpow]
  have hLp := carpetLp_rpow_midpoint_deficit E.one_lt_p hscalar (f : CarpetLp p) (g : CarpetLp p)
  have he := add_le_add (hG f g) hLp
  change _ + (‖(↑(f - g) : CarpetLp p)‖ ^ p + C * ‖(↑((1 / 2 : ℝ) • (f + g)) : CarpetLp p)‖ ^ p) ≤ _ at he
  nlinarith only [he]

end CarpetEnergy.SelfSimilarPEnergy
