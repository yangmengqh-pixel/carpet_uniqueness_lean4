import EnergyApproximation
import EnergyLocalMidpointDeficit
import CarpetCrossingCapacity

/-!
# Nonnegative continuous approximation in the graph norm
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3100000 in
/-- Nonnegative domain functions can be approximated in graph norm by
nonnegative continuous profiles. -/
theorem exists_nonnegative_core_graph_approximation
    (f : E.domain) (hf : ∀ᵐ x ∂carpetMeasure, 0 ≤ (f : CarpetLp p) x) :
    ∃ v : ℕ → E.continuousCore, (∀ n x, 0 ≤ (v n).val x) ∧
      Tendsto (fun n ↦ E.toGraph (E.continuousCoreToDomain (v n))) atTop (𝓝 (E.toGraph f)) := by
  let δ (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδ₁ (n : ℕ) : δ n ≤ 1 := (div_le_one (by positivity)).mpr
    (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hδt : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose u hu hD using fun n ↦ E.regular_graph f (δ n) (hδ n)
  let q (n : ℕ) : E.continuousCore := ⟨u n, hu n⟩
  let d (n : ℕ) := E.continuousCoreToDomain (q n)
  choose v hv hval henergy using fun n ↦ E.exists_continuous_comp_energy_le_mul
    (q n).val (q n).property Lp.lipschitzWith_pos_part
  let g (n : ℕ) : E.continuousCore := ⟨v n, hv n⟩
  let e (n : ℕ) := E.continuousCoreToDomain (g n)
  have hE (n : ℕ) : (E.energy (e n) : ℝ) ≤ (E.energy (d n) : ℝ) := by
    change (E.energy ⟨continuousLp p (v n), hv n⟩ : ℝ) ≤
      (E.energy ⟨continuousLp p (q n).val, (q n).property⟩ : ℝ)
    simpa only [NNReal.coe_one, Real.one_rpow, one_mul] using henergy n
  have hv' (n : ℕ) (x : CarpetPoints) : (g n).val x = max ((q n).val x) 0 := hval n x
  have hnorm (n : ℕ) : ‖(e n : CarpetLp p)‖ ≤ ‖(d n : CarpetLp p)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [continuousLp_ae_eq p (g n).val, continuousLp_ae_eq p (q n).val] with x ha hb
    change ‖continuousLp p (g n).val x‖ ≤ ‖continuousLp p (q n).val x‖
    rw [ha, hb, hv', Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hp := zero_lt_one.trans E.one_lt_p
  have hbnd (n : ℕ) : E.graphSeminorm (e n) ≤ ‖E.toGraph f‖ + 1 := by
    have hb : E.graphSeminorm (e n) ≤ E.graphSeminorm (d n) := by
      simp only [E.graphSeminorm_apply, energyGraphNorm]
      exact Real.rpow_le_rpow (by positivity)
        (add_le_add (hE n) (Real.rpow_le_rpow (norm_nonneg _) (hnorm n) hp.le)) (inv_nonneg.mpr hp.le)
    apply hb.trans
    rw [← E.norm_toGraph]
    have he : ‖E.toGraph (d n) - E.toGraph f‖ < δ n := hD n
    exact (norm_le_norm_sub_add _ _).trans (by linarith [hδ₁ n])
  have hdist (n : ℕ) : ‖(e n : CarpetLp p) - (f : CarpetLp p)‖ ≤
      ‖(d n : CarpetLp p) - (f : CarpetLp p)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (e n : CarpetLp p) (f : CarpetLp p),
      Lp.coeFn_sub (d n : CarpetLp p) (f : CarpetLp p),
      continuousLp_ae_eq p (g n).val, continuousLp_ae_eq p (q n).val, hf] with x he hd hgn hqn hfx
    rw [he, hd, Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
    change |continuousLp p (g n).val x - (f : CarpetLp p) x| ≤
      |continuousLp p (q n).val x - (f : CarpetLp p) x|
    rw [hgn, hqn, hv']
    have hh := Lp.lipschitzWith_pos_part.dist_le_mul ((q n).val x) ((f : CarpetLp p) x)
    simpa only [Real.dist_eq, max_eq_left hfx, NNReal.coe_one, one_mul] using hh
  have hlim : Tendsto (fun n ↦ (e n : CarpetLp p)) atTop (𝓝 (f : CarpetLp p)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδt (fun _ ↦ norm_nonneg _)
      (fun n ↦ (hdist n).trans ?_)
    have hn := E.norm_coe_le_graphSeminorm (d n - f)
    change ‖(d n : CarpetLp p) - (f : CarpetLp p)‖ ≤ _ at hn
    exact hn.trans (hD n).le
  obtain ⟨z, hz, htail⟩ := E.exists_mem_graphClosedConvexTails e (f : CarpetLp p) hbnd hlim
  have hzf : z = f := Subtype.ext hz
  let S : Set E.GraphDomain := {z | ∃ g : E.continuousCore,
    (∀ x, 0 ≤ g.val x) ∧ E.toGraph (E.continuousCoreToDomain g) = z}
  have hConv : Convex ℝ S := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb _
    refine ⟨a • v + b • w, fun x ↦ ?_, by simp only [map_add, map_smul]; rfl⟩
    change 0 ≤ a * v.val x + b * w.val x
    exact add_nonneg (mul_nonneg ha (hv x)) (mul_nonneg hb (hw x))
  have hsub : convexHull ℝ ((fun k ↦ E.toGraph (e k)) '' Ici 0) ⊆ S := by
    apply convexHull_min _ hConv
    rintro _ ⟨n, _, rfl⟩
    exact ⟨g n, fun x ↦ by rw [hv']; exact le_max_right _ _, rfl⟩
  have hfS : E.toGraph f ∈ closure S := by rw [← hzf]; exact closure_mono hsub (htail 0)
  have hfst (n : ℕ) : ∃ z ∈ S, dist z (E.toGraph f) < δ n := by
    obtain ⟨z, hzS, hz⟩ := Metric.mem_closure_iff.mp hfS _ (hδ n)
    exact ⟨z, hzS, by simpa only [dist_comm (E.toGraph f) z] using hz⟩
  choose z hzS hzdist using hfst
  have hzs (n : ℕ) : ∃ w : E.continuousCore, (∀ x, 0 ≤ w.val x) ∧
      E.toGraph (E.continuousCoreToDomain w) = z n := hzS n
  choose w hw hwz using hzs
  refine ⟨w, hw, Metric.tendsto_nhds.mpr (fun ε hε ↦ ?_)⟩
  filter_upwards [hδt.eventually_lt_const hε] with n hn
  rw [hwz]
  exact (hzdist n).trans hn

end CarpetEnergy.SelfSimilarPEnergy
