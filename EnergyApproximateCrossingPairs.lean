import EnergyApproximateLevelCrossing
import EnergyHarmonicMajorants
import EnergyInteriorHarmonicExterior

/-!
# Distance-spanning upper and lower level sets of approximating profiles
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem distance_image_contains_Icc_of_connected_crossing
    {x : CarpetPoints} {R : ℝ} (hR : 0 < R) {S : Set CarpetPoints}
    (hS : IsConnected S) (h₀ : (S ∩ ball x (R / 2)).Nonempty)
    (h₁ : (S \ ball x R).Nonempty) :
    Icc (R / 2) (3 * R / 4) ⊆ (fun y ↦ dist y x) '' (S ∩ ball x R) := by
  obtain ⟨y, hyS, hy⟩ := h₀
  obtain ⟨z, hzS, hz⟩ := h₁
  have hcont : Continuous (fun y : CarpetPoints ↦ dist y x) := continuous_id.dist continuous_const
  have hI := (hS.isPreconnected.image _ hcont.continuousOn).ordConnected
  intro r hr
  have hyr : dist y x ≤ r := (mem_ball.mp hy).le.trans hr.1
  have hzr : r ≤ dist z x := hr.2.trans ((show 3 * R / 4 ≤ R by linarith).trans
    (not_lt.mp (mt mem_ball.mpr hz)))
  obtain ⟨w, hw, hwr⟩ := hI.out ⟨y, hyS, rfl⟩ ⟨z, hzS, rfl⟩ (show r ∈ Icc _ _ from ⟨hyr, hzr⟩)
  refine ⟨w, ⟨hw, mem_ball.mpr ?_⟩, hwr⟩
  change dist w x = r at hwr
  rw [hwr]
  exact hr.2.trans_lt (by linarith)

set_option maxHeartbeats 2700000 in
/-- If both level sets have positive excess for a minimizing profile,
its graph approximants eventually have two distance-spanning level sets. -/
theorem eventually_exists_distance_spanning_level_sets
    {x : CarpetPoints} {R : ℝ} (hR : 0 < R) (hout : carpetMeasure (ball x R)ᶜ ≠ 0)
    (f : E.domain) (hf : E.MinimizesWithExterior (ball x R)ᶜ f)
    (u : ℕ → E.continuousCore)
    (hu : Tendsto (fun n ↦ E.toGraph (E.continuousCoreToDomain (u n))) atTop (𝓝 (E.toGraph f)))
    (a b : ℝ)
    (hlow : 0 < ∫ y in ball x (R / 2), max (a - (f : CarpetLp p) y) 0 ∂carpetMeasure)
    (hhigh : 0 < ∫ y in ball x (R / 2), max ((f : CarpetLp p) y - b) 0 ∂carpetMeasure) :
    ∀ᶠ n in atTop, ∃ S T : Set CarpetPoints, S ⊆ ball x R ∧ T ⊆ ball x R ∧
      Icc (R / 2) (3 * R / 4) ⊆ (fun y ↦ dist y x) '' S ∧
      Icc (R / 2) (3 * R / 4) ⊆ (fun y ↦ dist y x) '' T ∧
      (∀ y ∈ S, b ≤ (u n).val y) ∧ (∀ y ∈ T, (u n).val y ≤ a) := by
  let W := ball x (R / 2)
  have hupper := E.eventually_exists_connected_superlevel_crossing isOpen_ball.measurableSet
    (show MeasurableSet W from isOpen_ball.measurableSet) hout f hf u b hu hhigh
  have hneglim : Tendsto (fun n ↦ E.toGraph (E.continuousCoreToDomain (-u n))) atTop
      (𝓝 (E.toGraph (-f))) := by
    simp only [map_neg]
    exact hu.neg
  have hnegint : 0 < ∫ y in W, max (((-f : E.domain) : CarpetLp p) y - (-a)) 0 ∂carpetMeasure := by
    refine hlow.trans_eq (integral_congr_ae ?_)
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_neg (f : CarpetLp p))] with y hy
    change _ = max ((-(f : CarpetLp p)) y - (-a)) 0
    rw [hy, Pi.neg_apply]
    congr 1
    ring
  have hlower := E.eventually_exists_connected_superlevel_crossing isOpen_ball.measurableSet
    (show MeasurableSet W from isOpen_ball.measurableSet) hout (-f) (MinimizesWithExterior.neg E hf)
    (fun n ↦ -u n) (-a) hneglim hnegint
  filter_upwards [hupper, hlower] with n hpos hneg
  obtain ⟨S, hS, hSg, hW, houtS⟩ := hpos
  obtain ⟨T, hT, hTf, hW', houtT⟩ := hneg
  refine ⟨S ∩ ball x R, T ∩ ball x R, inter_subset_right, inter_subset_right,
    distance_image_contains_Icc_of_connected_crossing hR hS hW houtS,
    distance_image_contains_Icc_of_connected_crossing hR hT hW' houtT, ?_, ?_⟩
  · intro y hy
    exact (show b < (u n).val y from hSg hy.1).le
  · intro y hy
    have hh : -a < -((u n).val y) := hTf hy.1
    linarith

end CarpetEnergy.SelfSimilarPEnergy
