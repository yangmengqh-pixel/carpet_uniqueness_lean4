import EnergyHarmonicOscillationCascade

/-!
# A continuous local version of a harmonic profile

Nested essential intervals define the version. Fine neighborhoods at
a nearby point eventually lie in the same coarser neighborhood, so
their limiting values differ by at most its essential oscillation.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3800000 in
/-- Proposition 4.9 with a fixed stride between consecutive scales,
conditional on the neighborhood Harnack inequality. -/
theorem exists_continuous_harmonic_neighborhood_version {H : ℝ} (hH : 1 ≤ H)
    (hHar : E.HasNeighborhoodHarnack H)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ))) :
    ∃ L : ℕ, 0 < L ∧ ∃ C > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8),
      Disjoint (wordCellUnion (cellNeighborhood w 3)) carpetOuterBoundary →
      ∀ f : E.domain, E.IsInteriorHarmonic f →
        let W := wordCellUnion (cellNeighborhood w 2)
        let R := C * ((E.scalingFactor ^ n)⁻¹ * E.cellUnionEnergy (cellNeighborhood w 3) f) ^ p⁻¹
        ∃ u : C(W, ℝ),
          (∀ᵐ x ∂carpetMeasure.restrict W, ∀ hx : x ∈ W, u ⟨x, hx⟩ = (f : CarpetLp p) x) ∧
          (∀ x : W, |u x - E.wordMean (List.ofFn w) f| ≤ R) ∧
          ∀ (k : ℕ) (x y : W), dist x y < (1 / 3 : ℝ) ^ harmonicOscillationLevel n L k / 2 →
            |u x - u y| ≤ harnackOscillationFactor H ^ k * (2 * R) := by
  obtain ⟨L, hL, C, hC, hdata⟩ := E.exists_harmonic_essential_interval_cascade hH hHar hG
  refine ⟨L, hL, C, hC, fun n w hw f hf ↦ ?_⟩
  let W := wordCellUnion (cellNeighborhood w 2)
  let R := C * ((E.scalingFactor ^ n)⁻¹ * E.cellUnionEnergy (cellNeighborhood w 3) f) ^ p⁻¹
  let m := E.wordMean (List.ofFn w) f
  let μ (x : CarpetPoints) (k : ℕ) := carpetMeasure.restrict (harmonicOscillationNeighborhood n L x k)
  let a (x : CarpetPoints) (k : ℕ) := essInf (f : CarpetLp p) (μ x k)
  let b (x : CarpetPoints) (k : ℕ) := essSup (f : CarpetLp p) (μ x k)
  have hA (x : W) :
      (∀ k, ∀ᵐ y ∂μ x k, (f : CarpetLp p) y ∈ Icc (a x k) (b x k)) ∧
      (∀ k, m - R ≤ a x k ∧ b x k ≤ m + R) ∧
      (∀ k, b x k - a x k ≤ harnackOscillationFactor H ^ k * (2 * R)) ∧
      ∃! z : ℝ, ∀ k, z ∈ Icc (a x k) (b x k) := hdata n w hw f hf x x.property
  choose v hv using fun x : W ↦ (hA x).2.2.2.exists
  have hμ₀ (x : CarpetPoints) (k : ℕ) : μ x k ≠ 0 := by
    intro h
    have he := congrArg (fun ν : Measure CarpetPoints ↦ ν univ) h
    change (carpetMeasure.restrict (harmonicOscillationNeighborhood n L x k)) univ = 0 at he
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at he
    exact carpetMeasure_wordCellUnion_cellNeighborhood_ne_zero _ he
  have hlevels : Tendsto (harmonicOscillationLevel n L) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    have hmul : 1 * k ≤ L * k := Nat.mul_le_mul_right k hL
    rw [one_mul] at hmul
    dsimp only [harmonicOscillationLevel]
    omega
  have hrad :
      Tendsto (fun k ↦ 3 * ((1 / 3 : ℝ) ^ harmonicOscillationLevel n L k *
        Metric.diam (univ : Set CarpetPoints))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using (tendsto_wordMap_radius.const_mul (3 : ℝ)).comp hlevels
  have hmod (k : ℕ) (x y : W)
      (hxy : dist x y < (1 / 3 : ℝ) ^ harmonicOscillationLevel n L k / 2) :
      |v x - v y| ≤ harnackOscillationFactor H ^ k * (2 * R) := by
    let r := (1 / 3 : ℝ) ^ harmonicOscillationLevel n L k
    have hr : 0 < r := by dsimp only [r]; positivity
    obtain ⟨j, hj⟩ := (hrad.eventually_lt_const (half_pos hr)).exists
    have hsub : harmonicOscillationNeighborhood n L y j ⊆ harmonicOscillationNeighborhood n L x k := by
      intro z hz
      apply ball_subset_centerWord_neighborhood (harmonicOscillationLevel n L k) (x : CarpetPoints)
      have hz' := dist_centerWord_neighborhood (harmonicOscillationLevel n L j) 2 (y : CarpetPoints) hz
      norm_num at hz'
      have he : dist (y : CarpetPoints) (x : CarpetPoints) < r / 2 := by
        change dist (x : CarpetPoints) (y : CarpetPoints) < r / 2 at hxy
        rwa [dist_comm]
      change dist z (x : CarpetPoints) < r
      exact (dist_triangle _ (y : CarpetPoints) _).trans_lt (by linarith only [hz', hj, he])
    have hbounded := ((hA x).1 k).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    let : NeZero (μ y j) := ⟨hμ₀ y j⟩
    have hinterval := ae_interval_between_essBounds hbounded
    have hxv := hv x k
    have hyv := hv y j
    have hy₁ := hinterval.2.1.trans hyv.1
    have hy₂ := hyv.2.trans hinterval.2.2.1
    refine (abs_le.mpr ⟨?_, ?_⟩).trans ((hA x).2.2.1 k)
    · linarith only [hxv.1, hy₂]
    · linarith only [hxv.2, hy₁]
  have hcont : Continuous v := by
    apply Metric.continuous_iff.mpr
    intro x ε hε
    have hlim : Tendsto (fun k ↦ harnackOscillationFactor H ^ k * (2 * R)) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (harnackOscillationFactor_nonneg H) (harnackOscillationFactor_lt_one hH)).mul_const (2 * R)
    obtain ⟨k, hk⟩ := (hlim.eventually_lt_const hε).exists
    refine ⟨(1 / 3 : ℝ) ^ harmonicOscillationLevel n L k / 2, by positivity, fun y hy ↦ ?_⟩
    rw [Real.dist_eq]
    exact (hmod k y x hy).trans_lt hk
  let u : C(W, ℝ) := ⟨v, hcont⟩
  refine ⟨u, ?_, ?_, hmod⟩
  · have hCell (k : ℕ) (t : Fin (harmonicOscillationLevel n L k) → Fin 8) :
        let A := wordCellUnion (cellNeighborhood t 2)
        let ν := carpetMeasure.restrict A
        ∀ᵐ z ∂carpetMeasure, (∃ x : W, centerWord (harmonicOscillationLevel n L k) x = t) →
          z ∈ A → (f : CarpetLp p) z ∈ Icc (essInf (f : CarpetLp p) ν) (essSup (f : CarpetLp p) ν) := by
      by_cases ht : ∃ x : W, centerWord (harmonicOscillationLevel n L k) x = t
      · obtain ⟨x, rfl⟩ := ht
        have hloc := (ae_restrict_iff' (measurableSet_wordCellUnion _)).mp ((hA x).1 k)
        exact hloc.mono fun _ hz _ ↦ hz
      · exact Eventually.of_forall fun _ h ↦ (ht h).elim
    have hAll := ae_all_iff.mpr fun k : ℕ ↦ ae_all_iff.mpr (hCell k)
    filter_upwards [hAll.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hxW
    let z : W := ⟨x, hxW⟩
    have hfmem (k : ℕ) : (f : CarpetLp p) x ∈ Icc (a z k) (b z k) :=
      hx k (centerWord (harmonicOscillationLevel n L k) z) ⟨z, rfl⟩
        (mem_wordCellUnion_centerWord (harmonicOscillationLevel n L k) 2 z)
    exact (hA z).2.2.2.unique (hv z) hfmem
  · intro x
    have hx := hv x 0
    have hb := (hA x).2.1 0
    change |v x - m| ≤ R
    exact abs_le.mpr ⟨by linarith only [hx.1, hb.1], by linarith only [hx.2, hb.2]⟩

end CarpetEnergy.SelfSimilarPEnergy
