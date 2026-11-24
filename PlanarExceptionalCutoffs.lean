import PlanarQuadraticDensity
import PlanarDensityCutoffs
import PlanarWeightedCutoffTransfer
import PlanarWeightedCutoffUnion

/-!
# Small weighted tests for the exceptional planar density sets
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 5300000 in
/-- The exceptional sets in Case 2 of Theorem 5.2 lie in a measurable
set admitting arbitrarily small smooth weighted cutoff approximations. -/
theorem exists_small_weighted_cutoff_set_covering_planar_exceptions
    {p : ℝ} (hp : 1 < p) (hp₂ : p < 2)
    (ν κ : Measure PlanarCoordinates) [IsFiniteMeasure ν] [IsFiniteMeasure κ]
    {S : Set PlanarCoordinates} (hS : IsCompact S) (hκS : ∀ᵐ x ∂κ, x ∈ S)
    {s : ℝ≥0∞} (hs : 0 < s) (hsfin : s ≠ ∞)
    {u : PlanarCoordinates → ℝ} (hu : Measurable u) (hu₀ : ∀ x, 0 ≤ u x)
    (hSob : MemPlanarSobolev p u)
    (hdom : s • κ ≤ volume.withDensity (fun y ↦ ENNReal.ofReal (u y ^ p))) :
    ∃ B : Set PlanarCoordinates, MeasurableSet B ∧
      UnboundedUpperBallDensity ν (2 - p) ∪ UnboundedUpperBallDensity κ 2 ⊆ B ∧
      HasSmallWeightedCutoffsInMeasure p ν κ B := by
  obtain ⟨a, ha, ha₀, haEq, haI, haLp, g, hg⟩ :=
    exists_integrable_planar_sobolev_localization hp hu hu₀ hSob hS
  have hdom' := root_weight_domination_of_ae_eq p hS.measurableSet hκS haEq hdom
  let v (i : Fin 2) := (hg i).1.aemeasurable.mk (g i)
  have hvm (i : Fin 2) : Measurable (v i) := (hg i).1.aemeasurable.measurable_mk
  have he (i : Fin 2) : g i =ᵐ[volume] v i := (hg i).1.aemeasurable.ae_eq_mk
  have hv (i : Fin 2) : Integrable (v i) volume := (hg i).1.congr (he i)
  have hVLp (i : Fin 2) : MemLp (v i) (ENNReal.ofReal p) volume := MemLp.ae_eq (he i) (hg i).2.1
  have hp₀ := zero_lt_one.trans hp
  have hvP (i : Fin 2) : Integrable (fun x ↦ |v i x| ^ p) volume := by
    simpa only [ENNReal.toReal_ofReal hp₀.le, Real.norm_eq_abs] using
      (hVLp i).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top
  have haP : Integrable (fun x ↦ a x ^ p) volume := by
    simpa only [ENNReal.toReal_ofReal hp₀.le, Real.norm_eq_abs, abs_of_nonneg (ha₀ _)] using
      haLp.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top
  have hD (i : Fin 2) : HasWeakDirectionalDerivative volume a (v i) (planarDirection i) := by
    intro φ hφ hφs
    have hh := (hg i).2.2 φ hφ hφs
    rw [integral_congr_ae ((he i).mono fun x hx ↦ congrArg (fun t ↦ t * φ x) hx)] at hh
    exact hh
  let γ := planarGradientMeasure p v
  let A := UnboundedPlanarMollification a
  let C := UnboundedUpperBallDensity γ (2 - p)
  let V := UnboundedUpperBallDensity ν (2 - p)
  let : IsFiniteMeasure γ := isFiniteMeasure_planarGradientMeasure hvP
  have hV : MeasurableSet V := measurableSet_unboundedUpperBallDensity ν (sub_nonneg.mpr hp₂.le)
  have hA : MeasurableSet A := measurableSet_unboundedPlanarMollification haI
  have hC : MeasurableSet C := measurableSet_unboundedUpperBallDensity γ (sub_nonneg.mpr hp₂.le)
  have hsub : UnboundedUpperBallDensity κ 2 ⊆ A ∪ C :=
    unbounded_quadraticDensity_subset_of_sobolev_dominator hp hs hsfin ha ha₀ haI haP v hvm hv hvP hD hdom'
  have htransfer {B : Set PlanarCoordinates} (hB : MeasurableSet B)
      (ht : HasSmallWeightedCutoffsOnCompacts p volume B) :
      HasSmallWeightedCutoffsInMeasure p ν κ B :=
    (hasSmallWeightedCutoffsOnCompacts_of_sobolev_dominator hp hS hκS hs hsfin hu hu₀ hSob hdom ht).in_measure hB
  have hcutA := htransfer hA
    (hasSmallUnweightedCutoffsOnCompacts_unboundedPlanarMollification hp ha ha₀ haI haP v hvm hv hvP hD)
  have hcutV := htransfer hV (hasSmallUnweightedCutoffsOnCompacts_unboundedUpperBallDensity hp ν)
  have hcutC := htransfer hC (hasSmallUnweightedCutoffsOnCompacts_unboundedUpperBallDensity hp γ)
  refine ⟨V ∪ (A ∪ C), hV.union (hA.union hC), union_subset_union Subset.rfl hsub, ?_⟩
  exact hcutV.union hp (hcutA.union hp hcutC)

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- Nonconcentration also holds for compact cutoff approximations in
the reference pushforward measure. -/
theorem map_carpetMeasure_compl_pos_of_small_weighted_cutoffs_in_measure
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (u : Fin 2 → E.continuousCore) (j : Fin 2)
    (hj : 0 < E.rootSeminorm (E.continuousCoreToDomain (u j)))
    {B : Set PlanarCoordinates}
    (hb : HasSmallWeightedCutoffsInMeasure p (carpetMeasure.map (E.continuousCoreTuple u))
      ((E.pairEnergyMeasure u).map (E.continuousCoreTuple u)) B) :
    0 < (carpetMeasure.map (E.continuousCoreTuple u)) Bᶜ := by
  let ν := carpetMeasure.map (E.continuousCoreTuple u)
  apply pos_iff_ne_zero.mpr
  intro hnull
  apply E.false_of_small_weighted_cutoff_approximation h hc u j hj
  intro ε hε
  obtain ⟨K, _, hK, hsmall, f, hf⟩ := hb ε hε
  refine ⟨K, hK, ?_, f, hf⟩
  have he : Kᶜ \ Bᶜ = B \ K := by
    ext x
    simp only [Set.mem_sdiff, mem_compl_iff, not_not, and_comm]
  rw [← he, measure_sdiff_null hnull] at hsmall
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall
  rwa [ENNReal.toReal_ofReal hε.le] at hh

end SelfSimilarPEnergy

end CarpetEnergy
