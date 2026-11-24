import PEnergy
import UniformConvexApproximation
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.LinearAlgebra.Countable
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Bounded approximation in the graph norm

The graph norm gives a uniformly convex Banach space that embeds continuously
into the ambient Lp space. A graph-bounded sequence with an Lp limit has an
energy-domain limit in the closed convex hull of every tail.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace CarpetEnergy

theorem norm_carpetLp_le_of_ae_bound {p : ℝ} (f : CarpetLp p) {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ᵐ x ∂carpetMeasure, ‖f x‖ ≤ R) : ‖f‖ ≤ R := by
  have hm : measureUnivNNReal carpetMeasure = 1 := by
    apply ENNReal.coe_injective
    rw [coe_measureUnivNNReal, measure_univ, ENNReal.coe_one]
  simpa only [hm, NNReal.coe_one, Real.one_rpow, one_mul] using
    Lp.norm_le_of_ae_bound hR hf

end CarpetEnergy

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The energy domain equipped with the graph norm. -/
def GraphDomain : Type := E.domain

/-- A graph-domain element considered as a member of the original submodule. -/
def graphToDomain (f : E.GraphDomain) : E.domain := f

/-- A function in the submodule considered as an element of the graph-normed space. -/
def toGraph (f : E.domain) : E.GraphDomain := f

noncomputable instance : NormedAddCommGroup E.GraphDomain :=
  let N : AddGroupNorm E.domain :=
    { E.graphSeminorm.toAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun f hf ↦ (E.graphSeminorm_eq_zero_iff f).mp hf }
  N.toNormedAddCommGroup

noncomputable instance : Module ℝ E.GraphDomain :=
  show Module ℝ E.domain from inferInstance

noncomputable instance : NormedSpace ℝ E.GraphDomain :=
  { (inferInstance : Module ℝ E.GraphDomain) with
    norm_smul_le := fun a f ↦ (map_smul_eq_mul E.graphSeminorm a (E.graphToDomain f)).le }

instance : UniformConvexSpace E.GraphDomain := E.graph_uniformConvex

instance : CompleteSpace E.GraphDomain := E.graph_complete

theorem norm_toGraph (f : E.domain) : ‖E.toGraph f‖ = E.graphSeminorm f := rfl

theorem norm_coe_le_graphSeminorm (f : E.domain) : ‖(f : CarpetLp p)‖ ≤ E.graphSeminorm f := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hf : 0 ≤ ‖(f : CarpetLp p)‖ := norm_nonneg _
  rw [E.graphSeminorm_apply, energyGraphNorm]
  calc
    ‖(f : CarpetLp p)‖ = (‖(f : CarpetLp p)‖ ^ p) ^ p⁻¹ :=
      (Real.rpow_rpow_inv hf hp.ne').symm
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hf _)
      (le_add_of_nonneg_left (E.energy f).property) (inv_nonneg.mpr hp.le)

theorem rootSeminorm_le_graphSeminorm (f : E.domain) : E.rootSeminorm f ≤ E.graphSeminorm f := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  rw [E.rootSeminorm_apply, E.graphSeminorm_apply, energyGraphNorm]
  exact Real.rpow_le_rpow (E.energy f).property
    (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt_p).le)

/-- Bounds for the ambient norm and the energy root give a graph-norm bound. -/
theorem graphSeminorm_le_of_le (f : E.domain) {L R : ℝ}
    (hL : ‖(f : CarpetLp p)‖ ≤ L) (hR : E.rootSeminorm f ≤ R) :
    E.graphSeminorm f ≤ (R ^ p + L ^ p) ^ p⁻¹ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have henergy : (E.energy f : ℝ) ≤ R ^ p := by
    calc
      (E.energy f : ℝ) = ((E.energy f : ℝ) ^ p⁻¹) ^ p :=
        (Real.rpow_inv_rpow (E.energy f).property hp.ne').symm
      _ = (E.rootSeminorm f) ^ p := congrArg (fun t : ℝ ↦ t ^ p) (E.rootSeminorm_apply f).symm
      _ ≤ R ^ p := Real.rpow_le_rpow (apply_nonneg E.rootSeminorm f) hR hp.le
  rw [E.graphSeminorm_apply, energyGraphNorm]
  exact Real.rpow_le_rpow
    (add_nonneg (E.energy f).property (Real.rpow_nonneg (norm_nonneg _) _))
    (add_le_add henergy (Real.rpow_le_rpow (norm_nonneg _) hL hp.le))
    (inv_nonneg.mpr hp.le)

/-- The continuous linear inclusion from the graph-normed domain into the ambient Lp space. -/
noncomputable def graphInclusion [Fact (1 ≤ ENNReal.ofReal p)] :
    E.GraphDomain →L[ℝ] CarpetLp p :=
  (show E.GraphDomain →ₗ[ℝ] CarpetLp p from E.domain.subtype).mkContinuous 1
    fun z ↦ by
      rw [one_mul]
      exact E.norm_coe_le_graphSeminorm (E.graphToDomain z)

/-- Bounded graph approximants with an ambient limit yield an energy-domain function
in every closed convex tail, with the closure taken in the graph norm. -/
theorem exists_mem_graphClosedConvexTails (u : ℕ → E.domain) (f : CarpetLp p) {R : ℝ}
    (hb : ∀ n, E.graphSeminorm (u n) ≤ R) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
    Tendsto (fun n ↦ (u n : CarpetLp p)) atTop (𝓝 f) →
      ∃ v : E.domain, (v : CarpetLp p) = f ∧
        ∀ n, E.toGraph v ∈ closure (convexHull ℝ ((fun k ↦ E.toGraph (u k)) '' Ici n)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  intro hf
  obtain ⟨v, hv, htail⟩ := exists_mem_closed_convex_tails_of_bounded_tendsto E.graphInclusion
    (u := fun n ↦ E.toGraph (u n)) hb hf
  exact ⟨E.graphToDomain v, hv, htail⟩

/-- Bounds for seminorms controlled by the graph norm pass to ambient limits of
graph-bounded sequences. -/
theorem exists_domain_of_tendsto_of_seminorm_le (S : Seminorm ℝ E.domain)
    (hS : S ≤ E.graphSeminorm) (u : ℕ → E.domain) (f : CarpetLp p) {B R : ℝ}
    (hB : ∀ n, E.graphSeminorm (u n) ≤ B)
    (hR : ∀ r > R, ∀ᶠ n in atTop, S (u n) ≤ r) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
    Tendsto (fun n ↦ (u n : CarpetLp p)) atTop (𝓝 f) →
      ∃ v : E.domain, (v : CarpetLp p) = f ∧ S v ≤ R := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  intro hf
  obtain ⟨v, hv, htail⟩ := E.exists_mem_graphClosedConvexTails u f hB hf
  let toDomain : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let q := S.comp toDomain
  have hq : Continuous q :=
    Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm
      (fun z ↦ hS (E.graphToDomain z))
  refine ⟨v, hv, ?_⟩
  by_contra! hRv
  obtain ⟨r, hr, hrv⟩ := exists_between hRv
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hR r hr)
  have hsub : closure (convexHull ℝ ((fun k ↦ E.toGraph (u k)) '' Ici N)) ⊆
      q.closedBall 0 r := by
    apply closure_minimal _ (by rw [q.closedBall_zero_eq]; exact isClosed_le hq continuous_const)
    apply convexHull_min _ (q.convex_closedBall 0 r)
    rintro _ ⟨n, hn, rfl⟩
    rw [q.closedBall_zero_eq]
    exact hN n hn
  have hm := hsub (htail N)
  rw [q.closedBall_zero_eq] at hm
  exact hrv.not_ge hm

/-- The continuous finite-energy core contains a countable energy-dense sequence. -/
theorem exists_energyDense_continuous_sequence :
    ∃ d : ℕ → E.domain,
      (∀ n, ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (d n : CarpetLp p)) ∧
      ∀ f : E.domain, ∃ j : ℕ → ℕ,
        Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have : Fact (ENNReal.ofReal p ≠ ⊤) := ⟨ENNReal.ofReal_ne_top⟩
  have : TopologicalSpace.SeparableSpace E.GraphDomain :=
    separableSpace_of_injective_continuousLinearMap E.graphInclusion Subtype.val_injective
  let S : Set E.GraphDomain :=
    {f | ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (E.graphToDomain f : CarpetLp p)}
  have hS : Dense S := by
    intro f
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨u, hu, hdist⟩ := E.regular_graph (E.graphToDomain f) ε hε
    refine ⟨E.toGraph ⟨continuousLp p u, hu⟩, ⟨u, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact hdist
  obtain ⟨s, hsS, hcount, hsdense⟩ := hS.exists_countable_dense_subset
  obtain ⟨d, hd⟩ := hcount.exists_eq_range hsdense.nonempty
  have hdense : DenseRange d := by
    rw [hd] at hsdense
    exact hsdense
  refine ⟨fun n ↦ E.graphToDomain (d n), ?_, ?_⟩
  · intro n
    exact hsS (hd.symm ▸ mem_range_self n)
  · intro f
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense (E.toGraph f))
    choose j hj using hv
    have hn : Tendsto (fun n ↦ ‖v n - E.toGraph f‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlim
    refine ⟨j, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hn
      (fun n ↦ apply_nonneg _ _) fun n ↦ ?_⟩
    rw [← hj n, norm_sub_rev]
    exact E.rootSeminorm_le_graphSeminorm _

/-- The continuous finite-energy functions contain a countable rational subspace
which is dense in the energy seminorm. -/
theorem exists_energyDense_continuous_ratSubmodule :
    ∃ D : Submodule ℚ E.domain, ∃ d : ℕ → D, Function.Surjective d ∧
      (∀ f : D, ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (f : CarpetLp p)) ∧
      ∀ f : E.domain, ∃ j : ℕ → ℕ,
        Tendsto (fun n ↦ E.rootSeminorm (f - (d (j n) : E.domain))) atTop (𝓝 0) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨a, hac, had⟩ := E.exists_energyDense_continuous_sequence
  let T := (ContinuousMap.toLp (E := ℝ) (ENNReal.ofReal p) carpetMeasure ℝ).toLinearMap
  have hT (u : C(CarpetPoints, ℝ)) : T u = continuousLp p u := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp carpetMeasure u).trans (continuousLp_ae_eq p u).symm
  let D := Submodule.span ℚ (range a)
  have hD : D ≤ ((LinearMap.range T).comap E.domain.subtype).restrictScalars ℚ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    obtain ⟨u, hu⟩ := hac n
    exact ⟨u, (hT u).trans hu⟩
  have hcont (f : D) : ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (f : CarpetLp p) := by
    obtain ⟨u, hu⟩ := hD f.property
    exact ⟨u, (hT u).symm.trans hu⟩
  have : Countable D := inferInstanceAs (Countable (Submodule.span ℚ (range a)))
  obtain ⟨d, hd⟩ := (countable_univ : (univ : Set D).Countable).exists_eq_range
    (Set.univ_nonempty : (univ : Set D).Nonempty)
  have hd' : Function.Surjective d := range_eq_univ.mp hd.symm
  have hmem (n : ℕ) : a n ∈ D := Submodule.subset_span (mem_range_self n)
  choose k hk using fun n : ℕ ↦ hd' (⟨a n, hmem n⟩ : D)
  refine ⟨D, d, hd', hcont, fun f ↦ ?_⟩
  obtain ⟨j, hj⟩ := had f
  refine ⟨k ∘ j, ?_⟩
  simpa only [Function.comp_apply, hk] using hj

end CarpetEnergy.SelfSimilarPEnergy
