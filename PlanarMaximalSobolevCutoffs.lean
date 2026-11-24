import PlanarMaximalSobolevProfiles
import PlanarSmallSmoothThreshold
import EnergyWeightedCapacityNonconcentration

/-!
# Unweighted cutoffs for unbounded Sobolev mollifications
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

/-- The set where a nonnegative profile's normalized mollifications
are arbitrarily large. -/
def UnboundedPlanarMollification (u : PlanarCoordinates → ℝ) : Set PlanarCoordinates :=
  {x | ∀ C : ℝ, ∃ n : ℕ, C < mollify volume n u x}

theorem measurableSet_unboundedPlanarMollification {u : PlanarCoordinates → ℝ}
    (hu : Integrable u volume) :
    MeasurableSet (UnboundedPlanarMollification u) := by
  have he : UnboundedPlanarMollification u =
      ⋂ m : ℕ, ⋃ n : ℕ, {x | (m : ℝ) < mollify volume n u x} := by
    ext x
    simp only [UnboundedPlanarMollification, mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · exact fun h m ↦ h m
    · intro h C
      obtain ⟨m, hm⟩ := exists_nat_ge C
      obtain ⟨n, hn⟩ := h m
      exact ⟨n, hm.trans_lt hn⟩
  rw [he]
  exact MeasurableSet.iInter (fun _ ↦ MeasurableSet.iUnion (fun n ↦
    (isOpen_lt continuous_const (contDiff_mollify volume (n := n) hu).continuous).measurableSet))

set_option maxHeartbeats 2900000 in
/-- A finite smooth maximum and its uniform moment bound give a small
capacity test on any compact subset of the unbounded set. -/
theorem hasSmallUnweightedCutoffsOnCompacts_unboundedPlanarMollification {p : ℝ}
    (hp : 1 < p) {u : PlanarCoordinates → ℝ} (hu : Measurable u) (hu₀ : ∀ x, 0 ≤ u x)
    (huI : Integrable u volume) (huP : Integrable (fun x ↦ u x ^ p) volume)
    (v : Fin 2 → PlanarCoordinates → ℝ)
    (hv : ∀ i, Measurable (v i)) (hvI : ∀ i, Integrable (v i) volume)
    (hvP : ∀ i, Integrable (fun x ↦ |v i x| ^ p) volume)
    (hD : ∀ i, HasWeakDirectionalDerivative volume u (v i) (planarDirection i)) :
    HasSmallWeightedCutoffsOnCompacts p volume (UnboundedPlanarMollification u) := by
  classical
  intro K hKB hK ε hε
  obtain ⟨C, hC, H⟩ := exists_uniform_planar_smooth_maximal_profiles hp hu hu₀ huI huP v hv hvI hvP hD
  obtain ⟨t, _, hcut⟩ := exists_small_smooth_threshold_cutoff hp hK hC hε
  let O (n : ℕ) := {x | t + 1 < mollify volume n u x}
  have hO (n : ℕ) : IsOpen (O n) :=
    isOpen_lt continuous_const (contDiff_mollify volume (n := n) huI).continuous
  have hcov : K ⊆ ⋃ n, O n := fun _ hx ↦ mem_iUnion.mpr (hKB hx (t + 1))
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover O hO hcov
  obtain ⟨f, hf, hf₀, hf₁, hfI, hfC, hfD⟩ := H (insert 0 S) ⟨0, Finset.mem_insert_self _ _⟩
  obtain ⟨g, hg, hgs, hg01, hgK, hgE, hgD⟩ := hcut f hf hf₀ hfI hfC hfD
  refine ⟨g, hg, hgs, hg01, ?_, hgE, hgD⟩
  intro x hx
  apply hgK x hx
  obtain ⟨n, hn, hx'⟩ := mem_iUnion₂.mp (hS hx)
  have hh := hf₁ n (Finset.mem_insert_of_mem hn) x
  change t + 1 < mollify volume n u x at hx'
  linarith

end CarpetEnergy
