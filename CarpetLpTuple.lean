import CarpetDiscreteEnergy
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Pointwise vector operations on carpet Lp functions

A finite tuple of scalar Lp classes assembles linearly into a class
with values in a finite product. Lipschitz component maps act on it
pointwise. When the inputs are cell lifts, the output cell averages
are precisely the same component maps applied to the input averages.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy

variable {I O : Type*}

private noncomputable def coordinateLinear (i : I) : ℝ →L[ℝ] (I → ℝ) := by
  classical
  exact ContinuousLinearMap.pi fun j ↦ if j = i then ContinuousLinearMap.id ℝ ℝ else 0

private theorem coordinateLinear_apply (i j : I) (a : ℝ) :
    coordinateLinear i a j = (by classical exact if j = i then a else 0) := by
  classical
  by_cases hij : j = i <;> simp [coordinateLinear, hij]

variable [Fintype I]

/-- Assemble finitely many scalar Lp classes as one vector-valued class. -/
noncomputable def lpTuple (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    (I → CarpetLp p) →L[ℝ] Lp (I → ℝ) (ENNReal.ofReal p) carpetMeasure :=
  ∑ i, ((coordinateLinear i).compLpL (ENNReal.ofReal p) carpetMeasure).comp
    (ContinuousLinearMap.proj i)

theorem ae_lpTuple {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (u : I → CarpetLp p) :
    (lpTuple p u : CarpetPoints → I → ℝ) =ᵐ[carpetMeasure] fun x i ↦ u i x := by
  classical
  let v (i : I) := (coordinateLinear i).compLpL (ENNReal.ofReal p) carpetMeasure (u i)
  have hu : lpTuple p u = ∑ i, v i := by
    simp only [lpTuple, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, v]
  rw [hu]
  have hv : ∀ᵐ x ∂carpetMeasure, ∀ i, (v i) x = coordinateLinear i (u i x) :=
    ae_all_iff.mpr fun i ↦ (coordinateLinear i).coeFn_compLpL (u i)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ v, hv] with x hx hx'
  rw [hx, Finset.sum_apply]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · rw [hx' j, coordinateLinear_apply, ite_eq_left rfl]
  · intro i _ hi
    rw [hx' i, coordinateLinear_apply, ite_eq_right hi.symm]
  · simp

/-- Apply each Lipschitz component of a vector operation to an Lp tuple. -/
noncomputable def pointwiseLp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (T : (I → ℝ) → O → ℝ)
    {L : O → ℝ≥0} (hT : ∀ i, LipschitzWith (L i) fun v ↦ T v i)
    (h0 : ∀ i, T 0 i = 0) (u : I → CarpetLp p) (i : O) : CarpetLp p :=
  (hT i).compLp (h0 i) (lpTuple p u)

theorem continuous_pointwiseLp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (T : (I → ℝ) → O → ℝ) {L : O → ℝ≥0}
    (hT : ∀ i, LipschitzWith (L i) fun v ↦ T v i) (h0 : ∀ i, T 0 i = 0) :
    Continuous (pointwiseLp (p := p) T hT h0) := by
  apply continuous_pi
  intro i
  exact ((hT i).continuous_compLp (h0 i)).comp (lpTuple p).continuous

theorem ae_pointwiseLp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (T : (I → ℝ) → O → ℝ) {L : O → ℝ≥0}
    (hT : ∀ i, LipschitzWith (L i) fun v ↦ T v i) (h0 : ∀ i, T 0 i = 0)
    (u : I → CarpetLp p) (i : O) :
    (pointwiseLp T hT h0 u i : CarpetPoints → ℝ) =ᵐ[carpetMeasure]
      fun x ↦ T (fun j ↦ u j x) i := by
  exact ((hT i).coeFn_compLp (h0 i) (lpTuple p u)).trans
    ((ae_lpTuple u).mono fun _ hx ↦ congrArg (fun w ↦ T w i) hx)

theorem ambientWordMean_pointwiseLp_cellAveraging {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (T : (I → ℝ) → O → ℝ) {L : O → ℝ≥0}
    (hT : ∀ i, LipschitzWith (L i) fun v ↦ T v i) (h0 : ∀ i, T 0 i = 0)
    (n : ℕ) (u : I → CarpetLp p) (w : Fin n → Fin 8) (i : O) :
    ambientWordMean p (List.ofFn w) (pointwiseLp T hT h0 (fun j ↦ cellAveraging p n (u j)) i) =
      T (fun j ↦ ambientWordMean p (List.ofFn w) (u j)) i := by
  apply ambientWordMean_eq_of_ae_eq_on_openWordCell w
  have hu : ∀ᵐ x ∂carpetMeasure.restrict (openWordCell w), ∀ j,
      cellAveraging p n (u j) x = ambientWordMean p (List.ofFn w) (u j) :=
    ae_all_iff.mpr fun j ↦ cellAveraging_ae_eq_on_openWordCell n (u j) w
  filter_upwards [ae_restrict_of_ae (ae_pointwiseLp (p := p) T hT h0 (fun j ↦ cellAveraging p n (u j)) i), hu] with x hx hx'
  exact hx.trans (congrArg (fun z ↦ T z i) (funext hx'))

end CarpetEnergy
