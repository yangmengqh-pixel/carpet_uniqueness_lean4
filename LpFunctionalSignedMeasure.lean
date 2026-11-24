import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# The signed measure induced by an Lp functional

Evaluating a continuous linear functional on indicators gives a
countably additive signed measure. Continuity in Lp handles increasing
finite unions, and the Radon–Nikodym theorem gives an integrable density.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

private noncomputable def indicatorLp (μ : Measure X) [IsFiniteMeasure μ] (q : ℝ≥0∞)
    (A : Set X) (hA : MeasurableSet A) : Lp ℝ q μ :=
  indicatorConstLp q hA (measure_ne_top _ _) (1 : ℝ)

omit [Fact (1 ≤ q)] in
private theorem sum_indicatorLp_finset {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) (s : Finset ℕ) :
    (∑ n ∈ s, indicatorLp μ q (A n) (hA n)) =
      indicatorLp μ q (⋃ n ∈ s, A n) (MeasurableSet.biUnion s.countable_toSet fun n _ ↦ hA n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [indicatorLp]
  | insert n s hn ih =>
    rw [Finset.sum_insert hn, ih]
    have hd' : Disjoint (A n) (⋃ k ∈ s, A k) := by
      refine Set.disjoint_iUnion_right.mpr fun k ↦ Set.disjoint_iUnion_right.mpr fun hk ↦ ?_
      exact hd (fun h ↦ hn (h ▸ hk))
    unfold indicatorLp
    exact (indicatorConstLp_disjoint_union (hA n)
      (MeasurableSet.biUnion s.countable_toSet fun k _ ↦ hA k)
      (measure_ne_top _ _) (measure_ne_top _ _) hd' (1 : ℝ)).symm.trans (by
        simp only [Finset.set_biUnion_insert])

private theorem tendsto_indicatorLp_union (hq : q ≠ ∞) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n)) :
    Tendsto (fun s : Finset ℕ ↦ indicatorLp μ q (⋃ n ∈ s, A n)
      (MeasurableSet.biUnion s.countable_toSet fun n _ ↦ hA n)) atTop
      (𝓝 (indicatorLp μ q (⋃ n, A n) (MeasurableSet.iUnion hA))) := by
  let U := ⋃ n, A n
  let V (s : Finset ℕ) := ⋃ n ∈ s, A n
  let W (s : Finset ℕ) := U \ V s
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  have hV (s : Finset ℕ) : MeasurableSet (V s) :=
    MeasurableSet.biUnion s.countable_toSet fun n _ ↦ hA n
  have hsub (s : Finset ℕ) : V s ⊆ U := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, (mem_iUnion.mp hn).choose_spec⟩
  have hmono : Antitone W := by
    intro s t hst x hx
    refine ⟨hx.1, fun hh ↦ hx.2 ?_⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hh
    obtain ⟨hn', hxn⟩ := mem_iUnion.mp hn
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hst hn', hxn⟩⟩
  have hinter : (⋂ s, W s) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := mem_iInter.mp hx ∅
    obtain ⟨n, hn⟩ := mem_iUnion.mp h.1
    exact (mem_iInter.mp hx {n}).2 (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_singleton_self _, hn⟩⟩)
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun s ↦ (hU.diff (hV s)).nullMeasurableSet) hmono ⟨∅, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  apply tendsto_indicatorConstLp_set hq
  change Tendsto (fun s ↦ μ (symmDiff (V s) U)) atTop (𝓝 0)
  have heq (s : Finset ℕ) : symmDiff (V s) U = W s := by
    rw [Set.symmDiff_def, sdiff_eq_empty.mpr (hsub s), empty_union]
  simpa only [heq, Function.comp_def] using hlim

/-- The signed measure obtained by evaluating an Lp functional on
indicators of measurable sets. -/
noncomputable def signedMeasureOfLpFunctional (hq : q ≠ ∞) (L : Lp ℝ q μ →L[ℝ] ℝ) :
    SignedMeasure X := by
  classical
  refine
    { measureOf' := fun A ↦ if hA : MeasurableSet A then L (indicatorLp μ q A hA) else 0
      empty' := by simp [indicatorLp]
      not_measurable' := fun _ h ↦ dite_eq_right h
      m_iUnion' := ?_ }
  intro A hA hd
  simp only [hA, dite_eq_left, MeasurableSet.iUnion hA]
  change Tendsto (fun s : Finset ℕ ↦ ∑ n ∈ s, L (indicatorLp μ q (A n) (hA n))) atTop
    (𝓝 (L (indicatorLp μ q (⋃ n, A n) (MeasurableSet.iUnion hA))))
  simp only [← map_sum, sum_indicatorLp_finset hA hd]
  exact (L.continuous.tendsto _).comp (tendsto_indicatorLp_union hq hA)

theorem signedMeasureOfLpFunctional_apply (hq : q ≠ ∞) (L : Lp ℝ q μ →L[ℝ] ℝ)
    {A : Set X} (hA : MeasurableSet A) :
    signedMeasureOfLpFunctional hq L A = L (indicatorConstLp q hA (measure_ne_top _ _) 1) := by
  classical
  change (if h : MeasurableSet A then L (indicatorLp μ q A h) else 0) = _
  rw [dite_eq_left hA]
  rfl

theorem signedMeasureOfLpFunctional_absolutelyContinuous (hq : q ≠ ∞) (L : Lp ℝ q μ →L[ℝ] ℝ) :
    signedMeasureOfLpFunctional hq L ≪ᵥ μ.toENNRealVectorMeasure := by
  intro A hzero
  by_cases hA : MeasurableSet A
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hzero
    rw [signedMeasureOfLpFunctional_apply hq L hA]
    have hp : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le (Fact.out : 1 ≤ q))) hq
    have hI : (indicatorConstLp (μ := μ) q hA (measure_ne_top _ _) (1 : ℝ)) = 0 := by
      apply norm_eq_zero.mp
      rw [norm_indicatorConstLp (ne_of_gt (one_pos.trans_le (Fact.out : 1 ≤ q))) hq,
        measureReal_def, hzero, ENNReal.toReal_zero, Real.zero_rpow (one_div_ne_zero hp.ne'), mul_zero]
    rw [hI, map_zero]
  · exact VectorMeasure.not_measurable _ hA

theorem exists_integrable_density_LpFunctional (hq : q ≠ ∞) (L : Lp ℝ q μ →L[ℝ] ℝ) :
    ∃ f : X → ℝ, Measurable f ∧ Integrable f μ ∧
      ∀ A (hA : MeasurableSet A), L (indicatorConstLp q hA (measure_ne_top _ _) 1) = ∫ x in A, f x ∂μ := by
  let s := signedMeasureOfLpFunctional hq L
  let f := s.rnDeriv μ
  have hf : Integrable f μ := s.integrable_rnDeriv μ
  have he : μ.withDensityᵥ f = s :=
    (SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq s μ).mp
      (signedMeasureOfLpFunctional_absolutelyContinuous hq L)
  refine ⟨f, s.measurable_rnDeriv μ, hf, fun A hA ↦ ?_⟩
  rw [← signedMeasureOfLpFunctional_apply hq L hA, show signedMeasureOfLpFunctional hq L = s from rfl,
    ← he, withDensityᵥ_apply hf hA]

end CarpetEnergy
