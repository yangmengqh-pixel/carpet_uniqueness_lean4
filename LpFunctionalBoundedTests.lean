import LpFunctionalSignedMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Radon–Nikodym representation on bounded tests

The indicator identity extends to simple functions by linearity,
then to bounded measurable functions by Lp convergence and
dominated convergence against the integrable density.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

omit [Fact (1 ≤ q)] [IsFiniteMeasure μ] in
private theorem integrable_mul_simple {f : X → ℝ} (hf : Integrable f μ) (u : SimpleFunc X ℝ) :
    Integrable (fun x ↦ f x * u x) μ := by
  obtain ⟨C, hC⟩ := u.exists_forall_norm_le
  exact hf.mul_bdd u.aestronglyMeasurable (Eventually.of_forall hC)

private theorem apply_LpFunctional_simple (L : Lp ℝ q μ →L[ℝ] ℝ) {f : X → ℝ}
    (hf : Integrable f μ)
    (h : ∀ A (hA : MeasurableSet A),
      L (indicatorConstLp q hA (measure_ne_top _ _) 1) = ∫ x in A, f x ∂μ)
    (u : SimpleFunc X ℝ) :
    L ((u.memLp_of_isFiniteMeasure q μ).toLp u) = ∫ x, f x * u x ∂μ := by
  induction u using SimpleFunc.induction with
  | const c hA =>
    rename_i A
    let v : SimpleFunc X ℝ := SimpleFunc.piecewise A hA (SimpleFunc.const X c) (SimpleFunc.const X 0)
    let U : Lp ℝ q μ := (v.memLp_of_isFiniteMeasure q μ).toLp v
    let I : Lp ℝ q μ := indicatorConstLp q hA (measure_ne_top _ _) (1 : ℝ)
    have hU : U = c • I := by
      apply Lp.ext
      filter_upwards [(v.memLp_of_isFiniteMeasure q μ).coeFn_toLp, Lp.coeFn_smul c I,
        indicatorConstLp_coeFn (p := q) (hs := hA) (hμs := measure_ne_top μ A) (c := (1 : ℝ))]
        with x hx hx' hI
      have hx₁ : U x = v x := hx
      have hx₂ : (c • I) x = c * I x := hx'
      have hI' : I x = A.indicator (fun _ ↦ (1 : ℝ)) x := hI
      rw [hx₁, hx₂, hI']
      by_cases hmem : x ∈ A <;> simp [v, SimpleFunc.piecewise, hmem]
    have he : (fun x ↦ f x * v x) = A.indicator (fun x ↦ c * f x) := by
      funext x
      by_cases hmem : x ∈ A <;> simp [v, SimpleFunc.piecewise, hmem, mul_comm]
    change L U = ∫ x, f x * v x ∂μ
    rw [hU, map_smul, smul_eq_mul, h A hA, he, integral_indicator hA, integral_const_mul]
  | @add u v _ hu hv =>
    have he : (fun x ↦ f x * (u + v) x) = fun x ↦ f x * u x + f x * v x := by
      funext x
      exact mul_add _ _ _
    rw [show ((u + v).memLp_of_isFiniteMeasure q μ).toLp (u + v) =
      (u.memLp_of_isFiniteMeasure q μ).toLp u + (v.memLp_of_isFiniteMeasure q μ).toLp v
      from MemLp.toLp_add _ _, map_add, hu, hv, he,
      integral_add (integrable_mul_simple hf u) (integrable_mul_simple hf v)]

/-- The integrable Radon–Nikodym density represents the Lp functional
on all bounded measurable functions. -/
theorem exists_density_LpFunctional_bounded_tests (hq : q ≠ ∞) (L : Lp ℝ q μ →L[ℝ] ℝ) :
    ∃ f : X → ℝ, Measurable f ∧ Integrable f μ ∧
      ∀ (g : X → ℝ) (hg : Measurable g) (B : ℝ) (_hB : 0 ≤ B) (hb : ∀ x, |g x| ≤ B),
        L ((MemLp.of_bound (p := q) hg.aestronglyMeasurable B
          (Eventually.of_forall fun x ↦ (Real.norm_eq_abs (g x)).symm ▸ hb x)).toLp g) =
          ∫ x, f x * g x ∂μ := by
  obtain ⟨f, hfm, hf, h⟩ := exists_integrable_density_LpFunctional hq L
  refine ⟨f, hfm, hf, fun g hg B hB hb ↦ ?_⟩
  have hgLp : MemLp g q μ := MemLp.of_bound hg.aestronglyMeasurable B
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hb x)
  let S := range g ∪ {0}
  have h0 : (0 : ℝ) ∈ S := by simp [S]
  let u (n : ℕ) : SimpleFunc X ℝ := SimpleFunc.approxOn g hg S 0 h0 n
  have hu (n : ℕ) (x : X) : ‖u n x‖ ≤ B := by
    have hm : u n x ∈ S := SimpleFunc.approxOn_mem hg h0 n x
    change u n x ∈ range g ∨ u n x ∈ ({0} : Set ℝ) at hm
    rcases hm with ⟨y, hy⟩ | hy
    · rw [← hy, Real.norm_eq_abs]
      exact hb y
    · rw [mem_singleton_iff.mp hy, norm_zero]
      exact hB
  have hLp : Tendsto (fun n ↦ ((u n).memLp_of_isFiniteMeasure q μ).toLp (u n)) atTop (𝓝 (hgLp.toLp g)) :=
    SimpleFunc.tendsto_approxOn_range_Lp hq hg hgLp
  have hInt : Tendsto (fun n ↦ ∫ x, f x * u n x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖ * B)
    · exact fun n ↦ hf.aestronglyMeasurable.mul (u n).aestronglyMeasurable
    · exact hf.norm.mul_const B
    · exact fun n ↦ Eventually.of_forall fun x ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hu n x) (norm_nonneg _)
    · exact Eventually.of_forall fun x ↦ tendsto_const_nhds.mul
        (SimpleFunc.tendsto_approxOn hg h0 (subset_closure (mem_union_left _ (mem_range_self x))))
  have hlim := (L.continuous.tendsto _).comp hLp
  have he (n : ℕ) : L (((u n).memLp_of_isFiniteMeasure q μ).toLp (u n)) = ∫ x, f x * u n x ∂μ :=
    apply_LpFunctional_simple L hf h (u n)
  exact tendsto_nhds_unique hlim (hInt.congr fun n ↦ (he n).symm)

end CarpetEnergy
