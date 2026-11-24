import CommonDensity
import EnergySeminorm

/-!
# A reference measure from an energy-dense sequence

The weighted sum of energy measures is finite and is minimal among the
measures dominating the energy measures of all domain functions.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The weights in Section 7, with the sequence indexed from zero. -/
noncomputable def energyReferenceWeight (d : ℕ → E.domain) (n : ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ * (1 + (E.energy (d n) : ℝ≥0∞))⁻¹

theorem energyReferenceWeight_ne_zero (d : ℕ → E.domain) (n : ℕ) :
    E.energyReferenceWeight d n ≠ 0 := by
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (by simp))
    (ENNReal.inv_ne_zero.mpr (by simp))

/-- The weighted reference measure used before Lemma 7.3. -/
noncomputable def energyReferenceMeasure (d : ℕ → E.domain) : Measure CarpetPoints :=
  Measure.sum (fun n ↦ E.energyReferenceWeight d n • E.energyMeasure (d n))

theorem energyReferenceMeasure_univ_le (d : ℕ → E.domain) :
    E.energyReferenceMeasure d univ ≤ 1 := by
  rw [energyReferenceMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [smul_apply, smul_eq_mul, E.energyMeasure_univ, energyReferenceWeight, mul_assoc]
  have hsum : (∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) = 1 := by
    simpa only [neg_sub_left, ENNReal.zpow_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add,
      zpow_natCast] using ENNReal.tsum_two_zpow_neg_add_one
  apply (le_of_eq hsum).trans' ?_
  apply tsum_le_tsum
  intro n
  refine mul_le_of_le_one_right' ?_
  calc
    (1 + (E.energy (d n) : ℝ≥0∞))⁻¹ * (E.energy (d n) : ℝ≥0∞) ≤
        (1 + (E.energy (d n) : ℝ≥0∞))⁻¹ * (1 + (E.energy (d n) : ℝ≥0∞)) := by gcongr; simp
    _ ≤ 1 := ENNReal.inv_mul_le_one _

instance (d : ℕ → E.domain) : IsFiniteMeasure (E.energyReferenceMeasure d) :=
  ⟨(E.energyReferenceMeasure_univ_le d).trans_lt ENNReal.one_lt_top⟩

/-- Energy approximation by the sequence implies domination of every energy measure. -/
theorem energyMeasure_absolutelyContinuous_reference (d : ℕ → E.domain)
    (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0))
    (f : E.domain) :
    E.energyMeasure f ≪ E.energyReferenceMeasure d := by
  apply absolutelyContinuous_weighted_sum_of_energy_approximation E.energyMeasure
    (fun _ ↦ inferInstance) d (E.energyReferenceWeight d) (E.energyReferenceWeight_ne_zero d)
    E.rootSeminorm (zero_lt_one.trans E.one_lt_p) _ hdense f
  intro A hA
  exact ⟨E.energyMeasureSeminorm A hA, fun g ↦
    ⟨E.energyMeasureSeminorm_apply A hA g, E.energyMeasureSeminorm_le_rootSeminorm A hA g⟩⟩

/-- Every measure dominating all the energy measures also dominates the weighted sum. -/
theorem energyReferenceMeasure_absolutelyContinuous (d : ℕ → E.domain)
    (ν : Measure CarpetPoints) (h : ∀ f : E.domain, E.energyMeasure f ≪ ν) :
    E.energyReferenceMeasure d ≪ ν :=
  Measure.absolutelyContinuous_sum_left fun n ↦
    Measure.smul_absolutelyContinuous.trans (h (d n))

private theorem withDensity_reference_rnDeriv (d : ℕ → E.domain)
    (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0))
    (f : E.domain) :
    (E.energyReferenceMeasure d).withDensity
        ((E.energyMeasure f).rnDeriv (E.energyReferenceMeasure d)) = E.energyMeasure f := by
  have : (E.energyMeasure f).HaveLebesgueDecomposition (E.energyReferenceMeasure d) :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  exact Measure.withDensity_rnDeriv_eq _ _
    (E.energyMeasure_absolutelyContinuous_reference d hdense f)

/-- For an energy-dense sequence, the weighted sum of the Radon–Nikodym derivatives is one. -/
theorem ae_reference_density_sum_eq_one (d : ℕ → E.domain)
    (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0)) :
    (fun x ↦ ∑' n, E.energyReferenceWeight d n *
      (E.energyMeasure (d n)).rnDeriv (E.energyReferenceMeasure d) x)
      =ᵐ[E.energyReferenceMeasure d] fun _ ↦ 1 := by
  let μ := E.energyReferenceMeasure d
  have : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (E.energyReferenceMeasure d))
  let r (f : E.domain) := (E.energyMeasure f).rnDeriv μ
  have hr (f : E.domain) : Measurable (r f) := Measure.measurable_rnDeriv _ _
  have hd (f : E.domain) : μ.withDensity (r f) = E.energyMeasure f :=
    E.withDensity_reference_rnDeriv d hdense f
  have hμ : μ = Measure.sum (fun n ↦ E.energyReferenceWeight d n • μ.withDensity (r (d n))) := by
    change Measure.sum (fun n ↦ E.energyReferenceWeight d n • E.energyMeasure (d n)) = _
    exact congrArg Measure.sum
      (funext fun n ↦ congrArg (fun ν : Measure CarpetPoints ↦ E.energyReferenceWeight d n • ν)
        (hd (d n)).symm)
  exact ae_tsum_density_eq_one (μ := μ) (r := r) d (E.energyReferenceWeight d) hr hμ

end CarpetEnergy.SelfSimilarPEnergy
