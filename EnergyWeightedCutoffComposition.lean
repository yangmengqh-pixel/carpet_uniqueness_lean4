import EnergySmoothCompositionBound
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# A weighted cutoff multiplied by a coordinate profile

The smooth composition bound controls the energy of a cutoff times
a coordinate. Only the cutoff and its two partial derivatives need
small Lp norms for the pushed-forward energy measure.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

noncomputable def pairEnergyMeasure (u : Fin 2 → E.continuousCore) : Measure CarpetPoints :=
  E.energyMeasure (E.continuousCoreToDomain (u 0)) + E.energyMeasure (E.continuousCoreToDomain (u 1))

instance (u : Fin 2 → E.continuousCore) : IsFiniteMeasure (E.pairEnergyMeasure u) :=
  inferInstanceAs (IsFiniteMeasure (_ + _))

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem energyMeasure_le_pairEnergyMeasure (u : Fin 2 → E.continuousCore) (i : Fin 2) :
    E.energyMeasure (E.continuousCoreToDomain (u i)) ≤ E.pairEnergyMeasure u := by
  fin_cases i <;> unfold pairEnergyMeasure
  · exact Measure.le_add_right le_rfl
  · exact Measure.le_add_left le_rfl

private theorem abs_add_rpow_le {a b p : ℝ} (hp : 1 ≤ p) :
    |a + b| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  refine (Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (zero_le_one.trans hp)).trans ?_
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    ⟨|a|, abs_nonneg _⟩ ⟨|b|, abs_nonneg _⟩ hp

set_option maxHeartbeats 2900000 in
theorem exists_core_coordinate_mul_cutoff
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (u : Fin 2 → E.continuousCore) (j : Fin 2) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x, |(u j).val x| ≤ M) (f : (Fin 2 → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    {b : ℝ}
    (hbudget : let κ := (E.pairEnergyMeasure u).map (E.continuousCoreTuple u)
      (∫ x, |f x| ^ p ∂κ) ≤ b ∧
        ∀ i : Fin 2, (∫ x, |fderiv ℝ f x (Pi.single i 1)| ^ p ∂κ) ≤ b) :
    ∃ v : E.continuousCore,
      (∀ x, v.val x = (u j).val x * f (E.continuousCoreTuple u x)) ∧
      E.rootSeminorm (E.continuousCoreToDomain v) ≤
        2 * ((2 : ℝ) ^ (p - 1) * (1 + M ^ p) * b) ^ p⁻¹ := by
  let H := E.continuousCoreTuple u
  let φ (x : Fin 2 → ℝ) := x j * f x
  let Λ := E.pairEnergyMeasure u
  let κ := Λ.map H
  let Q := (2 : ℝ) ^ (p - 1)
  have hQ : 0 ≤ Q := Real.rpow_nonneg (by norm_num) _
  let P : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hφ : ContDiff ℝ 1 φ := P.contDiff.mul hf
  obtain ⟨v, hv⟩ := E.exists_core_comp_contDiff hc u φ hφ
  refine ⟨v, hv, ?_⟩
  have hp := zero_lt_one.trans E.one_lt_p
  have hproj (i : Fin 2) : |P (Pi.single i (1 : ℝ))| ≤ 1 := by
    let ei : Fin 2 → ℝ := Pi.single i 1
    change |ei j| ≤ 1
    dsimp only [ei]
    by_cases hij : j = i
    · subst j
      simp
    · rw [Pi.single_eq_of_ne hij, abs_zero]
      exact zero_le_one
  have hcoord (i : Fin 2) (y : Fin 2 → ℝ) :
      fderiv ℝ φ y (Pi.single i 1) =
        y j * fderiv ℝ f y (Pi.single i 1) + f y * P (Pi.single i 1) := by
    have he := P.hasFDerivAt.mul (hf.differentiable (by norm_num) y).hasFDerivAt
    change HasFDerivAt φ _ y at he
    rw [he.fderiv]
    rfl
  have hpt (i : Fin 2) (x : CarpetPoints) :
      |fderiv ℝ φ (H x) (Pi.single i 1)| ^ p ≤ Q *
        (|f (H x)| ^ p + M ^ p * |fderiv ℝ f (H x) (Pi.single i 1)| ^ p) := by
    rw [hcoord, add_comm]
    apply (abs_add_rpow_le E.one_lt_p.le).trans
    simp only [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    have hl : |P (Pi.single i 1)| ^ p ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (abs_nonneg _) (hproj i) hp.le
    have hr : |H x j| ^ p ≤ M ^ p := Real.rpow_le_rpow (abs_nonneg _) (hm x) hp.le
    have hl' := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg (abs_nonneg (f (H x))) p)
    rw [mul_one] at hl'
    exact mul_le_mul_of_nonneg_left (add_le_add hl' (mul_le_mul_of_nonneg_right hr
      (Real.rpow_nonneg (abs_nonneg (fderiv ℝ f (H x) (Pi.single i 1))) p))) hQ
  have hcoeff (i : Fin 2) :
      (∫ x, |fderiv ℝ φ (H x) (Pi.single i 1)| ^ p
        ∂E.energyMeasure (E.continuousCoreToDomain (u i))) ≤ Q * (1 + M ^ p) * b := by
    let D (x : Fin 2 → ℝ) := |fderiv ℝ f x (Pi.single i 1)| ^ p
    let L (x : Fin 2 → ℝ) := |f x| ^ p
    have hdc : Continuous D :=
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).abs.rpow_const
        (fun _ ↦ Or.inr hp.le)
    have hlc : Continuous L := hf.continuous.abs.rpow_const (fun _ ↦ Or.inr hp.le)
    have hI : Integrable (fun x ↦ |fderiv ℝ φ (H x) (Pi.single i 1)| ^ p) Λ :=
      (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp H.continuous).abs.rpow_const
        (fun _ ↦ Or.inr hp.le) |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hD : Integrable (D ∘ H) Λ := (hdc.comp H.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hL : Integrable (L ∘ H) Λ := (hlc.comp H.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have h₁ := integral_mono_measure (E.energyMeasure_le_pairEnergyMeasure u i)
      (Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg
        (fderiv ℝ φ (H x) (Pi.single i 1))) p) hI
    have h₂ := integral_mono hI ((hL.add (hD.const_mul (M ^ p))).const_mul Q) (hpt i)
    change (∫ x, |fderiv ℝ φ (H x) (Pi.single i 1)| ^ p ∂Λ) ≤
      ∫ x, Q * ((L ∘ H) x + M ^ p * (D ∘ H) x) ∂Λ at h₂
    have hLmap : (∫ x, L x ∂κ) = ∫ x, (L ∘ H) x ∂Λ :=
      integral_map H.continuous.measurable.aemeasurable hlc.aestronglyMeasurable
    have hDmap : (∫ x, D x ∂κ) = ∫ x, (D ∘ H) x ∂Λ :=
      integral_map H.continuous.measurable.aemeasurable hdc.aestronglyMeasurable
    rw [integral_const_mul, integral_add hL (hD.const_mul (M ^ p)), integral_const_mul,
      ← hLmap, ← hDmap] at h₂
    have h₃ := mul_le_mul_of_nonneg_left (add_le_add hbudget.1
      (mul_le_mul_of_nonneg_left (hbudget.2 i) (Real.rpow_nonneg hM p))) hQ
    exact (h₁.trans (h₂.trans h₃)).trans_eq (by ring)
  apply (E.rootSeminorm_smooth_comp_le h hc u φ hφ v hv).trans
  calc
    _ ≤ ∑ _i : Fin 2, (Q * (1 + M ^ p) * b) ^ p⁻¹ := Finset.sum_le_sum fun i _ ↦
      Real.rpow_le_rpow (integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)) (hcoeff i)
        (inv_nonneg.mpr hp.le)
    _ = _ := by rw [Fin.sum_univ_two, two_mul]

end CarpetEnergy.SelfSimilarPEnergy
