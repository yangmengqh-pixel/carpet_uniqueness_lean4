import PlanarTranslationAveraging
import MollifierDerivativeBudget
import MollifierDerivativeConvolution

/-!
# A weighted derivative bound for mollified reciprocal cutoffs
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

set_option maxHeartbeats 4400000 in
/-- A weighted increment bound transfers the small derivative budget
of a Sobolev tail to the mollified reciprocal cutoff. -/
theorem lintegral_weighted_mollify_fderiv_rpow_le
    {p : ℝ} (hp : 1 < p) {a b T : Plane2 → ℝ}
    (ha₀ : ∀ x, 0 ≤ a x)
    (hb : Integrable b volume) (hTm : Measurable T) (hT : Integrable T volume)
    (hinc : ∀ x y, (a x + 1) * |b y - b x| ≤ |T y - T x|)
    (v : Fin 2 → Plane2 → ℝ) (hv : ∀ i, Integrable (v i) volume)
    (hvp : ∀ i, Integrable (fun x ↦ |v i x| ^ p) volume)
    (hD : ∀ i, HasWeakDirectionalDerivative volume T (v i) (planarDirection i))
    (n : ℕ) (e : Plane2) :
    (∫⁻ x, ENNReal.ofReal (((a x + 1) * |fderiv ℝ (mollify volume n b) x e|) ^ p) ∂volume) ≤
      ENNReal.ofReal (∫ y, |fderiv ℝ ((mollifierBump 0).normed volume) y e| ∂volume) ^ p *
      ENNReal.ofReal ((2 : ℝ) ^ (p - 1) * ((∫ x, |v 0 x| ^ p ∂volume) + ∫ x, |v 1 x| ^ p ∂volume)) := by
  let B := mollifierBump (X := Plane2) n
  let K := B.normed volume
  let D (y : Plane2) := fderiv ℝ K y e
  let r := B.rOut
  let ν := (volume : Measure Plane2).withDensity (fun y ↦ ENNReal.ofReal |D y|)
  have hK : ContDiff ℝ 1 K := B.contDiff_normed
  have hDs : HasCompactSupport D := B.hasCompactSupport_normed.fderiv_apply ℝ e
  have hDc : Continuous D := (hK.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDI : Integrable D volume := hDc.integrable_of_hasCompactSupport hDs
  have hDm : Measurable (fun y ↦ ENNReal.ofReal |D y|) := hDc.abs.measurable.ennreal_ofReal
  have hνmass : ν univ = ENNReal.ofReal (∫ y, |D y| ∂volume) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ofReal_integral_eq_lintegral_ofReal hDI.abs (Eventually.of_forall fun _ ↦ abs_nonneg _)]
  let : IsFiniteMeasure ν := ⟨hνmass ▸ ENNReal.ofReal_lt_top⟩
  have hνr : ∀ᵐ y ∂ν, ‖y‖ ≤ r := by
    rw [ae_withDensity_iff hDm]
    refine Eventually.of_forall (fun y hy ↦ ?_)
    by_contra! hh
    have hyout : y ∉ tsupport K := by
      rw [B.tsupport_normed_eq (μ := volume), mem_closedBall, dist_zero_right]
      exact hh.not_ge
    apply hy
    change ENNReal.ofReal |fderiv ℝ K y e| = 0
    rw [fderiv_of_notMem_tsupport ℝ hyout, zero_apply, abs_zero, ENNReal.ofReal_zero]
  have hbudget : ν univ * ENNReal.ofReal r =
      ENNReal.ofReal (∫ y, |fderiv ℝ ((mollifierBump 0).normed volume) y e| ∂volume) := by
    rw [hνmass, mul_comm, ← ENNReal.ofReal_mul B.rOut_pos.le]
    exact congrArg ENNReal.ofReal (mul_integral_abs_fderiv_mollifier_eq volume n e)
  obtain ⟨C, hC⟩ := hDs.exists_bound_of_continuous hDc
  have hDb (x : Plane2) : ‖D x‖ ≤ C := hC x
  have hDbabs (x : Plane2) : ‖|D x|‖ ≤ C := by simpa only [Real.norm_eq_abs, abs_abs] using hDb x
  have hzero : (∫ y, D y ∂volume) = 0 := integral_fderiv_mollifier_eq_zero volume n e
  have hshift {f : Plane2 → ℝ} (hf : Integrable f volume) (x : Plane2) :
      Integrable (fun y ↦ f (x - y)) volume := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using (hf.comp_add_left x).comp_neg
  have hpt (x : Plane2) :
      ENNReal.ofReal ((a x + 1) * |fderiv ℝ (mollify volume n b) x e|) ≤
        ∫⁻ y, ENNReal.ofReal |T (x - y) - T x| ∂ν := by
    have hi : Integrable (fun y ↦ D y * b (x - y)) volume :=
      (hshift hb x).bdd_mul hDc.aestronglyMeasurable (Eventually.of_forall hDb)
    have hi' : Integrable (fun y ↦ D y * (b (x - y) - b x)) volume := by
      have hEq : (fun y ↦ D y * (b (x - y) - b x)) =
          (fun y ↦ D y * b (x - y)) - (fun y ↦ D y * b x) := by
        funext y
        exact mul_sub _ _ _
      rw [hEq]
      exact hi.sub (hDI.mul_const (b x))
    have hder : fderiv ℝ (mollify volume n b) x e = ∫ y, D y * (b (x - y) - b x) ∂volume := by
      rw [fderiv_mollify_apply_eq_integral_mollifier_fderiv hb, integral_congr_ae (f := fun y ↦ D y * (b (x - y) - b x))
        (g := fun y ↦ D y * b (x - y) - D y * b x) (Eventually.of_forall fun _ ↦ mul_sub _ _ _),
        integral_sub hi (hDI.mul_const (b x)), integral_mul_const, hzero, zero_mul, sub_zero]
    have hj : Integrable (fun y ↦ |D y| * |T (x - y) - T x|) volume := by
      have hj₀ := (hshift hT x).abs.bdd_mul hDc.abs.aestronglyMeasurable (Eventually.of_forall hDbabs)
      have hj₁ := hDI.abs.mul_const |T x|
      apply (hj₀.add hj₁).mono'
        (hDc.abs.aestronglyMeasurable.mul
          (continuous_abs.comp_aestronglyMeasurable ((hshift hT x).aestronglyMeasurable.sub aestronglyMeasurable_const)))
      refine Eventually.of_forall fun y ↦ ?_
      change ‖|D y| * |T (x - y) - T x|‖ ≤ |D y| * |T (x - y)| + |D y| * |T x|
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)), ← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
    have hle : (a x + 1) * |fderiv ℝ (mollify volume n b) x e| ≤
        ∫ y, |D y| * |T (x - y) - T x| ∂volume := by
      rw [hder]
      refine (mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by linarith [ha₀ x])).trans ?_
      rw [← integral_const_mul]
      apply integral_mono (hi'.abs.const_mul _) hj
      intro y
      change (a x + 1) * |D y * (b (x - y) - b x)| ≤ |D y| * |T (x - y) - T x|
      rw [abs_mul, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hinc x (x - y)) (abs_nonneg _)
    refine (ENNReal.ofReal_le_ofReal hle).trans_eq ?_
    have hm : Measurable (fun y : Plane2 ↦ ENNReal.ofReal |T (x - y) - T x|) :=
      (continuous_abs.measurable.comp ((hTm.comp
        (measurable_const.sub measurable_id : Measurable (fun y : Plane2 ↦ x - y))).sub
          (measurable_const : Measurable (fun _ : Plane2 ↦ T x)))).ennreal_ofReal
    dsimp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul _ hDm hm,
      ofReal_integral_eq_lintegral_ofReal hj
        (Eventually.of_forall fun _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    simp only [ENNReal.ofReal_mul (abs_nonneg _), Pi.mul_apply]
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal |T (x - y) - T x| ∂ν) ^ p ∂volume := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (((a x + 1) * |fderiv ℝ (mollify volume n b) x e|) ^ p) ≤ _
      rw [← ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by linarith [ha₀ x]) (abs_nonneg _))
        (zero_le_one.trans hp.le)]
      exact ENNReal.rpow_le_rpow (hpt x) (zero_le_one.trans hp.le)
    _ ≤ _ := by
      rw [← hbudget]
      exact lintegral_planar_translation_average_rpow_le hp hTm hT v hv hvp hD ν B.rOut_pos.le hνr

end CarpetEnergy
