import WeakDirectionalTranslation

/-!
# A translation bound in terms of the two weak coordinate derivatives
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

theorem planarDirection_decomposition_eq (z : Plane2) :
    z = z 0 • planarDirection 0 + z 1 • planarDirection 1 := by
  ext i
  fin_cases i <;> simp [planarDirection, Pi.add_apply, Pi.smul_apply]

private theorem abs_add_rpow_le {p a b : ℝ} (hp : 1 ≤ p) :
    |a + b| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  apply (Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (zero_le_one.trans hp)).trans
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨|a|, abs_nonneg _⟩ : ℝ≥0) (⟨|b|, abs_nonneg _⟩ : ℝ≥0) hp

set_option maxHeartbeats 3200000 in
theorem integral_abs_planar_translation_sub_rpow_le {p : ℝ} (hp : 1 ≤ p)
    {u : Plane2 → ℝ} (hu : Integrable u volume) (v : Fin 2 → Plane2 → ℝ)
    (hv : ∀ i, Integrable (v i) volume) (hvp : ∀ i, Integrable (fun x ↦ |v i x| ^ p) volume)
    (h : ∀ i, HasWeakDirectionalDerivative volume u (v i) (planarDirection i)) (z : Plane2) :
    Integrable (fun x ↦ |u (x + z) - u x| ^ p) volume ∧
      (∫ x, |u (x + z) - u x| ^ p ∂volume) ≤
        (2 : ℝ) ^ (p - 1) * ‖z‖ ^ p *
          ((∫ x, |v 0 x| ^ p ∂volume) + ∫ x, |v 1 x| ^ p ∂volume) := by
  let w (x : Plane2) := z 0 * v 0 x + z 1 * v 1 x
  have hw : Integrable w volume := ((hv 0).const_mul _).add ((hv 1).const_mul _)
  have hD : HasWeakDirectionalDerivative volume u w z := by
    intro φ hφ hs
    let F (i : Fin 2) (x : Plane2) := u x * fderiv ℝ φ x (planarDirection i)
    have hI (i : Fin 2) : Integrable (F i) volume := by
      have hC : Continuous (fun x ↦ fderiv ℝ φ x (planarDirection i)) :=
        (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hL := hC.memLp_of_hasCompactSupport (μ := (volume : Measure Plane2)) (p := ∞) (hs.fderiv_apply ℝ (planarDirection i))
      exact (memLp_one_iff_integrable.mpr hu).integrable_mul hL
    have hW (i : Fin 2) : Integrable (fun x ↦ v i x * φ x) volume :=
      (memLp_one_iff_integrable.mpr (hv i)).integrable_mul (hφ.continuous.memLp_of_hasCompactSupport (μ := (volume : Measure Plane2)) (p := ∞) hs)
    have hleft : (∫ x, u x * fderiv ℝ φ x z ∂volume) =
        z 0 * (∫ x, F 0 x ∂volume) + z 1 * (∫ x, F 1 x ∂volume) := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hI 0).const_mul _) ((hI 1).const_mul _)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by
        conv_lhs => rw [planarDirection_decomposition_eq z]
        simp only [map_add, map_smul, smul_eq_mul, F]
        ring
    have hright : (∫ x, w x * φ x ∂volume) =
        z 0 * (∫ x, v 0 x * φ x ∂volume) + z 1 * (∫ x, v 1 x * φ x ∂volume) := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hW 0).const_mul _) ((hW 1).const_mul _)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by dsimp only [w]; ring
    rw [hleft, hright]
    simp only [show (∫ x, F 0 x ∂volume) = -(∫ x, v 0 x * φ x ∂volume) from h 0 φ hφ hs,
      show (∫ x, F 1 x ∂volume) = -(∫ x, v 1 x * φ x ∂volume) from h 1 φ hφ hs]
    ring
  let C := (2 : ℝ) ^ (p - 1) * ‖z‖ ^ p
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hdom (x : Plane2) : |w x| ^ p ≤ C * (|v 0 x| ^ p + |v 1 x| ^ p) := by
    apply (abs_add_rpow_le hp).trans
    have hcoord (i : Fin 2) : |z i * v i x| ^ p ≤ ‖z‖ ^ p * |v i x| ^ p := by
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg _) _)
      exact Real.rpow_le_rpow (abs_nonneg _)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i) (zero_le_one.trans hp)
    dsimp only [C]
    rw [mul_assoc, mul_add (‖z‖ ^ p)]
    exact mul_le_mul_of_nonneg_left (add_le_add (hcoord 0) (hcoord 1)) (by positivity)
  have hI : Integrable (fun x ↦ C * (|v 0 x| ^ p + |v 1 x| ^ p)) volume :=
    ((hvp 0).add (hvp 1)).const_mul C
  have hwI : Integrable (fun x ↦ |w x| ^ p) volume := by
    apply hI.mono' ((Real.continuous_rpow_const (zero_le_one.trans hp)).comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable hw.aestronglyMeasurable))
    exact Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact hdom x
  obtain ⟨hT, hB⟩ := hD.integral_abs_translation_sub_rpow_le hp hu hw hwI
  refine ⟨hT, hB.trans ?_⟩
  have hE := integral_mono hwI hI hdom
  rwa [integral_const_mul, integral_add (hvp 0) (hvp 1)] at hE

end CarpetEnergy
