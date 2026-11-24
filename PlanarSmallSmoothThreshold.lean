import SmoothScaledBallCutoff
import SmoothCutoffFamily
import PlanarLowerDensity

/-!
# Small Sobolev cutoffs for large values of bounded-moment profiles
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace CarpetEnergy

private theorem abs_add_rpow_le {p a b : ℝ} (hp : 1 ≤ p) :
    |a + b| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  apply (Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (zero_le_one.trans hp)).trans
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨|a|, abs_nonneg _⟩ : ℝ≥0) (⟨|b|, abs_nonneg _⟩ : ℝ≥0) hp

private theorem integrable_abs_rpow_of_continuous_of_compactSupport {F : PlanarCoordinates → ℝ}
    (hF : Continuous F) (hFs : HasCompactSupport F) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x ↦ |F x| ^ p) volume := by
  apply (hF.abs.rpow_const (fun _ ↦ Or.inr hp.le)).integrable_of_hasCompactSupport
  apply hFs.mono'
  intro x hx
  by_contra hx'
  have hzero : F x = 0 := notMem_support.mp (fun h ↦ hx' (subset_tsupport _ h))
  exact hx (by
    change |F x| ^ p = 0
    rw [hzero, abs_zero, Real.zero_rpow hp.ne'])

set_option maxHeartbeats 5400000 in
/-- Uniform moment bounds make smooth cutoffs of high superlevels
arbitrarily small on a fixed compact region. -/
theorem exists_small_smooth_threshold_cutoff {p : ℝ} (hp : 1 < p)
    {K : Set PlanarCoordinates} (hK : IsCompact K) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ t > (0 : ℝ), ∀ f : PlanarCoordinates → ℝ, ContDiff ℝ 1 f → (∀ x, 0 ≤ f x) →
      Integrable (fun x ↦ f x ^ p) volume → (∫ x, f x ^ p ∂volume) ≤ C →
      (∀ i : Fin 2, Integrable (fun x ↦ |fderiv ℝ f x (Pi.single i 1)| ^ p) volume ∧
        (∫ x, |fderiv ℝ f x (Pi.single i 1)| ^ p ∂volume) ≤ C) →
      ∃ g : PlanarCoordinates → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
        (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ K, t ≤ f x → g x = 1) ∧
        (∫ x, |g x| ^ p ∂volume) ≤ ε ∧
        ∀ i : Fin 2, (∫ x, |fderiv ℝ g x (Pi.single i 1)| ^ p ∂volume) ≤ ε := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : PlanarCoordinates)
  obtain ⟨L, hL, hcut⟩ := exists_planar_ball_cutoffs
  obtain ⟨χ, hχ, hχ01, hχ1, hχ0, hχD⟩ := hcut 0 R hR
  have hχs : HasCompactSupport χ := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (3 * R))
    (fun x hx ↦ by by_contra hx'; exact hx ((hχ0 x (fun h ↦ hx' (ball_subset_closedBall h))).1))
  obtain ⟨A, hA, hAθ⟩ := exists_deriv_bound_smoothTransition
  have hθc : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hθ (x : ℝ) (hx : 0 ≤ x) : Real.smoothTransition x ≤ A * x := by
    let An : ℝ≥0 := ⟨A, hA.le⟩
    have hLip : LipschitzWith An Real.smoothTransition :=
      lipschitzWith_of_nnNorm_deriv_le (hθc.differentiable (by norm_num)) (fun t ↦ by
        change ‖deriv Real.smoothTransition t‖ ≤ A
        rw [Real.norm_eq_abs]
        exact hAθ t)
    have hh := hLip.dist_le_mul x 0
    change dist (Real.smoothTransition x) (Real.smoothTransition 0) ≤ A * dist x 0 at hh
    rwa [Real.smoothTransition.zero, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
      abs_of_nonneg (Real.smoothTransition.nonneg _), abs_of_nonneg hx] at hh
  let Q := L / R
  let B := A ^ p * C + (2 : ℝ) ^ (p - 1) * A ^ p * (Q ^ p * C + C) + 1
  have hQ : 0 ≤ Q := div_nonneg hL.le hR.le
  have hB : 0 < B := by dsimp only [B]; positivity
  let δ := min 1 (ε / B)
  have hδ : 0 < δ := lt_min one_pos (div_pos hε hB)
  have hδp : δ ^ p ≤ δ := by
    have h := Real.rpow_le_rpow_of_exponent_ge' hδ.le (min_le_left _ _) zero_le_one hp.le
    rwa [Real.rpow_one] at h
  have hδε : δ * B ≤ ε := (le_div_iff₀ hB).mp (min_le_right _ _)
  refine ⟨δ⁻¹, inv_pos.mpr hδ, fun f hf hf₀ hfI hfC hfD ↦ ?_⟩
  let w (x : PlanarCoordinates) := Real.smoothTransition (δ * f x)
  let g := χ * w
  have hw : ContDiff ℝ 1 w := hθc.comp (contDiff_const.mul hf)
  have hg : ContDiff ℝ 1 g := hχ.mul hw
  have hgs : HasCompactSupport g := hχs.mul_right
  have hwp (x : PlanarCoordinates) : w x ≤ (A * δ) * f x := by
    have hh := hθ (δ * f x) (mul_nonneg hδ.le (hf₀ x))
    simpa only [w, mul_assoc] using hh
  have hwD (x e : PlanarCoordinates) :
      |fderiv ℝ w x e| ≤ (A * δ) * |fderiv ℝ f x e| := by
    have hd := ((hθc.differentiable (by norm_num) (δ * f x)).hasDerivAt).comp_hasFDerivAt x
      ((hf.differentiable (by norm_num) x).hasFDerivAt.const_mul δ)
    change HasFDerivAt w _ x at hd
    rw [hd.fderiv, smul_smul, smul_apply, smul_eq_mul, abs_mul, abs_mul, abs_of_pos hδ]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hAθ _) hδ.le) (abs_nonneg _)
  have h01 (x : PlanarCoordinates) : g x ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hχ01 x).1 (Real.smoothTransition.nonneg _),
      (mul_le_of_le_one_right (hχ01 x).1 (Real.smoothTransition.le_one _)).trans (hχ01 x).2⟩
  have hAδ : 0 ≤ A * δ := mul_nonneg hA.le hδ.le
  have hp₀ := zero_lt_one.trans hp
  have hbudget : (A * δ) ^ p ≤ A ^ p * δ := by
    rw [Real.mul_rpow hA.le hδ.le]
    exact mul_le_mul_of_nonneg_left hδp (Real.rpow_nonneg hA.le _)
  refine ⟨g, hg, hgs, h01, ?_, ?_, ?_⟩
  · intro x hx hx'
    change χ x * Real.smoothTransition (δ * f x) = 1
    rw [hχ1 x (hKR hx), Real.smoothTransition.one_of_one_le, one_mul]
    have hh := mul_le_mul_of_nonneg_left hx' hδ.le
    rwa [mul_inv_cancel₀ hδ.ne'] at hh
  · have hI := integrable_abs_rpow_of_continuous_of_compactSupport hg.continuous hgs hp₀
    have hh := integral_mono hI (hfI.const_mul ((A * δ) ^ p)) (fun x ↦ by
      change |g x| ^ p ≤ (A * δ) ^ p * f x ^ p
      rw [abs_of_nonneg (h01 x).1, ← Real.mul_rpow hAδ (hf₀ x)]
      apply Real.rpow_le_rpow (h01 x).1 _ hp₀.le
      exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (hχ01 x).2).trans (hwp x))
    rw [integral_const_mul] at hh
    refine hh.trans ((mul_le_mul hbudget hfC (integral_nonneg fun x ↦ Real.rpow_nonneg (hf₀ x) _)
      (mul_nonneg (Real.rpow_nonneg hA.le _) hδ.le)).trans ?_)
    have hh' : A ^ p * C ≤ B := by
      dsimp only [B]
      have he : 0 ≤ (2 : ℝ) ^ (p - 1) * A ^ p * (Q ^ p * C + C) := by positivity
      linarith only [he]
    exact ((show A ^ p * δ * C = δ * (A ^ p * C) by ring).le.trans
      (mul_le_mul_of_nonneg_left hh' hδ.le)).trans hδε
  · intro i
    let e : PlanarCoordinates := Pi.single i 1
    let d (x : PlanarCoordinates) := fderiv ℝ f x e
    let P (x : PlanarCoordinates) := |fderiv ℝ g x e| ^ p
    have hd (x : PlanarCoordinates) : fderiv ℝ g x e =
        χ x * fderiv ℝ w x e + fderiv ℝ χ x e * w x := by
      change fderiv ℝ (χ * w) x e = _
      rw [fderiv_mul (hχ.differentiable (by norm_num) x) (hw.differentiable (by norm_num) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    let J := (2 : ℝ) ^ (p - 1) * (A * δ) ^ p
    have hJ : 0 ≤ J := by dsimp only [J]; positivity
    have hpoint (x : PlanarCoordinates) : P x ≤ J * (Q ^ p * f x ^ p + |d x| ^ p) := by
      have h₁ : |χ x * fderiv ℝ w x e| ≤ (A * δ) * |d x| := by
        rw [abs_mul, abs_of_nonneg (hχ01 x).1]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hχ01 x).2).trans (hwD x e)
      have h₂ : |fderiv ℝ χ x e * w x| ≤ (A * δ) * (Q * f x) := by
        rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact (mul_le_mul (hχD x i) (hwp x) (Real.smoothTransition.nonneg _) hQ).trans_eq (by ring)
      change |fderiv ℝ g x e| ^ p ≤ _
      rw [hd]
      refine (abs_add_rpow_le hp.le).trans ?_
      have hn₁ := Real.rpow_le_rpow (abs_nonneg _) h₁ hp₀.le
      have hn₂ := Real.rpow_le_rpow (abs_nonneg _) h₂ hp₀.le
      rw [Real.mul_rpow hAδ (abs_nonneg _)] at hn₁
      rw [Real.mul_rpow hAδ (mul_nonneg hQ (hf₀ x)), Real.mul_rpow hQ (hf₀ x)] at hn₂
      refine (mul_le_mul_of_nonneg_left (add_le_add hn₁ hn₂) (Real.rpow_nonneg (by norm_num) _)).trans_eq ?_
      dsimp only [J]
      ring
    have hc : Continuous (fun x ↦ fderiv ℝ g x e) :=
      ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    have hI : Integrable P volume :=
      integrable_abs_rpow_of_continuous_of_compactSupport hc (hgs.fderiv_apply ℝ e) hp₀
    have hi : Integrable (fun x ↦ |d x| ^ p) volume := (hfD i).1
    have hh := integral_mono hI (((hfI.const_mul (Q ^ p)).add hi).const_mul J) hpoint
    rw [integral_const_mul] at hh
    change (∫ x, P x ∂volume) ≤ J * ∫ x, Q ^ p * f x ^ p + |d x| ^ p ∂volume at hh
    rw [integral_add (hfI.const_mul _) hi, integral_const_mul] at hh
    refine hh.trans ?_
    have hF : (Q ^ p * ∫ x, f x ^ p ∂volume) + ∫ x, |d x| ^ p ∂volume ≤ Q ^ p * C + C :=
      add_le_add (mul_le_mul_of_nonneg_left hfC (Real.rpow_nonneg hQ _)) (hfD i).2
    refine (mul_le_mul_of_nonneg_left hF hJ).trans ?_
    have hJδ : J ≤ δ * ((2 : ℝ) ^ (p - 1) * A ^ p) := by
      change (2 : ℝ) ^ (p - 1) * (A * δ) ^ p ≤ _
      rw [← mul_assoc, mul_comm δ ((2 : ℝ) ^ (p - 1)), mul_assoc, mul_comm δ (A ^ p)]
      exact mul_le_mul_of_nonneg_left hbudget (Real.rpow_nonneg (by norm_num) _)
    have hCsum : 0 ≤ Q ^ p * C + C := by positivity
    refine (mul_le_mul_of_nonneg_right hJδ hCsum).trans ?_
    rw [mul_assoc]
    have hb : (2 : ℝ) ^ (p - 1) * A ^ p * (Q ^ p * C + C) ≤ B := by
      dsimp only [B]
      linarith only [show 0 ≤ A ^ p * C by positivity]
    exact (mul_le_mul_of_nonneg_left hb hδ.le).trans hδε

end CarpetEnergy
