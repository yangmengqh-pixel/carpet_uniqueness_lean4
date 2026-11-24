import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Combining a finite family of cutoffs in the Sobolev norm
-/

open Function Set
open scoped BigOperators

namespace CarpetEnergy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem nonnegative_abs_power_hasFDerivAt {p : ℝ} (hp : 1 < p)
    {f : V → ℝ} {A : V →L[ℝ] ℝ} {x : V} (hf : HasFDerivAt f A x) (hx : 0 ≤ f x) :
    HasFDerivAt (fun y ↦ |f y| ^ p) ((p * (f x) ^ (p - 1)) • A) x := by
  have hh := (hasDerivAt_abs_rpow (f x) hp).comp_hasFDerivAt x hf
  rw [abs_of_nonneg hx] at hh
  have he : p * (f x) ^ (p - 2) * f x = p * (f x) ^ (p - 1) := by
    rcases hx.eq_or_lt with h | h
    · rw [← h, mul_zero, Real.zero_rpow (sub_pos.mpr hp).ne', mul_zero]
    · rw [mul_assoc]
      have hpow : (f x) ^ (p - 2) * f x = (f x) ^ (p - 1) := by
        calc
          _ = (f x) ^ (p - 2) * (f x) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add h]; congr 1; ring
      rw [hpow]
  rw [he] at hh
  exact hh

theorem exists_deriv_bound_smoothTransition :
    ∃ C > (0 : ℝ), ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hf : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨x, _, hx⟩ := (isCompact_Icc (α := ℝ)).exists_isMaxOn
    (nonempty_Icc.mpr zero_le_one) (hf.continuous_deriv (by norm_num)).abs.continuousOn
  refine ⟨max |deriv Real.smoothTransition x| 1, zero_lt_one.trans_le (le_max_right _ _), fun t ↦ ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hx ht).trans (le_max_left _ _)
  have h : deriv Real.smoothTransition t = 0 := by
    rcases not_and_or.mp ht with h | h
    · have he : Real.smoothTransition =ᶠ[nhds t] fun _ ↦ (0 : ℝ) :=
        (gt_mem_nhds (lt_of_not_ge h)).mono (fun _ ht' ↦ Real.smoothTransition.zero_of_nonpos ht'.le)
      rw [he.deriv_eq, deriv_const]
    · have he : Real.smoothTransition =ᶠ[nhds t] fun _ ↦ (1 : ℝ) :=
        (lt_mem_nhds (lt_of_not_ge h)).mono (fun _ ht' ↦ Real.smoothTransition.one_of_one_le ht'.le)
      rw [he.deriv_eq, deriv_const]
  rw [h, abs_zero]
  exact zero_le_one.trans (le_max_right _ _)

set_option maxHeartbeats 3000000 in
/-- Cutoffs with values in ([0,1]) combine to a cutoff equal to one
where any input is one. Its derivative has the finite (L^p) budget
of the inputs with a constant independent of the number of cutoffs. -/
theorem exists_smooth_cutoff_family {p : ℝ} (hp : 1 < p) :
    ∃ C > (0 : ℝ), ∀ {m : ℕ} (f : Fin m → V → ℝ),
      (∀ j, ContDiff ℝ 1 (f j)) → (∀ j x, f j x ∈ Icc (0 : ℝ) 1) →
      ∃ g : V → ℝ, ContDiff ℝ 1 g ∧
        (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, (∃ j, f j x = 1) → g x = 1) ∧
        (∀ x, (∀ j, f j x = 0) → g x = 0) ∧
        ∀ x e, |fderiv ℝ g x e| ^ p ≤ C * ∑ j, |fderiv ℝ (f j) x e| ^ p := by
  obtain ⟨D, hD, hD'⟩ := exists_deriv_bound_smoothTransition
  refine ⟨(D * p) ^ p, Real.rpow_pos_of_pos (mul_pos hD (zero_lt_one.trans hp)) _, ?_⟩
  intro m f hf h01
  let S (x : V) := ∑ j, |f j x| ^ p
  let B (j : Fin m) (x : V) := (p * (f j x) ^ (p - 1)) • fderiv ℝ (f j) x
  let g := Real.smoothTransition ∘ S
  have hB (j : Fin m) (x : V) : HasFDerivAt (fun y ↦ |f j y| ^ p) (B j x) x :=
    nonnegative_abs_power_hasFDerivAt hp ((hf j).differentiable (by norm_num) x).hasFDerivAt (h01 j x).1
  have hC (j : Fin m) : ContDiff ℝ 1 (fun y ↦ |f j y| ^ p) := by
    apply contDiff_one_iff_fderiv.mpr
    refine ⟨fun x ↦ (hB j x).differentiableAt, ?_⟩
    have he : fderiv ℝ (fun y ↦ |f j y| ^ p) = B j := funext fun x ↦ (hB j x).fderiv
    rw [he]
    exact (continuous_const.mul ((hf j).continuous.rpow_const
      (fun _ ↦ Or.inr (sub_nonneg.mpr hp.le)))).smul ((hf j).continuous_fderiv (by norm_num))
  have hS : ContDiff ℝ 1 S := ContDiff.sum (fun j _ ↦ hC j)
  have hdS (x : V) : HasFDerivAt S (∑ j, B j x) x :=
    HasFDerivAt.fun_sum (fun j _ ↦ hB j x)
  have hθ : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  refine ⟨g, hθ.comp hS, fun _ ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    ?_, ?_, ?_⟩
  · rintro x ⟨j, hj⟩
    apply Real.smoothTransition.one_of_one_le
    have h := Finset.single_le_sum (f := fun j ↦ |f j x| ^ p)
      (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) p) (Finset.mem_univ j)
    simpa only [hj, abs_one, Real.one_rpow] using h
  · intro x hx
    simp only [g, Function.comp_apply, S, hx, abs_zero, Real.zero_rpow (zero_lt_one.trans hp).ne',
      Finset.sum_const_zero, Real.smoothTransition.zero]
  · intro x e
    have hder : fderiv ℝ g x e = deriv Real.smoothTransition (S x) * (∑ j, B j x e) := by
      have ht := (hθ.differentiable (by norm_num) (S x)).hasDerivAt
      rw [(ht.comp_hasFDerivAt x (hdS x)).fderiv, smul_apply,
        sum_apply, smul_eq_mul]
    have hnn : 0 ≤ (D * p) ^ p * ∑ j, |fderiv ℝ (f j) x e| ^ p :=
      mul_nonneg (Real.rpow_nonneg (mul_nonneg hD.le (zero_lt_one.trans hp).le) _)
        (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    by_cases hS₁ : 1 < S x
    · have he : Real.smoothTransition =ᶠ[nhds (S x)] fun _ ↦ (1 : ℝ) :=
        (lt_mem_nhds hS₁).mono (fun _ h ↦ Real.smoothTransition.one_of_one_le h.le)
      rw [hder, he.deriv_eq, deriv_const, zero_mul, abs_zero, Real.zero_rpow (zero_lt_one.trans hp).ne']
      exact hnn
    have hp₀ := zero_lt_one.trans hp
    let q := p.conjExponent
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
    have hqp : q * (p - 1) = p := by
      dsimp only [q, Real.conjExponent]
      field_simp
    have hsum (j : Fin m) : ((f j x) ^ (p - 1)) ^ q = |f j x| ^ p := by
      rw [← Real.rpow_mul (h01 j x).1, mul_comm, hqp, abs_of_nonneg (h01 j x).1]
    have hHold := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hpq.symm
      (f := fun j ↦ (f j x) ^ (p - 1)) (g := fun j ↦ |fderiv ℝ (f j) x e|)
      (fun j _ ↦ Real.rpow_nonneg (h01 j x).1 _) (fun _ _ ↦ abs_nonneg _)
    simp only [hsum, one_div] at hHold
    have hSnn : 0 ≤ S x := Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    have hSr : (S x) ^ q⁻¹ ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow hSnn (not_lt.mp hS₁) (inv_nonneg.mpr hpq.symm.nonneg)
    let M := ∑ j, |fderiv ℝ (f j) x e| ^ p
    have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    have hsumB : (∑ j, |B j x e|) ≤ p * M ^ p⁻¹ := by
      have he (j : Fin m) : |B j x e| = p * ((f j x) ^ (p - 1) * |fderiv ℝ (f j) x e|) := by
        dsimp only [B]
        rw [smul_apply, smul_eq_mul, abs_mul,
          abs_of_nonneg (mul_nonneg hp₀.le (Real.rpow_nonneg (h01 j x).1 _)), mul_assoc]
      simp only [he, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hp₀.le
      exact hHold.trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hSr (Real.rpow_nonneg hM _))
    have hroot : |fderiv ℝ g x e| ≤ (D * p) * M ^ p⁻¹ := by
      rw [hder, abs_mul, mul_assoc]
      exact mul_le_mul (hD' _) ((Finset.abs_sum_le_sum_abs _ _).trans hsumB)
        (abs_nonneg _) hD.le
    refine (Real.rpow_le_rpow (abs_nonneg _) hroot hp₀.le).trans_eq ?_
    rw [Real.mul_rpow (mul_nonneg hD.le hp₀.le) (Real.rpow_nonneg hM _),
      Real.rpow_inv_rpow hM hp₀.ne']

end CarpetEnergy
