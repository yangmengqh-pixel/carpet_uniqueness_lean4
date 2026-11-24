import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A smooth finite maximum with a uniform directional derivative bound
-/

open Function Filter Set
open scoped BigOperators

namespace CarpetEnergy

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

set_option maxHeartbeats 3500000 in
/-- The logarithm of the mean exponential approximates the maximum
with error at most one and takes convex averages of the directional derivatives. -/
theorem exists_smooth_finite_maximum [Nonempty ι] (f : ι → X → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (h₀ : ∀ i x, 0 ≤ f i x) :
    ∃ g : X → ℝ, ContDiff ℝ 1 g ∧ (∀ x, 0 ≤ g x) ∧
      (∀ i x, f i x - 1 ≤ g x) ∧ (∀ x, ∃ i, g x ≤ f i x) ∧
      ∀ (x z : X) (D : ℝ), (∀ i, |fderiv ℝ (f i) x z| ≤ D) →
        |fderiv ℝ g x z| ≤ D := by
  classical
  let N := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hN₁ : 1 ≤ N := by
    have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
    change (1 : ℝ) ≤ (Fintype.card ι : ℝ)
    exact_mod_cast hn
  let a := Real.log N + 1
  have ha : 0 < a := add_pos_of_nonneg_of_pos (Real.log_nonneg hN₁) one_pos
  let F (i : ι) (x : X) := Real.exp (a * f i x)
  let S (x : X) := ∑ i, F i x
  let g (x : X) := (Real.log (S x / N)) / a
  have hNle (x : X) : N ≤ S x := by
    have h := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : ι ↦ (1 : ℝ))
      (g := fun i ↦ F i x) fun i _ ↦ Real.one_le_exp (mul_nonneg ha.le (h₀ i x))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] using h
  have hS (x : X) : 0 < S x := hN.trans_le (hNle x)
  have hSc : ContDiff ℝ 1 S := ContDiff.sum (s := Finset.univ) (fun i _ ↦ (contDiff_const.mul (hf i)).exp)
  have hg : ContDiff ℝ 1 g := ((hSc.div_const N).log (fun x ↦ (div_pos (hS x) hN).ne')).div_const a
  have hlog (x : X) : g x = (Real.log (S x) - Real.log N) / a := by
    dsimp only [g]
    rw [Real.log_div (hS x).ne' hN.ne']
  refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
  · intro x
    exact div_nonneg (Real.log_nonneg ((le_div_iff₀ hN).mpr (by rw [one_mul]; exact hNle x))) ha.le
  · intro i x
    have hsingle : F i x ≤ S x :=
      Finset.single_le_sum (fun j _ ↦ (Real.exp_pos (a * f j x)).le) (Finset.mem_univ i)
    have hh := Real.log_le_log (Real.exp_pos (a * f i x)) hsingle
    change Real.log (Real.exp (a * f i x)) ≤ Real.log (S x) at hh
    rw [Real.log_exp] at hh
    rw [hlog]
    apply (le_div_iff₀ ha).mpr
    dsimp only [a] at *
    nlinarith only [hh]
  · intro x
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset ι) (fun i ↦ f i x) Finset.univ_nonempty
    have hSle : S x ≤ N * Real.exp (a * f i x) := by
      calc
        _ ≤ ∑ _ : ι, Real.exp (a * f i x) := Finset.sum_le_sum fun j hj ↦
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hi j hj) ha.le)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    have hdiv : S x / N ≤ Real.exp (a * f i x) := (div_le_iff₀ hN).mpr
      (hSle.trans_eq (mul_comm _ _))
    have hh := Real.log_le_log (div_pos (hS x) hN) hdiv
    rw [Real.log_exp] at hh
    exact ⟨i, (div_le_iff₀ ha).mpr (hh.trans_eq (mul_comm _ _))⟩
  · intro x z D hD
    let T (i : ι) := fderiv ℝ (f i) x
    have hFi (i : ι) : HasFDerivAt (F i) ((F i x * a) • T i) x := by
      have hh := (Real.hasDerivAt_exp (a * f i x)).comp_hasFDerivAt x
        (((hf i).differentiable (by norm_num) x).hasFDerivAt.const_mul a)
      change HasFDerivAt (Real.exp ∘ fun y ↦ a * f i y)
        ((Real.exp (a * f i x) * a) • fderiv ℝ (f i) x) x
      rw [← smul_smul]
      exact hh
    have hSsum : S = ∑ i, F i := by
      funext y
      simp only [S, Finset.sum_apply]
    have hSd : HasFDerivAt S (∑ i, (F i x * a) • T i) x := by
      rw [hSsum]
      exact HasFDerivAt.sum (u := Finset.univ) (fun i _ ↦ hFi i)
    have hgD := ((Real.hasDerivAt_log (hS x).ne').comp_hasFDerivAt x hSd).sub_const (Real.log N)
    have hgD' := hgD.const_mul a⁻¹
    have he : g = fun x ↦ a⁻¹ * ((Real.log ∘ S) x - Real.log N) :=
      funext (fun y ↦ (hlog y).trans (div_eq_inv_mul _ _))
    rw [he, hgD'.fderiv, smul_smul, smul_apply, sum_apply]
    have hsum : |∑ i, ((F i x * a) • T i) z| ≤ a * (S x * D) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      have hFn (i : ι) : 0 ≤ F i x * a := mul_nonneg (Real.exp_pos (a * f i x)).le ha.le
      calc
        _ = ∑ i, (F i x * a) * |T i z| := by
          refine Finset.sum_congr rfl (fun i _ ↦ ?_)
          rw [smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hFn i)]
        _ ≤ ∑ i, (F i x * a) * D := Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hD i) (hFn i)
        _ = _ := by simp only [S, ← Finset.sum_mul]; ring
    have hcoeff : 0 ≤ a⁻¹ * (S x)⁻¹ := mul_nonneg (inv_nonneg.mpr ha.le) (inv_nonneg.mpr (hS x).le)
    rw [smul_eq_mul, abs_mul, abs_of_nonneg hcoeff]
    refine (mul_le_mul_of_nonneg_left hsum hcoeff).trans_eq ?_
    field_simp [ha.ne', (hS x).ne']

end CarpetEnergy
