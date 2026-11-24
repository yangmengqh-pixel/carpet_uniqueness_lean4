import EnergySelfSimilarSmoothness
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Linear first variations from a symmetric increment bound
-/

open Asymptotics Filter Set
open scoped Topology

namespace CarpetEnergy

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

theorem exists_seminorm_norming (S : Seminorm ℝ X) (x : X) :
    ∃ L : X →ₗ[ℝ] ℝ, L x = S x ∧ ∀ z, |L z| ≤ S z := by
  by_cases hS : S x = 0
  · exact ⟨0, by simp [hS], fun z ↦ by simpa only [LinearMap.zero_apply, abs_zero] using apply_nonneg S z⟩
  have hx : x ≠ 0 := fun hx ↦ hS (hx.symm ▸ map_zero S)
  let V := Submodule.span ℝ ({x} : Set X)
  let e : ℝ ≃ₗ[ℝ] V := LinearEquiv.toSpanNonzeroSingleton ℝ X x hx
  let ℓ : V →ₗ[ℝ] ℝ := S x • e.symm.toLinearMap
  have he (z : V) : e.symm z • x = (z : X) :=
    LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℝ X x hx z
  have hb (z : V) : ℓ z ≤ S z := by
    calc
      ℓ z = S x * e.symm z := rfl
      _ ≤ S x * |e.symm z| := mul_le_mul_of_nonneg_left (le_abs_self _) (apply_nonneg S _)
      _ = S (e.symm z • x) := by rw [map_smul_eq_mul, Real.norm_eq_abs, mul_comm]
      _ = S z := by rw [he z]
  obtain ⟨L, hL, hnorm⟩ := Module.Dual.exists_extension_of_le_seminorm_real V ℓ hb
  refine ⟨L, ?_, hnorm⟩
  have ht := hL (e 1)
  change L (e 1 : V) = S x * e.symm (e 1) at ht
  rw [e.symm_apply_apply, mul_one] at ht
  change L ((1 : ℝ) • x) = S x at ht
  simpa only [one_smul] using ht

private theorem two_mul_abs_rpow_le_symm {p : ℝ} (hp : 1 < p) (r s : ℝ) :
    2 * |r| ^ p ≤ |r + s| ^ p + |r - s| ^ p := by
  have ht := abs_add_le (r + s) (r - s)
  rw [show r + s + (r - s) = 2 * r by ring, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
  have hr : |r| ≤ (1 / 2 : ℝ) * |r + s| + (1 / 2 : ℝ) * |r - s| := by linarith only [ht]
  have hpow := Real.rpow_le_rpow (abs_nonneg _) hr (zero_lt_one.trans hp).le
  have hcv := (convexOn_rpow hp.le).2 (mem_Ici.mpr (abs_nonneg (r + s)))
    (mem_Ici.mpr (abs_nonneg (r - s))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hcv
  have hh := hpow.trans hcv
  linarith only [hh]

set_option maxHeartbeats 1000000 in
/-- If a p-power of a seminorm satisfies the uniform symmetric increment
bound, its directional derivatives are given by a single linear
functional at each base point. -/
theorem exists_linear_first_variation_of_uniformSymmetricIncrement
    (S : Seminorm ℝ X) {p : ℝ} (hp : 1 < p)
    (h : HasUniformSymmetricIncrement (fun z ↦ (S z) ^ p)) (x : X) :
    ∃ L : X →ₗ[ℝ] ℝ, ∀ y : X,
      HasDerivAt (fun t : ℝ ↦ S (x + t • y) ^ p) (p * L y) 0 := by
  obtain ⟨L, hL, hdom⟩ := exists_seminorm_norming S x
  let r := S x
  let c := |r| ^ (p - 2) * r
  refine ⟨c • L, fun y ↦ ?_⟩
  let F (t : ℝ) := S (x + t • y) ^ p
  let G (t : ℝ) := |r + t * L y| ^ p
  have hr : 0 ≤ r := apply_nonneg S x
  have hzero : F 0 = G 0 := by
    simp only [F, G, zero_smul, zero_mul, add_zero, abs_of_nonneg hr]
    rfl
  have hdom' (t : ℝ) : G t ≤ F t := by
    apply Real.rpow_le_rpow (abs_nonneg _) _ (zero_lt_one.trans hp).le
    have hh := hdom (x + t • y)
    rw [map_add, map_smul, smul_eq_mul, hL] at hh
    exact hh
  have heven (t : ℝ) : 2 * F 0 ≤ G t + G (-t) := by
    rw [hzero]
    simpa only [G, zero_mul, add_zero, neg_mul, ← sub_eq_add_neg] using
      two_mul_abs_rpow_le_symm hp r (t * L y)
  have hdiff : (fun t ↦ F t - G t) =o[𝓝 (0 : ℝ)] (fun t ↦ t) := by
    apply isLittleO_iff.mpr
    intro ε hε
    let C := (S x) ^ p + (S y) ^ p
    have hC : 0 ≤ C := add_nonneg (Real.rpow_nonneg (apply_nonneg S _) _) (Real.rpow_nonneg (apply_nonneg S _) _)
    let a := ε / (C + 1)
    have ha : 0 < a := div_pos hε (by positivity)
    have haC : a * C ≤ ε := by
      dsimp only [a]
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ (by positivity : 0 < C + 1)).mpr (by linarith)
    obtain ⟨δ, hδ, hδest⟩ := h a ha
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have ht' : |t| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    have hs := hδest x y t ht'
    have hm : F t + F (-t) ≤ 2 * F 0 + a * |t| * C := by
      dsimp only [F, C]
      rw [zero_smul, add_zero, neg_smul, ← sub_eq_add_neg]
      linarith only [hs, show
        (2 + a * |t|) * S x ^ p + a * |t| * S y ^ p =
          2 * S x ^ p + a * |t| * (S x ^ p + S y ^ p) by ring]
    have hx : F t - G t ≤ a * |t| * C := by linarith only [hm, heven t, hdom' (-t)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hdom' t))]
    exact hx.trans (by
      rw [mul_right_comm a _ C]
      exact mul_le_mul_of_nonneg_right haC (abs_nonneg _))
  have hg : HasDerivAt G (p * (c • L) y) 0 := by
    have hlin : HasDerivAt (fun t : ℝ ↦ r + t * L y) (L y) 0 := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (L y)).const_add r
    have h := (hasDerivAt_abs_rpow (r + (0 : ℝ) * L y) hp).comp 0 hlin
    change HasDerivAt G _ 0 at h
    simpa only [zero_mul, add_zero, LinearMap.smul_apply, smul_eq_mul, c, mul_assoc] using h
  apply hasDerivAt_iff_isLittleO.mpr
  have hb := hg.isLittleO
  simp only [sub_zero] at hb ⊢
  have hs := hdiff.add hb
  convert hs using 1
  funext t
  change F t - F 0 - t * (p * (c • L) y) =
    F t - G t + (G t - G 0 - t * (p * (c • L) y))
  rw [hzero]
  ring

end CarpetEnergy
