import EnergyRootUniformConvex
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.Compact

/-!
# Quantitative midpoint deficits for powers of seminorms

A uniform gap at the unit radius gives a p-power deficit whenever
the two vectors are separated relative to that radius. For the
unequal-radius case the strict convexity of the scalar power supplies
the same positive deficit by compactness of the endpoint norms.
-/

open Function Set
open scoped Topology

namespace CarpetEnergy

private theorem rpow_midpoint_le {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((a + b) / 2) ^ p ≤ (a ^ p + b ^ p) / 2 := by
  have hc := (convexOn_rpow hp).2
  have h := hc (show a ∈ Ici (0 : ℝ) from ha) (show b ∈ Ici (0 : ℝ) from hb)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hab' : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  have hpab : (1 / 2 : ℝ) * a ^ p + (1 / 2 : ℝ) * b ^ p = (a ^ p + b ^ p) / 2 := by ring
  simpa only [smul_eq_mul, hab', hpab] using h

private theorem rpow_midpoint_lt {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) :
    ((a + b) / 2) ^ p < (a ^ p + b ^ p) / 2 := by
  have hc := (strictConvexOn_rpow hp).2
  have h := hc (show a ∈ Ici (0 : ℝ) from ha) (show b ∈ Ici (0 : ℝ) from hb) hab
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  have hab' : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  have hpab : (1 / 2 : ℝ) * a ^ p + (1 / 2 : ℝ) * b ^ p = (a ^ p + b ^ p) / 2 := by ring
  simpa only [smul_eq_mul, hab', hpab] using h

private theorem exists_unit_power_gap {p m : ℝ} (hp : 1 < p) (hm : 0 ≤ m) (hm₁ : m < 1) :
    ∃ δ > (0 : ℝ), ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      max a b = 1 → δ ≤ (a ^ p + b ^ p) / 2 - min ((a + b) / 2) m ^ p := by
  let g (s : ℝ) : ℝ := (1 + s ^ p) / 2 - min ((1 + s) / 2) m ^ p
  have hc : Continuous (fun s : ℝ ↦ s ^ p) := Real.continuous_rpow_const (zero_le_one.trans hp.le)
  have hg : Continuous g := ((continuous_const.add hc).div_const 2).sub
    (hc.comp (((continuous_const.add continuous_id).div_const 2).min continuous_const))
  obtain ⟨x, hx, hxMin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨1, zero_le_one, le_rfl⟩) hg.continuousOn
  have hpos (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < g s := by
    have hmin : 0 ≤ min ((1 + s) / 2) m := le_min (by linarith [hs.1]) hm
    by_cases h : s = 1
    · rw [h]
      change 0 < (1 + (1 : ℝ) ^ p) / 2 - min ((1 + 1) / 2) m ^ p
      rw [Real.one_rpow, show (1 + 1) / 2 = (1 : ℝ) by norm_num, min_eq_right hm₁.le]
      exact sub_pos.mpr ((Real.rpow_lt_rpow hm hm₁ (zero_lt_one.trans hp)).trans_eq (Real.one_rpow _))
    · have h₀ := rpow_midpoint_lt hp zero_le_one hs.1 (Ne.symm h)
      have h₁ := Real.rpow_le_rpow hmin (min_le_left _ _) (zero_le_one.trans hp.le)
      rw [Real.one_rpow] at h₀
      exact sub_pos.mpr (h₁.trans_lt h₀)
  refine ⟨g x, hpos x hx, fun a b ha hb hmax ↦ ?_⟩
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab] at hmax
    rw [hmax, add_comm a, Real.one_rpow, add_comm (a ^ p)]
    exact hxMin ha
  · rw [max_eq_left hba] at hmax
    rw [hmax, Real.one_rpow]
    exact hxMin hb

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A uniform midpoint gap controls the p-th power of a difference
by the sum of the endpoint energies and their midpoint deficit. -/
theorem power_deficit_controls_difference (S : Seminorm ℝ V) {p : ℝ} (hp : 1 < p)
    (hUC : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f g : V, S f ≤ 1 → S g ≤ 1 →
      ε ≤ S (f - g) → S ((1 / 2 : ℝ) • (f + g)) ≤ 1 - δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ f g : V,
      S (f - g) ^ p ≤ ε * (S f ^ p + S g ^ p) +
        C * ((S f ^ p + S g ^ p) / 2 - S ((1 / 2 : ℝ) • (f + g)) ^ p) := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  let d := ε ^ p⁻¹
  have hd : 0 < d := Real.rpow_pos_of_pos hε _
  obtain ⟨δ, hδ, hgap⟩ := hUC d hd
  let m := max (1 - δ) 0
  have hm : 0 ≤ m := le_max_right _ _
  have hm₁ : m < 1 := max_lt (sub_lt_self _ hδ) zero_lt_one
  obtain ⟨e, he, hE⟩ := exists_unit_power_gap hp hm hm₁
  let C : ℝ := (2 : ℝ) ^ p / e
  have hC : 0 ≤ C := div_nonneg (by positivity) he.le
  refine ⟨C, hC, fun f g ↦ ?_⟩
  let M := max (S f) (S g)
  have hM : 0 ≤ M := (apply_nonneg S f).trans (le_max_left _ _)
  have hmid (u v : V) : S ((1 / 2 : ℝ) • (u + v)) ≤ (S u + S v) / 2 := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith only [map_add_le_add S u v]
  have hdeficit : 0 ≤ (S f ^ p + S g ^ p) / 2 - S ((1 / 2 : ℝ) • (f + g)) ^ p := by
    apply sub_nonneg.mpr
    exact (Real.rpow_le_rpow (apply_nonneg _ _) (hmid f g) hp₀.le).trans
      (rpow_midpoint_le hp.le (apply_nonneg _ _) (apply_nonneg _ _))
  have hMpow : M ^ p ≤ S f ^ p + S g ^ p := by
    dsimp only [M]
    rcases le_total (S f) (S g) with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (apply_nonneg _ _) _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (apply_nonneg _ _) _)
  by_cases hclose : S (f - g) ≤ d * M
  · have h := Real.rpow_le_rpow (apply_nonneg S _) hclose hp₀.le
    rw [Real.mul_rpow hd.le hM, show d ^ p = ε from Real.rpow_inv_rpow hε.le hp₀.ne'] at h
    exact (h.trans (mul_le_mul_of_nonneg_left hMpow hε.le)).trans
      (le_add_of_nonneg_right (mul_nonneg hC hdeficit))
  have hsub : S (f - g) ≤ 2 * M := by
    have ht : S (f - g) ≤ S f + S g := by
      rw [sub_eq_add_neg]
      exact (map_add_le_add S f (-g)).trans_eq (by rw [map_neg_eq_map])
    exact ht.trans (by linarith only [le_max_left (S f) (S g), le_max_right (S f) (S g)])
  have hM₀ : 0 < M := by
    apply lt_of_le_of_ne hM
    intro hz
    rw [← hz, mul_zero] at hsub
    exact hclose (by rwa [← hz, mul_zero])
  let u := M⁻¹ • f
  let v := M⁻¹ • g
  have hu : S u = M⁻¹ * S f := by
    rw [show u = M⁻¹ • f from rfl, map_smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hM)]
  have hv : S v = M⁻¹ * S g := by
    rw [show v = M⁻¹ • g from rfl, map_smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hM)]
  have hu₁ : S u ≤ 1 := by rw [hu, inv_mul_le_iff₀ hM₀, mul_one]; exact le_max_left _ _
  have hv₁ : S v ≤ 1 := by rw [hv, inv_mul_le_iff₀ hM₀, mul_one]; exact le_max_right _ _
  have hmax : max (S u) (S v) = 1 := by
    rw [hu, hv, ← mul_max_of_nonneg _ _ (inv_nonneg.mpr hM)]
    exact inv_mul_cancel₀ hM₀.ne'
  have hsep : d ≤ S (u - v) := by
    change d ≤ S (M⁻¹ • f - M⁻¹ • g)
    rw [← smul_sub, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hM),
      le_inv_mul_iff₀ hM₀]
    rw [mul_comm M d]
    exact le_of_lt (lt_of_not_ge hclose)
  let z := S ((1 / 2 : ℝ) • (u + v))
  have hz : z ≤ min ((S u + S v) / 2) m :=
    le_min (hmid u v) ((hgap u v hu₁ hv₁ hsep).trans (le_max_left _ _))
  have hδpow : e ≤ (S u ^ p + S v ^ p) / 2 - z ^ p :=
    (hE _ _ ⟨apply_nonneg _ _, hu₁⟩ ⟨apply_nonneg _ _, hv₁⟩ hmax).trans
      (sub_le_sub_left (Real.rpow_le_rpow (apply_nonneg _ _) hz hp₀.le) _)
  have hscale (w : V) : S (M • w) ^ p = M ^ p * S w ^ p := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hM, Real.mul_rpow hM (apply_nonneg _ _)]
  have hfu : M • u = f := smul_inv_smul₀ hM₀.ne' f
  have hgv : M • v = g := smul_inv_smul₀ hM₀.ne' g
  have hmuv : M • ((1 / 2 : ℝ) • (u + v)) = (1 / 2 : ℝ) • (f + g) := by
    rw [smul_comm M, smul_add, hfu, hgv]
  have hdef : e * M ^ p ≤ (S f ^ p + S g ^ p) / 2 - S ((1 / 2 : ℝ) • (f + g)) ^ p := by
    have hsf : S f ^ p = M ^ p * S u ^ p := hfu ▸ hscale u
    have hsg : S g ^ p = M ^ p * S v ^ p := hgv ▸ hscale v
    have hm' : S ((1 / 2 : ℝ) • (f + g)) ^ p = M ^ p * z ^ p := hmuv ▸ hscale _
    rw [hsf, hsg, hm']
    have h := mul_le_mul_of_nonneg_right hδpow (Real.rpow_nonneg hM p)
    linarith only [h]
  have hb := Real.rpow_le_rpow (apply_nonneg S _) hsub hp₀.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hM] at hb
  have hh := mul_le_mul_of_nonneg_left hdef hC
  have hCe : C * e = (2 : ℝ) ^ p := div_mul_cancel₀ _ he.ne'
  rw [← mul_assoc, hCe] at hh
  exact (hb.trans hh).trans (le_add_of_nonneg_left (mul_nonneg hε.le
    (add_nonneg (Real.rpow_nonneg (apply_nonneg _ _) _) (Real.rpow_nonneg (apply_nonneg _ _) _))))

end CarpetEnergy
