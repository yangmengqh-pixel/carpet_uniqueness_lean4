import LpFunctionalBoundedTests
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Basic.Real.ConjExponents

/-!
# The conjugate-exponent bound for the representing density

Testing with signed, truncated powers of the Radon–Nikodym
density bounds its Lp norm. Monotone convergence removes the
truncation.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

private theorem pow_le_of_le_mul_pow {p q a C : ℝ} (hpq : p.HolderConjugate q)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (h : a ≤ C * a ^ q⁻¹) : a ≤ C ^ p := by
  rcases ha.eq_or_lt with ha | ha
  · rw [← ha]
    exact Real.rpow_nonneg hC _
  have hpos : 0 < a ^ q⁻¹ := Real.rpow_pos_of_pos ha _
  have hle := (div_le_iff₀ hpos).mpr h
  have he : 1 - q⁻¹ = p⁻¹ := by linarith only [hpq.inv_add_inv_eq_one]
  have he' : a / a ^ q⁻¹ = a ^ p⁻¹ := by
    rw [← he, Real.rpow_sub ha, Real.rpow_one]
  rw [he'] at hle
  have hp : 0 < p := zero_lt_one.trans hpq.lt
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg ha.le _) hle hp.le
  rwa [Real.rpow_inv_rpow ha.le hp.ne'] at hh

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

set_option maxHeartbeats 2200000 in
/-- Continuous linear functionals on real Lq over a finite measure are
represented on bounded measurable tests by a measurable Lp density. -/
theorem exists_memLp_density_of_LpFunctional {p q : ℝ} (hpq : p.HolderConjugate q)
    [Fact (1 ≤ ENNReal.ofReal q)] (L : Lp ℝ (ENNReal.ofReal q) μ →L[ℝ] ℝ) :
    ∃ f : X → ℝ, Measurable f ∧ MemLp f (ENNReal.ofReal p) μ ∧
      ∀ (g : X → ℝ) (hg : Measurable g) (B : ℝ) (_hB : 0 ≤ B) (hb : ∀ x, |g x| ≤ B),
        L ((MemLp.of_bound (p := ENNReal.ofReal q) hg.aestronglyMeasurable B
          (Eventually.of_forall fun x ↦ (Real.norm_eq_abs (g x)).symm ▸ hb x)).toLp g) =
          ∫ x, f x * g x ∂μ := by
  obtain ⟨f, hfm, hf, h⟩ := exists_density_LpFunctional_bounded_tests ENNReal.ofReal_ne_top L
  refine Exists.intro f (And.intro hfm (And.intro ?_ h))
  change eLpNorm f (ENNReal.ofReal p) μ < ∞
  have hp : 0 < p := zero_lt_one.trans hpq.lt
  have hq : 0 < q := zero_lt_one.trans hpq.symm.lt
  have hp₁ : 0 ≤ p - 1 := sub_nonneg.mpr hpq.lt.le
  let a (n : ℕ) (x : X) := min |f x| (n : ℝ)
  let d (n : ℕ) (x : X) := a n x ^ p
  have ha (n : ℕ) (x : X) : 0 ≤ a n x := le_min (abs_nonneg _) (Nat.cast_nonneg _)
  have haN (n : ℕ) (x : X) : a n x ≤ (n : ℝ) := min_le_right _ _
  have hm (n : ℕ) : Measurable (a n) := (continuous_abs.measurable.comp hfm).min measurable_const
  have hd (n : ℕ) : Measurable (d n) :=
    ((Real.continuous_rpow_const hp.le).measurable).comp (hm n)
  have hInt (n : ℕ) : Integrable (d n) μ := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound (hd n).aestronglyMeasurable ((n : ℝ) ^ p)
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (ha n x) p)]
    exact Real.rpow_le_rpow (ha n x) (haN n x) hp.le
  have hbound (n : ℕ) : (∫ x, d n x ∂μ) ≤ ‖L‖ ^ p := by
    let b (x : X) := a n x ^ (p - 1)
    let g (x : X) := if 0 ≤ f x then b x else -b x
    have hb₀ (x : X) : 0 ≤ b x := Real.rpow_nonneg (ha n x) _
    have hb (x : X) : |g x| = b x := by
      unfold g
      split_ifs <;> simp only [abs_neg, abs_of_nonneg (hb₀ x)]
    have hb' (x : X) : |g x| ≤ (n : ℝ) ^ (p - 1) := by
      rw [hb]
      exact Real.rpow_le_rpow (ha n x) (haN n x) hp₁
    have hbM : Measurable b := (Real.continuous_rpow_const hp₁).measurable.comp (hm n)
    have hg : Measurable g := hbM.ite (measurableSet_le measurable_const hfm) hbM.neg
    have hgLp : MemLp g (ENNReal.ofReal q) μ := MemLp.of_bound hg.aestronglyMeasurable
      ((n : ℝ) ^ (p - 1)) (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hb' x)
    have heq := h g hg ((n : ℝ) ^ (p - 1)) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hb'
    change L (hgLp.toLp g) = _ at heq
    have hprod (x : X) : f x * g x = |f x| * b x := by
      unfold g
      split_ifs with h₀
      · rw [abs_of_nonneg h₀]
      · rw [abs_of_neg (lt_of_not_ge h₀), neg_mul, mul_neg]
    have hle (x : X) : d n x ≤ f x * g x := by
      rw [hprod]
      have had : d n x = a n x * b x := by
        change a n x ^ p = a n x * a n x ^ (p - 1)
        have he : 1 + (p - 1) = p := by ring
        conv_lhs => rw [← he]
        rw [Real.rpow_add' (ha n x) (show (1 : ℝ) + (p - 1) ≠ 0 by rw [he]; exact hp.ne'),
          Real.rpow_one]
      rw [had]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (hb₀ x)
    have hI := integral_mono (hInt n)
      (hf.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]; exact hb' x)) hle
    have hnorm : ‖hgLp.toLp g‖ = (∫ x, d n x ∂μ) ^ q⁻¹ := by
      rw [Lp.norm_toLp, toReal_eLpNorm,
        lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
          hg.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change ‖g x‖ ^ q = d n x
      rw [Real.norm_eq_abs, hb]
      change (a n x ^ (p - 1)) ^ q = a n x ^ p
      rw [← Real.rpow_mul (ha n x), hpq.sub_one_mul_conj]
    have hL := L.le_opNorm (hgLp.toLp g)
    rw [heq, hnorm, Real.norm_eq_abs] at hL
    apply pow_le_of_le_mul_pow hpq (integral_nonneg fun x ↦ Real.rpow_nonneg (ha n x) _) (norm_nonneg L)
    exact hI.trans ((le_abs_self _).trans hL)
  have hMono : Monotone (fun n x ↦ ENNReal.ofReal (d n x)) := by
    intro n m hnm x
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (ha n x) (min_le_min_left _ (Nat.cast_le.mpr hnm)) hp.le
  have hSup (x : X) : (⨆ n, ENNReal.ofReal (d n x)) = ENNReal.ofReal (|f x| ^ p) := by
    apply le_antisymm
    · exact iSup_le fun n ↦ ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (ha n x) (min_le_left _ _) hp.le)
    · let n := Nat.ceil |f x|
      have he : a n x = |f x| := min_eq_left (Nat.le_ceil _)
      rw [← he]
      exact le_iSup (fun n ↦ ENNReal.ofReal (d n x)) n
  apply (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hfm.aestronglyMeasurable).mpr
  have hlin : (∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ) ≤ ENNReal.ofReal (‖L‖ ^ p) := by
    simp_rw [← hSup]
    have hD (n : ℕ) : Measurable (fun x ↦ ENNReal.ofReal (d n x)) :=
      ENNReal.continuous_ofReal.measurable.comp (hd n)
    rw [lintegral_iSup (μ := μ) hD hMono]
    refine iSup_le fun n ↦ ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt n)
      (Eventually.of_forall fun x ↦ Real.rpow_nonneg (ha n x) _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  simp_rw [ENNReal.toReal_ofReal hp.le, ← ofReal_norm, Real.norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  exact hlin.trans_lt ENNReal.ofReal_lt_top

end CarpetEnergy
