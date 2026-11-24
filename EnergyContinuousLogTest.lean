import EnergyTwoCoordinateVariation
import EnergyClippedHarmonic
import EnergySmoothCompositionBound
import SmoothPositiveShift
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Logarithmic energy estimate for continuous harmonic profiles

The cutoff test against harmonicity bounds the integral of
((f+\varepsilon)^{-p}) against the energy measure, weighted by a
power of the cutoff.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem variation_eq_zero_of_harmonicOn (h : E.HasLinearFirstVariations)
    {U : Set CarpetPoints} {f : E.continuousCore} (hf : E.IsHarmonicOn U f)
    (v : E.continuousCore) (hv : ∀ x ∉ U, v.val x = 0) :
    E.variation h (E.continuousCoreToDomain f) (E.continuousCoreToDomain v) = 0 := by
  let d := E.continuousCoreToDomain f
  have hmin : IsLocalMin (fun t : ℝ ↦
      (E.energy (d + t • E.continuousCoreToDomain v) : ℝ)) 0 := by
    apply Eventually.of_forall
    intro t
    change (E.energy (d + (0 : ℝ) • E.continuousCoreToDomain v) : ℝ) ≤ _
    rw [zero_smul, add_zero]
    have ht := hf (t • v) (fun x hx ↦ by change t * v.val x = 0; rw [hv x hx, mul_zero])
    rw [map_add, map_smul] at ht
    exact NNReal.coe_le_coe.mpr ht
  have hz := hmin.hasDerivAt_eq_zero (E.hasDerivAt_energy_variation h d _)
  exact (mul_eq_zero.mp hz).resolve_left (zero_lt_one.trans E.one_lt_p).ne'

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem log_budget_of_holder {q I J m : ℝ} (hpq : p.HolderConjugate q)
    (hI : 0 ≤ I) (hJ : 0 ≤ J) (hm : 0 ≤ m)
    (hb : (p - 1) * I ≤ m * (I ^ q⁻¹ * J ^ p⁻¹)) :
    I ≤ (m / (p - 1)) ^ p * J := by
  rcases hI.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (Real.rpow_nonneg (div_nonneg hm (sub_nonneg.mpr hpq.lt.le)) _) hJ
  have ht : I = I ^ q⁻¹ * I ^ p⁻¹ := by
    rw [← Real.rpow_add hpos, hpq.symm.inv_add_inv_eq_one, Real.rpow_one]
  have hh : (p - 1) * I ^ p⁻¹ ≤ m * J ^ p⁻¹ := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hpos q⁻¹)).mp
    calc
      _ = (p - 1) * (I ^ q⁻¹ * I ^ p⁻¹) := by ring
      _ = (p - 1) * I := by rw [← ht]
      _ ≤ _ := hb
      _ = _ := by ring
  have hroot : I ^ p⁻¹ ≤ (m / (p - 1)) * J ^ p⁻¹ := by
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ (sub_pos.mpr hpq.lt)).mpr ?_
    exact (mul_comm _ _).trans_le hh
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hroot hpq.nonneg
  rwa [Real.rpow_inv_rpow hI hpq.ne_zero, Real.mul_rpow
    (div_nonneg hm (sub_nonneg.mpr hpq.lt.le)) (Real.rpow_nonneg hJ _),
    Real.rpow_inv_rpow hJ hpq.ne_zero] at h

set_option maxHeartbeats 4200000 in
/-- A logarithmic test with its energy bounded uniformly in the base
profile's energy. Its first variation is the residual in the log estimate. -/
theorem exists_logarithmic_test
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {U : Set CarpetPoints} (f χ : E.continuousCore)
    (hf₀ : ∀ x, 0 ≤ f.val x) (hχ : ∀ x, χ.val x ∈ Icc (0 : ℝ) 1)
    (hχ₀ : ∀ x ∉ U, χ.val x = 0) {ε : ℝ} (hε : 0 < ε)
    (m : ℕ) (hm : p ≤ (m : ℝ)) :
    let d := E.continuousCoreToDomain f
    let dχ := E.continuousCoreToDomain χ
    let I := ∫ x, (χ.val x) ^ m * (f.val x + ε) ^ (-p) ∂E.energyMeasure d
    ∃ v : E.continuousCore, (∀ x ∉ U, v.val x = 0) ∧
      E.rootSeminorm (E.continuousCoreToDomain v) ≤
        (p - 1) * ε ^ (-p) * E.rootSeminorm d +
        (m : ℝ) * ε ^ (1 - p) * E.rootSeminorm dχ ∧
      (p - 1) * I ≤ (m : ℝ) * (I ^ p.conjExponent⁻¹ * (E.energy dχ : ℝ) ^ p⁻¹) +
        |E.variation h d (E.continuousCoreToDomain v)| := by
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent E.one_lt_p
  have hm₀ : m ≠ 0 := by
    intro h0
    subst m
    norm_num at hm
    linarith [E.one_lt_p]
  obtain ⟨S, hS, hSp, hSid⟩ := exists_smooth_positive_shift hε
  let C := Fin 2 → ℝ
  let P₀ : C →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let P₁ : C →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  let T (y : C) := S (y 0) ^ (1 - p)
  let φ (y : C) := (y 1) ^ m * T y
  let H : Fin 2 → E.continuousCore := ![f, χ]
  let F := E.continuousCoreTuple H
  have hF₀ (x : CarpetPoints) : F x 0 = f.val x := rfl
  have hF₁ (x : CarpetPoints) : F x 1 = χ.val x := rfl
  have hT : ContDiff ℝ 1 T := (hS.comp P₀.contDiff).rpow_const_of_ne (fun y ↦ (hSp (y 0)).ne')
  have hφ : ContDiff ℝ 1 φ := (P₁.contDiff.pow _).mul hT
  obtain ⟨v, hv⟩ := E.exists_core_comp_contDiff hc H φ hφ
  have hv₀ (x : CarpetPoints) (hx : x ∉ U) : v.val x = 0 := by
    rw [hv, show φ (F x) = (χ.val x) ^ m * T (F x) from rfl, hχ₀ x hx, zero_pow hm₀, zero_mul]
  let W : C(CarpetPoints, ℝ) := ⟨fun x ↦ (χ.val x) ^ m * (f.val x + ε) ^ (-p),
    (χ.val.continuous.pow _).mul ((f.val.continuous.add continuous_const).rpow_const
      (fun x ↦ Or.inl (add_pos_of_nonneg_of_pos (hf₀ x) hε).ne'))⟩
  let a : C(CarpetPoints, ℝ) := (1 - p) • W
  let b : C(CarpetPoints, ℝ) := ⟨fun x ↦ (m : ℝ) * (χ.val x) ^ (m - 1) * (f.val x + ε) ^ (1 - p),
    (continuous_const.mul (χ.val.continuous.pow _)).mul
      ((f.val.continuous.add continuous_const).rpow_const
        (fun x ↦ Or.inl (add_pos_of_nonneg_of_pos (hf₀ x) hε).ne'))⟩
  have hd (x : CarpetPoints) : fderiv ℝ φ (F x) =
      a x • P₀ + b x • P₁ := by
    let y := F x
    have hy : 0 ≤ y 0 := hf₀ x
    have hpow := (Real.hasDerivAt_rpow_const (p := 1 - p) (Or.inl (hSp (y 0)).ne')).comp
      (y 0) (hSid (y 0) hy).2
    have hdiff := hpow.comp_hasFDerivAt y P₀.hasFDerivAt
    have hφd := (P₁.hasFDerivAt (x := y)).pow m |>.mul hdiff
    change HasFDerivAt φ _ y at hφd
    rw [hφd.fderiv]
    have hshift := (hSid (y 0) hy).1
    have hpowexp : 1 - p - 1 = -p := by ring
    simp only [hshift, hpowexp, mul_one, nsmul_eq_mul, smul_smul]
    change ((F x 1) ^ m * ((1 - p) * (F x 0 + ε) ^ (-p))) • P₀ +
      (S (F x 0) ^ (1 - p) * ((m : ℝ) * (F x 1) ^ (m - 1))) • P₁ =
      (((1 - p) * ((χ.val x) ^ m * (f.val x + ε) ^ (-p))) • P₀) +
        (((m : ℝ) * (χ.val x) ^ (m - 1) * (f.val x + ε) ^ (1 - p)) • P₁)
    rw [(hSid (F x 0) hy).1, hF₀, hF₁, mul_left_comm ((χ.val x) ^ m),
      mul_comm ((f.val x + ε) ^ (1 - p))]
  have ha (x : CarpetPoints) : fderiv ℝ φ (F x) (Pi.single 0 1) = a x := by
    rw [hd]
    change a x * (Pi.single 0 1 : Fin 2 → ℝ) 0 +
      b x * (Pi.single 0 1 : Fin 2 → ℝ) 1 = a x
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, mul_zero, add_zero]
  have hb (x : CarpetPoints) : fderiv ℝ φ (F x) (Pi.single 1 1) = b x := by
    rw [hd]
    change a x * (Pi.single 1 1 : Fin 2 → ℝ) 0 +
      b x * (Pi.single 1 1 : Fin 2 → ℝ) 1 = b x
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_one, mul_zero, zero_add]
  let d := E.continuousCoreToDomain f
  let dχ := E.continuousCoreToDomain χ
  let μ := E.energyMeasure d
  let I := ∫ x, W x ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun x ↦
    mul_nonneg (pow_nonneg (hχ x).1 _) (Real.rpow_nonneg (add_nonneg (hf₀ x) hε.le) _))
  have hvv := E.abs_variation_two_coordinate_sub_integral_le h hc H φ hφ v hv a b ha hb
  change |E.variation h d (E.continuousCoreToDomain v) - ∫ x, a x ∂μ| ≤
    (∫ x, |b x| ^ q ∂μ) ^ q⁻¹ * (E.energy dχ : ℝ) ^ p⁻¹ at hvv
  have hA : (∫ x, a x ∂μ) = (1 - p) * I := integral_const_mul _ _
  have habs : |(∫ x, a x ∂μ)| = (p - 1) * I := by
    rw [hA, abs_mul, abs_of_neg (sub_neg.mpr E.one_lt_p), neg_sub, abs_of_nonneg hI]
  have htriangle : (p - 1) * I ≤
      |E.variation h d (E.continuousCoreToDomain v) - ∫ x, a x ∂μ| +
        |E.variation h d (E.continuousCoreToDomain v)| := by
    rw [← habs, abs_sub_comm]
    simpa only [sub_add_cancel] using abs_add_le
      ((∫ x, a x ∂μ) - E.variation h d (E.continuousCoreToDomain v))
      (E.variation h d (E.continuousCoreToDomain v))
  have hbound (i : Fin 2) (A : ℝ) (hA : 0 ≤ A)
      (hD : ∀ x, |fderiv ℝ φ (F x) (Pi.single i 1)| ≤ A) :
      (∫ x, |fderiv ℝ φ (F x) (Pi.single i 1)| ^ p
        ∂E.energyMeasure (E.continuousCoreToDomain (H i))) ^ p⁻¹ ≤
        A * E.rootSeminorm (E.continuousCoreToDomain (H i)) := by
    let g := E.continuousCoreToDomain (H i)
    have hcont : Continuous (fun x ↦ fderiv ℝ φ (F x) (Pi.single i 1)) :=
      ((hφ.continuous_fderiv (by norm_num)).comp F.continuous).clm_apply continuous_const
    have hi : Integrable (fun x ↦ |fderiv ℝ φ (F x) (Pi.single i 1)| ^ p) (E.energyMeasure g) :=
      (hcont.abs.rpow_const (fun _ ↦ Or.inr hpq.nonneg)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hle := integral_mono hi (integrable_const (A ^ p))
      (fun x ↦ Real.rpow_le_rpow (abs_nonneg _) (hD x) hpq.nonneg)
    rw [integral_const, smul_eq_mul, measureReal_def, E.energyMeasure_univ,
      ENNReal.coe_toReal, mul_comm] at hle
    have hpow := Real.rpow_le_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
      hle (inv_nonneg.mpr hpq.nonneg)
    rwa [Real.mul_rpow (Real.rpow_nonneg hA _) (NNReal.coe_nonneg _),
      Real.rpow_rpow_inv hA hpq.ne_zero, ← E.rootSeminorm_apply] at hpow
  have h₀ (x : CarpetPoints) : |a x| ≤ (p - 1) * ε ^ (-p) := by
    change |(1 - p) * ((χ.val x) ^ m * (f.val x + ε) ^ (-p))| ≤ _
    rw [abs_mul, abs_of_neg (sub_neg.mpr E.one_lt_p), neg_sub,
      abs_of_nonneg (mul_nonneg (pow_nonneg (hχ x).1 _) (Real.rpow_nonneg (add_nonneg (hf₀ x) hε.le) _))]
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr E.one_lt_p.le)
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (hχ x).1 (hχ x).2)
      (Real.rpow_nonneg (add_nonneg (hf₀ x) hε.le) _)).trans
        (by
          rw [one_mul]
          exact Real.rpow_le_rpow_of_nonpos hε (le_add_of_nonneg_left (hf₀ x))
            (neg_nonpos.mpr hpq.nonneg))
  have h₁ (x : CarpetPoints) : |b x| ≤ (m : ℝ) * ε ^ (1 - p) := by
    change |(m : ℝ) * (χ.val x) ^ (m - 1) * (f.val x + ε) ^ (1 - p)| ≤ _
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hχ x).1 _))
      (Real.rpow_nonneg (add_nonneg (hf₀ x) hε.le) _)), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (hχ x).1 (hχ x).2)
      (Real.rpow_nonneg (add_nonneg (hf₀ x) hε.le) _)).trans
        (by
          rw [one_mul]
          exact Real.rpow_le_rpow_of_nonpos hε (le_add_of_nonneg_left (hf₀ x))
            (sub_nonpos.mpr E.one_lt_p.le))
  have hroot := E.rootSeminorm_smooth_comp_le h hc H φ hφ v hv
  rw [Fin.sum_univ_two] at hroot
  refine ⟨v, hv₀, hroot.trans (add_le_add
    (hbound 0 _ (mul_nonneg (sub_nonneg.mpr E.one_lt_p.le) (Real.rpow_nonneg hε.le _))
      (fun x ↦ by rw [ha]; exact h₀ x))
    (hbound 1 _ (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hε.le _))
      (fun x ↦ by rw [hb]; exact h₁ x))), ?_⟩
  have hJ (x : CarpetPoints) : |b x| ^ q ≤ (m : ℝ) ^ q * W x := by
    let u := f.val x + ε
    have hu : 0 < u := add_pos_of_nonneg_of_pos (hf₀ x) hε
    have hx := hχ x
    have hq := hpq.symm.pos
    have hmq : (m : ℝ) ≤ (m - 1 : ℕ) * q := by
      have hm₁ : (1 : ℕ) ≤ m := Nat.one_le_iff_ne_zero.mpr hm₀
      rw [Nat.cast_sub hm₁, Nat.cast_one]
      dsimp only [q, Real.conjExponent]
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (sub_pos.mpr E.one_lt_p)).mpr
      nlinarith only [hm]
    have hpq' : (1 - p) * q = -p := by
      dsimp only [q, Real.conjExponent]
      field_simp [ne_of_gt (sub_pos.mpr E.one_lt_p)]
      ring
    change |(m : ℝ) * (χ.val x) ^ (m - 1) * u ^ (1 - p)| ^ q ≤
      (m : ℝ) ^ q * ((χ.val x) ^ m * u ^ (-p))
    have hχm : 0 ≤ (m : ℝ) * (χ.val x) ^ (m - 1) := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _)
    rw [abs_of_nonneg (mul_nonneg hχm (Real.rpow_nonneg hu.le _)),
      Real.mul_rpow hχm (Real.rpow_nonneg hu.le _),
      Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hx.1 _),
      ← Real.rpow_natCast_mul hx.1, ← Real.rpow_mul hu.le, hpq',
      mul_assoc, ← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge' hx.1 hx.2 (Nat.cast_nonneg _) hmq)
      (Real.rpow_nonneg hu.le _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hJint : Integrable (fun x ↦ |b x| ^ q) μ :=
    (b.continuous.abs.rpow_const (fun _ ↦ Or.inr hpq.symm.nonneg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hW : Integrable W μ := W.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJle := integral_mono hJint (hW.const_mul ((m : ℝ) ^ q)) hJ
  rw [integral_const_mul] at hJle
  have hJbound := Real.rpow_le_rpow (integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _))
    hJle (inv_nonneg.mpr hpq.symm.nonneg)
  change _ ≤ ((m : ℝ) ^ q * I) ^ q⁻¹ at hJbound
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hI,
    Real.rpow_rpow_inv (Nat.cast_nonneg _) hpq.symm.ne_zero] at hJbound
  have hfinal := hvv.trans (mul_le_mul_of_nonneg_right hJbound (Real.rpow_nonneg (NNReal.coe_nonneg _) _))
  rw [mul_assoc] at hfinal
  exact htriangle.trans (add_le_add hfinal le_rfl)

/-- Weighted logarithmic energy estimate for nonnegative continuous harmonic profiles. -/
theorem integral_log_weight_le_of_harmonicOn
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {U : Set CarpetPoints} (f χ : E.continuousCore) (hf : E.IsHarmonicOn U f)
    (hf₀ : ∀ x, 0 ≤ f.val x) (hχ : ∀ x, χ.val x ∈ Icc (0 : ℝ) 1)
    (hχ₀ : ∀ x ∉ U, χ.val x = 0) {ε : ℝ} (hε : 0 < ε)
    (m : ℕ) (hm : p ≤ (m : ℝ)) :
    (∫ x, (χ.val x) ^ m * (f.val x + ε) ^ (-p)
        ∂E.energyMeasure (E.continuousCoreToDomain f)) ≤
      ((m : ℝ) / (p - 1)) ^ p * (E.energy (E.continuousCoreToDomain χ) : ℝ) := by
  obtain ⟨v, hv, _, htest⟩ := E.exists_logarithmic_test h hc f χ hf₀ hχ hχ₀ hε m hm
  rw [E.variation_eq_zero_of_harmonicOn h hf v hv, abs_zero, add_zero] at htest
  exact log_budget_of_holder (Real.HolderConjugate.conjExponent E.one_lt_p)
    (integral_nonneg fun x ↦ mul_nonneg (pow_nonneg (hχ x).1 _)
      (Real.rpow_nonneg (add_nonneg (hf₀ x) hε.le) _))
    (NNReal.coe_nonneg _) (Nat.cast_nonneg _) htest

end CarpetEnergy.SelfSimilarPEnergy
