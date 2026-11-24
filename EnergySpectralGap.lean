import BoundedEnergyOscillation
import DyadicEnergyTruncation
import MeasureMedian

/-!
# The spectral gap for self-similar p-energies

The dyadic selection and cell blowup give a bounded competitor with
separated plateaus. Proposition 3.6 bounds its energy away from zero.
Applying this to the two parts about a median yields the spectral gap.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem norm_centered_lower_bound_of_level [Fact (1 ≤ ENNReal.ofReal p)]
    (f : C(CarpetPoints, ℝ)) (a : ℝ) :
    (carpetMeasure {x | f x = a}).toReal * |a - ∫ x, f x ∂carpetMeasure| ≤
      ‖continuousLp p (centeredContinuous f)‖ := by
  let A : Set CarpetPoints := {x | f x = a}
  let c := ∫ x, f x ∂carpetMeasure
  have hA : MeasurableSet A := measurableSet_eq_fun f.continuous.measurable measurable_const
  have h : ((continuousLp p (centeredContinuous f)) : CarpetPoints → ℝ) =ᵐ[carpetMeasure.restrict A]
      fun _ ↦ a - c := by
    have hae : (continuousLp p (centeredContinuous f) : CarpetPoints → ℝ) =ᵐ[carpetMeasure.restrict A]
        centeredContinuous f := ae_restrict_of_ae (continuousLp_ae_eq p _)
    refine hae.trans ((ae_restrict_mem hA).mono fun x hx ↦ ?_)
    change f x - c = a - c
    rw [show f x = a from hx]
  have ht := norm_setIntegral_le A (continuousLp p (centeredContinuous f))
  rw [integral_congr_ae h, integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] at ht
  exact ht

private theorem energy_lower_bound_of_two_plateaus (δ : ℝ≥0) (hδ : 0 < δ) (hδ' : (δ : ℝ≥0∞) ≤ 2⁻¹) :
    ∃ η > (0 : ℝ), ∀ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain),
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (δ : ℝ≥0∞) ≤ carpetMeasure {x | f x = 1} →
      carpetMeasure {x | 0 < f x} ≤ 2⁻¹ →
      η ≤ (E.energy ⟨continuousLp p f, hf⟩ : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hε : 0 < (δ : ℝ) / 2 := by positivity
  obtain ⟨η, hη, hηosc⟩ := E.exists_energy_bound_for_bounded_oscillation hε
  refine ⟨η, hη, ?_⟩
  intro f hf hb h1 hp
  by_contra! hE
  have hosc := hηosc f hf hb hE
  let c := ∫ x, f x ∂carpetMeasure
  suffices hlower : (δ : ℝ) / 2 ≤ ‖continuousLp p (centeredContinuous f)‖ from hosc.not_ge hlower
  by_cases hc : c ≤ 1 / 2
  · have hr : (δ : ℝ) ≤ (carpetMeasure {x | f x = 1}).toReal := by
      simpa only [ENNReal.coe_toReal] using ENNReal.toReal_mono (measure_ne_top _ _) h1
    calc
      _ = (δ : ℝ) * (1 / 2) := by ring
      _ ≤ (carpetMeasure {x | f x = 1}).toReal * |1 - c| :=
        mul_le_mul hr (le_abs.mpr (Or.inl (by linarith))) (by norm_num) ENNReal.toReal_nonneg
      _ ≤ _ := norm_centered_lower_bound_of_level f 1
  · have hcomp : {x | f x = 0} = {x | 0 < f x}ᶜ := by
      ext x
      change f x = 0 ↔ ¬ 0 < f x
      exact ⟨fun h ↦ by rw [h]; exact lt_irrefl 0, fun h ↦ (not_lt.mp h).antisymm (hb x).1⟩
    have hr' : (δ : ℝ≥0∞) ≤ carpetMeasure {x | f x = 0} := by
      rw [hcomp, measure_compl (measurableSet_lt measurable_const f.continuous.measurable)
        (measure_ne_top _ _), measure_univ]
      exact hδ'.trans ((by norm_num : (2 : ℝ≥0∞)⁻¹ ≤ 1 - 2⁻¹).trans (tsub_le_tsub_left hp 1))
    have hr : (δ : ℝ) ≤ (carpetMeasure {x | f x = 0}).toReal := by
      simpa only [ENNReal.coe_toReal] using ENNReal.toReal_mono (measure_ne_top _ _) hr'
    calc
      _ = (δ : ℝ) * (1 / 2) := by ring
      _ ≤ (carpetMeasure {x | f x = 0}).toReal * |0 - c| :=
        mul_le_mul hr (le_abs.mpr (Or.inr (by linarith))) (by norm_num) ENNReal.toReal_nonneg
      _ ≤ _ := norm_centered_lower_bound_of_level f 0

private theorem continuousLp_comp_wordMap_eq (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) (w : List (Fin 8)) :
    continuousLp p (u.comp ⟨wordMap w, continuous_wordMap w⟩) =
      ((E.pullbackWord w ⟨continuousLp p u, hu⟩) : CarpetLp p) := by
  apply Lp.ext
  have h := (quasiMeasurePreserving_wordMap w).ae_eq_comp (continuousLp_ae_eq p u)
  exact (continuousLp_ae_eq p _).trans ((E.pullbackWord_isLpPullback w _).trans h).symm

private theorem choose_small_plateau_threshold (C : ℝ≥0) (hC : 1 ≤ C) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ < 1 ∧ (δ : ℝ≥0∞) ≤ 2⁻¹ ∧
      32 * (C : ℝ≥0∞) * (δ : ℝ≥0∞) ≤ 2⁻¹ := by
  let δ : ℝ≥0 := (64 * C)⁻¹
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  have h64 : (0 : ℝ≥0) < 64 * C := by positivity
  have hδ : 0 < δ := inv_pos.mpr h64
  have hδle : δ ≤ 2⁻¹ := by
    apply (inv_le_inv₀ h64 (by norm_num : (0 : ℝ≥0) < 2)).mpr
    have hc : (64 : ℝ≥0) ≤ 64 * C := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hC (show (0 : ℝ≥0) ≤ 64 by positivity)
    exact (by norm_num : (2 : ℝ≥0) ≤ 64).trans hc
  have hprod : (32 : ℝ≥0) * C * δ = 2⁻¹ := by
    rw [show (32 : ℝ≥0) * C = (2 : ℝ≥0)⁻¹ * (64 * C) by ring, mul_assoc]
    change (2 : ℝ≥0)⁻¹ * ((64 * C) * (64 * C)⁻¹) = _
    rw [mul_inv_cancel₀ h64.ne', mul_one]
  refine ⟨δ, hδ, hδle.trans_lt (by norm_num), ?_, ?_⟩
  · rw [← ENNReal.coe_inv_two]
    exact ENNReal.coe_le_coe.mpr hδle
  · rw [← ENNReal.coe_inv_two]
    exact_mod_cast hprod.le

private theorem exists_energy_bound_of_small_positive_set :
    ∃ C > (0 : ℝ), ∀ (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain),
      (∀ x, 0 ≤ u x) → carpetMeasure {x | 0 < u x} ≤ 2⁻¹ →
      ‖continuousLp p u‖ ^ p ≤ C * (E.energy ⟨continuousLp p u, hu⟩ : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨C₁, C₂, h₁, h₂, hselect⟩ := exists_dyadic_truncation E.one_lt_p
  obtain ⟨δ, hδ, hδ₁, hδhalf, hδC⟩ := choose_small_plateau_threshold C₁ h₁.le
  obtain ⟨η, hη, heta⟩ := E.energy_lower_bound_of_two_plateaus δ hδ hδhalf
  have hC₂ : 0 < (C₂ : ℝ) := by exact_mod_cast zero_lt_one.trans h₂
  refine ⟨32 * (C₂ : ℝ) / η, by positivity, ?_⟩
  intro u hu hu₀ hupos
  let Eu := (E.energy ⟨continuousLp p u, hu⟩ : ℝ)
  let J := ‖continuousLp p u‖ ^ p
  have hJ₀ : 0 ≤ J := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hzero : u = 0
  · have hz : continuousLp p u = 0 := by
      subst u
      apply Lp.ext
      exact (continuousLp_ae_eq p (0 : C(CarpetPoints, ℝ))).trans (Lp.coeFn_zero ..).symm
    change ‖continuousLp p u‖ ^ p ≤ 32 * (C₂ : ℝ) / η * Eu
    rw [hz, norm_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt_p).ne']
    positivity
  obtain ⟨g, hg, hgb, hsub, hplateau, _, hsupport, hE⟩ :=
    hselect E u hu hzero hu₀
  let q := carpetMeasure {x | g x = 1}
  let Eg := (E.energy ⟨continuousLp p g, hg⟩ : ℝ)
  have hq : 0 < q.toReal := ENNReal.toReal_pos hplateau.ne' (measure_ne_top _ _)
  have hq₁ : q.toReal ≤ 1 := by
    simp only [← ENNReal.toReal_one]
    apply ENNReal.toReal_mono ENNReal.one_ne_top
    simpa only [measure_univ] using (measure_mono (subset_univ {x | g x = 1}) :
      q ≤ carpetMeasure univ)
  have hEreal : J * Eg ≤ (C₂ : ℝ) * Eu * q.toReal := by
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
        (measure_ne_top carpetMeasure {x | g x = 1})) hE
    have hJreal : (ENNReal.ofReal (‖continuousLp p u‖ ^ p)).toReal = J :=
      ENNReal.toReal_ofReal hJ₀
    simpa only [ENNReal.toReal_mul, hJreal, ENNReal.coe_toReal] using hh
  suffices h : η * J ≤ 32 * (C₂ : ℝ) * Eu by
    change J ≤ 32 * (C₂ : ℝ) / η * Eu
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hη).mpr
    rwa [mul_comm J η]
  by_cases hqδ : (δ : ℝ≥0∞) ≤ q
  · have hηg := heta g hg hgb hqδ ((measure_mono hsub).trans hupos)
    calc
      η * J ≤ J * Eg := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hηg hJ₀
      _ ≤ (C₂ : ℝ) * Eu * q.toReal := hEreal
      _ ≤ (C₂ : ℝ) * Eu := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hq₁ (by positivity : 0 ≤ (C₂ : ℝ) * Eu)
      _ ≤ 32 * (C₂ : ℝ) * Eu := by
        rw [mul_assoc]
        exact le_mul_of_one_le_left (by positivity) (by norm_num)
  · obtain ⟨n, w, hδw, hsupportw, hEw⟩ := E.exists_word_of_small_plateau g hg hδ₁ h₁.le
      hplateau.ne' (lt_of_not_ge hqδ) hsupport
    let F := wordMap (List.ofFn w)
    let f : C(CarpetPoints, ℝ) := g.comp ⟨F, continuous_wordMap _⟩
    let fg := E.pullbackWord (List.ofFn w) ⟨continuousLp p g, hg⟩
    have hf_eq : continuousLp p f = (fg : CarpetLp p) := E.continuousLp_comp_wordMap_eq g hg _
    have hf : continuousLp p f ∈ E.domain := hf_eq.symm ▸ fg.property
    have hf' : (⟨continuousLp p f, hf⟩ : E.domain) = fg := Subtype.ext hf_eq
    have hηf : η ≤ (E.energy fg : ℝ) := by
      rw [← hf']
      exact heta f hf (fun x ↦ hgb (F x)) hδw (hsupportw.trans hδC)
    have hEw_real : q.toReal * (E.energy fg : ℝ) ≤ 32 * (δ : ℝ) * Eg := by
      have h := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) ENNReal.coe_ne_top)
        hEw
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] using h
    have hδn : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ₁.le
    apply (mul_le_mul_iff_right₀ hq).mp
    calc
      q.toReal * (η * J) ≤ q.toReal * ((E.energy fg : ℝ) * J) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hηf hJ₀) hq.le
      _ = (q.toReal * (E.energy fg : ℝ)) * J := by ring
      _ ≤ (32 * (δ : ℝ) * Eg) * J := mul_le_mul_of_nonneg_right hEw_real hJ₀
      _ = (32 * (δ : ℝ)) * (J * Eg) := by ring
      _ ≤ (32 * (δ : ℝ)) * ((C₂ : ℝ) * Eu * q.toReal) :=
        mul_le_mul_of_nonneg_left hEreal (by positivity)
      _ ≤ 32 * ((C₂ : ℝ) * Eu * q.toReal) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by norm_num) hδn) (by positivity)
      _ = q.toReal * (32 * (C₂ : ℝ) * Eu) := by ring

/-- Subtraction of the probability mean as a continuous linear operator on Lp. -/
noncomputable def centerLp (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    CarpetLp p →L[ℝ] CarpetLp p :=
  ContinuousLinearMap.id ℝ _ -
    (Lp.constL (ENNReal.ofReal p) carpetMeasure ℝ).comp (lpSetIntegral univ)

theorem centerLp_apply [Fact (1 ≤ ENNReal.ofReal p)] (f : CarpetLp p) :
    centerLp p f = f - constantLp p (∫ x, f x ∂carpetMeasure) := by
  change f - constantLp p (∫ x in univ, f x ∂carpetMeasure) = _
  rw [Measure.restrict_univ]

private theorem centerLp_constant [Fact (1 ≤ ENNReal.ofReal p)] (a : ℝ) :
    centerLp p (constantLp p a) = 0 := by
  rw [centerLp_apply]
  unfold constantLp
  rw [integral_congr_ae (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a)]
  simp [Measure.real]

private theorem norm_centerLp_le [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (f : CarpetLp p) :
    ‖centerLp p f‖ ≤ 2 * ‖f‖ := by
  rw [centerLp_apply, two_mul]
  apply (norm_sub_le _ _).trans
  apply add_le_add_right
  have h := norm_setIntegral_le univ f
  rw [Measure.restrict_univ] at h
  unfold constantLp
  rw [Lp.norm_const _ _ _ (ENNReal.ofReal_ne_zero_iff.mpr hp)]
  simpa [Measure.real] using h

private theorem exists_spectral_gap_continuous [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C > (0 : ℝ), ∀ (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain),
      ‖centerLp p (continuousLp p u)‖ ^ p ≤ C * (E.energy ⟨continuousLp p u, hu⟩ : ℝ) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨C, hC, hselect⟩ := E.exists_energy_bound_of_small_positive_set
  refine ⟨4 ^ p * C, by positivity, ?_⟩
  intro f hf
  obtain ⟨m, hm₀, hm₁⟩ := exists_median_of_bounded carpetMeasure f f.continuous.measurable
    (ContinuousMap.neg_norm_le_apply f) (ContinuousMap.apply_le_norm f)
  obtain ⟨u, hu, huf, hue⟩ := E.exists_continuous_comp_energy_le_mul f hf (lipschitzWith_sub_part m)
  obtain ⟨v, hv, hvf, hve⟩ := E.exists_continuous_comp_energy_le_mul f hf (lipschitzWith_reverse_sub_part m)
  simp only [NNReal.coe_one, Real.one_rpow, one_mul] at hue hve
  let e := (E.energy ⟨continuousLp p f, hf⟩ : ℝ)
  have he : 0 ≤ C * e := by positivity
  have hU : ‖continuousLp p u‖ ^ p ≤ C * e := by
    apply (hselect u hu (fun x ↦ (huf x).symm ▸ le_max_right _ _) ?_).trans
      (mul_le_mul_of_nonneg_left hue hC.le)
    have hs : {x | 0 < u x} ⊆ {x | m < f x} := by
      intro x hx
      change 0 < u x at hx
      rw [huf, lt_max_iff, sub_pos] at hx
      exact hx.resolve_right (lt_irrefl 0)
    exact (measure_mono hs).trans hm₁
  have hV : ‖continuousLp p v‖ ^ p ≤ C * e := by
    apply (hselect v hv (fun x ↦ (hvf x).symm ▸ le_max_right _ _) ?_).trans
      (mul_le_mul_of_nonneg_left hve hC.le)
    have hs : {x | 0 < v x} ⊆ {x | f x < m} := by
      intro x hx
      change 0 < v x at hx
      rw [hvf, lt_max_iff, sub_pos] at hx
      exact hx.resolve_right (lt_irrefl 0)
    exact (measure_mono hs).trans hm₀
  let w := continuousLp p f - constantLp p m
  have hw : w = continuousLp p u - continuousLp p v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (continuousLp p f) (constantLp p m),
      Lp.coeFn_sub (continuousLp p u) (continuousLp p v), continuousLp_ae_eq p f,
      continuousLp_ae_eq p u, continuousLp_ae_eq p v,
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure m] with x hl hr hf' hu' hv' hm
    change (constantLp p m) x = m at hm
    rw [hl, hr, Pi.sub_apply, Pi.sub_apply, hf', hu', hv', hm, huf, hvf]
    by_cases hh : m ≤ f x
    · rw [max_eq_left (sub_nonneg.mpr hh), max_eq_right (sub_nonpos.mpr hh), sub_zero]
    · have hh' := (lt_of_not_ge hh).le
      rw [max_eq_right (sub_nonpos.mpr hh'), max_eq_left (sub_nonneg.mpr hh')]
      ring
  have hc : centerLp p (continuousLp p f) = centerLp p w := by
    unfold w
    rw [map_sub, centerLp_constant, sub_zero]
  have hn (g : C(CarpetPoints, ℝ)) (h : ‖continuousLp p g‖ ^ p ≤ C * e) :
      ‖continuousLp p g‖ ≤ (C * e) ^ p⁻¹ := by
    rw [← Real.rpow_rpow_inv (norm_nonneg (continuousLp p g)) hp.ne']
    exact Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) h (inv_nonneg.mpr hp.le)
  have hsum : ‖centerLp p (continuousLp p f)‖ ≤ 4 * (C * e) ^ p⁻¹ := by
    rw [hc]
    calc
      _ ≤ 2 * ‖w‖ := norm_centerLp_le hp w
      _ ≤ 2 * (‖continuousLp p u‖ + ‖continuousLp p v‖) := by
        rw [hw]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
      _ ≤ 2 * ((C * e) ^ p⁻¹ + (C * e) ^ p⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add (hn u hU) (hn v hV)) (by norm_num)
      _ = _ := by ring
  calc
    ‖centerLp p (continuousLp p f)‖ ^ p ≤ (4 * (C * e) ^ p⁻¹) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) hsum hp.le
    _ = 4 ^ p * C * e := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg he _), Real.rpow_inv_rpow he hp.ne', mul_assoc]

/-- Proposition 2.2, the spectral gap for every self-similar p-energy. -/
theorem exists_spectral_gap :
    ∃ C > (0 : ℝ), ∀ f : E.domain,
      ‖(f : CarpetLp p) - constantLp p (∫ x, (f : CarpetLp p) x ∂carpetMeasure)‖ ^ p ≤
        C * (E.energy f : ℝ) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨C, hC, hgap⟩ := E.exists_spectral_gap_continuous
  refine ⟨C, hC, fun f ↦ ?_⟩
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose u hu happrox using fun n ↦ E.regular_graph f (ε n) (hε n)
  let g (n : ℕ) : E.domain := ⟨continuousLp p (u n), hu n⟩
  have hnorm (n : ℕ) : ‖(g n : CarpetLp p) - (f : CarpetLp p)‖ ≤ ε n :=
    (E.norm_coe_le_graphSeminorm (g n - f)).trans (happrox n).le
  have ht : Tendsto (fun n ↦ (g n : CarpetLp p)) atTop (𝓝 (f : CarpetLp p)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεlim
        (fun _ ↦ norm_nonneg _) hnorm)
  have hroot (n : ℕ) : E.rootSeminorm (g n) ≤ E.rootSeminorm f + ε n := by
    calc
      _ = E.rootSeminorm ((g n - f) + f) := by rw [sub_add_cancel]
      _ ≤ E.rootSeminorm (g n - f) + E.rootSeminorm f := map_add_le_add _ _ _
      _ ≤ _ := by
        rw [add_comm (E.rootSeminorm f)]
        exact add_le_add_left ((E.rootSeminorm_le_graphSeminorm _).trans (happrox n).le) _
  have heq (z : E.domain) : (E.rootSeminorm z) ^ p = (E.energy z : ℝ) := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg (E.energy z)) hp.ne'
  have hE (n : ℕ) : (E.energy (g n) : ℝ) ≤ (E.rootSeminorm f + ε n) ^ p := by
    rw [← heq]
    exact Real.rpow_le_rpow (apply_nonneg _ _) (hroot n) hp.le
  have hl := (((centerLp p).continuous.tendsto _).comp ht).norm.rpow_const
    (p := p) (Or.inr hp.le)
  have hr : Tendsto (fun n ↦ C * (E.rootSeminorm f + ε n) ^ p) atTop
      (𝓝 (C * (E.energy f : ℝ))) := by
    have hr₀ : Tendsto (fun n ↦ E.rootSeminorm f + ε n) atTop
        (𝓝 (E.rootSeminorm f + 0)) := tendsto_const_nhds.add hεlim
    have hrp := hr₀.rpow_const (p := p) (Or.inr hp.le)
    simpa only [add_zero, heq] using hrp.const_mul C
  rw [← centerLp_apply]
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n ↦
    (hgap (u n) (hu n)).trans (mul_le_mul_of_nonneg_left (hE n) hC.le))

end CarpetEnergy.SelfSimilarPEnergy
