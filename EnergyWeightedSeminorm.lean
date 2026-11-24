import EnergyDensities

/-!
# Weighted setwise energy seminorms

The root of the weighted mass is an Lp norm of the root density. This
gives the weighted seminorm estimate in (7.6) and the dense-domain
extension in Proposition 7.5.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem withDensity_le_smul_of_bound (ν : Measure CarpetPoints)
    {w : CarpetPoints → ℝ≥0∞} {C : ℝ≥0} (hw : ∀ x, w x ≤ C) :
    ν.withDensity w ≤ (C : ℝ≥0∞) • ν := by
  rw [← withDensity_const]
  exact withDensity_mono (Eventually.of_forall hw)

private theorem eLpNorm_energyDensityRoot (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    {w : CarpetPoints → ℝ≥0∞} (hw : Measurable w)
    {A : Set CarpetPoints} (hA : MeasurableSet A) (f : E.domain)
    (hdom : E.energyMeasure f ≪ μ) :
    eLpNorm (E.energyDensityRoot μ f) (ENNReal.ofReal p) ((μ.withDensity w).restrict A) =
      (((E.energyMeasure f).withDensity w) A) ^ p⁻¹ := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let r := (E.energyMeasure f).rnDeriv μ
  have hr : Measurable r := Measure.measurable_rnDeriv _ _
  have hdec : (E.energyMeasure f).HaveLebesgueDecomposition μ :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  let ν := (μ.withDensity w).restrict A
  have hac : ν ≪ μ := (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
    (withDensity_absolutelyContinuous μ w)
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top (E.measurable_energyDensityRoot μ f).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, one_div]
  apply congrArg (fun t : ℝ≥0∞ ↦ t ^ p⁻¹)
  calc
    _ = ∫⁻ x, r x ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hac ((E.energyMeasure f).rnDeriv_ne_top μ)] with x hx
      have hnonneg := E.energyDensityRoot_nonneg μ f x
      calc
        _ = ENNReal.ofReal (E.energyDensityRoot μ f x) ^ p :=
          congrArg (· ^ p) (Real.eNorm_eq_ofReal hnonneg)
        _ = ENNReal.ofReal (E.energyDensityRoot μ f x ^ p) :=
          ENNReal.ofReal_rpow_of_nonneg hnonneg hp.le
        _ = _ := E.ofReal_energyDensityRoot_pow μ f hx
    _ = ∫⁻ x in A, (w * r) x ∂μ := setLIntegral_withDensity_eq_setLIntegral_mul μ hw hr hA
    _ = ((E.energyMeasure f).withDensity w) A := by
      rw [← Measure.withDensity_rnDeriv_eq _ _ hdom, ← withDensity_mul μ hr hw, withDensity_apply _ hA]
      simp only [mul_comm w r]

/-- The p-th root of the mass weighted by a bounded Borel density is a
seminorm dominated by the corresponding multiple of the energy root. -/
theorem exists_energyMeasure_withDensity_seminorm
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (hdom : ∀ f, E.energyMeasure f ≪ μ)
    {w : CarpetPoints → ℝ≥0∞} (hw : Measurable w) {C : ℝ≥0} (hC : ∀ x, w x ≤ C)
    {A : Set CarpetPoints} (hA : MeasurableSet A) :
    ∃ S : Seminorm ℝ E.domain, ∀ f : E.domain,
      S f = (((E.energyMeasure f).withDensity w).real A) ^ p⁻¹ ∧
      S f ≤ (C : ℝ) ^ p⁻¹ * E.rootSeminorm f := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let ν := (μ.withDensity w).restrict A
  have hac : ν ≪ μ := (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
    (withDensity_absolutelyContinuous μ w)
  let mass (f : E.domain) := ((E.energyMeasure f).withDensity w) A
  let s (f : E.domain) := (mass f).toReal ^ p⁻¹
  have hmass (f : E.domain) : mass f ≤ (C : ℝ≥0∞) * E.energyMeasure f A :=
    withDensity_le_smul_of_bound (E.energyMeasure f) hC A
  have hfin (f : E.domain) : mass f ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)) (hmass f)
  let q (f : E.domain) := eLpNorm (E.energyDensityRoot μ f) (ENNReal.ofReal p) ν
  have hq (f : E.domain) : q f = (mass f) ^ p⁻¹ :=
    E.eLpNorm_energyDensityRoot μ hw hA f (hdom f)
  have hqfin (f : E.domain) : q f ≠ ∞ := by
    rw [hq]
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) (hfin f)
  have hqreal (f : E.domain) : (q f).toReal = s f := by
    rw [hq, ← ENNReal.toReal_rpow]
  have hadd (f g : E.domain) : s (f + g) ≤ s f + s g := by
    have htri : q (f + g) ≤ q f + q g := calc
      _ ≤ eLpNorm (E.energyDensityRoot μ f + E.energyDensityRoot μ g) (ENNReal.ofReal p) ν := by
        apply eLpNorm_mono_ae_real (E.measurable_energyDensityRoot μ (f + g)).aestronglyMeasurable
        filter_upwards [hac (E.ae_energyDensityRoot_add_le μ hdom f g)] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (E.energyDensityRoot_nonneg μ (f + g) x)]
        exact hx
      _ ≤ _ := eLpNorm_add_le (ENNReal.one_le_ofReal.mpr E.one_lt_p.le)
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hqfin f, hqfin g⟩) htri
    rw [ENNReal.toReal_add (hqfin f) (hqfin g), hqreal, hqreal, hqreal] at h
    exact h
  have hsmul (c : ℝ) (f : E.domain) : s (c • f) = ‖c‖ * s f := by
    have h : mass (c • f) = ENNReal.ofReal (|c| ^ p) * mass f := by
      simp only [mass, E.energyMeasure_smul, withDensity_smul_measure, smul_apply, smul_eq_mul]
    change (mass (c • f)).toReal ^ p⁻¹ = _
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _),
      Real.norm_eq_abs]
    calc
      _ = (|c| ^ p) ^ p⁻¹ * (mass f).toReal ^ p⁻¹ :=
        Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) ENNReal.toReal_nonneg
      _ = _ := congrArg (· * (mass f).toReal ^ p⁻¹) (Real.rpow_rpow_inv (abs_nonneg _) hp.ne')
  let S := Seminorm.of s hadd hsmul
  refine ⟨S, fun f ↦ ⟨rfl, ?_⟩⟩
  change s f ≤ _
  have hmass' : mass f ≤ (C : ℝ≥0∞) * E.energyMeasure f univ :=
    (hmass f).trans (mul_le_mul' le_rfl (measure_mono (subset_univ _)))
  have hle := Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)) hmass')
    (inv_nonneg.mpr hp.le)
  apply hle.trans_eq
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, E.energyMeasure_univ, ENNReal.coe_toReal,
    E.rootSeminorm_apply]
  exact Real.mul_rpow C.coe_nonneg (E.energy f).property

private theorem tendsto_seminorm_of_rootSeminorm_sub_tendsto_zero
    (S : Seminorm ℝ E.domain) {c : ℝ} (hS : ∀ g, S g ≤ c * E.rootSeminorm g)
    (f : E.domain) (u : ℕ → E.domain)
    (hu : Tendsto (fun n ↦ E.rootSeminorm (f - u n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ S (u n)) atTop (𝓝 (S f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun n ↦ c * E.rootSeminorm (f - u n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hu.const_mul c
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  have h₁ := map_add_le_add S (u n - f) f
  rw [sub_add_cancel, ← neg_sub f (u n), map_neg_eq_map] at h₁
  have h₂ := map_add_le_add S (f - u n) (u n)
  rw [sub_add_cancel] at h₂
  apply le_trans _ (hS (f - u n))
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith only [h₂], by linarith only [h₁]⟩

/-- A bounded common density on a dense sequence gives the same density on the
whole energy domain, as in (7.6). -/
theorem energyMeasure_eq_withDensity_of_energyDense
    (D : SelfSimilarPEnergy p) (hED : E.domain ≤ D.domain)
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (d : ℕ → E.domain) (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0))
    {K : ℝ} (hcomp : ∀ f, D.rootSeminorm (Submodule.inclusion hED f) ≤ K * E.rootSeminorm f)
    {w : CarpetPoints → ℝ≥0∞} (hw : Measurable w) {C : ℝ≥0} (hC : ∀ x, w x ≤ C)
    (heq : ∀ n, D.energyMeasure (Submodule.inclusion hED (d n)) =
      (E.energyMeasure (d n)).withDensity w)
    (f : E.domain) :
    D.energyMeasure (Submodule.inclusion hED f) = (E.energyMeasure f).withDensity w := by
  apply Measure.ext
  intro A hA
  obtain ⟨S, hS⟩ := E.exists_energyMeasure_withDensity_seminorm μ hdom hw hC hA
  let T := (D.energyMeasureSeminorm A hA).comp (Submodule.inclusion hED)
  have hT (g : E.domain) : T g ≤ K * E.rootSeminorm g :=
    (D.energyMeasureSeminorm_le_rootSeminorm A hA _).trans (hcomp g)
  obtain ⟨j, hj⟩ := hdense f
  have hlimT := E.tendsto_seminorm_of_rootSeminorm_sub_tendsto_zero T hT f (fun n ↦ d (j n)) hj
  have hlimS := E.tendsto_seminorm_of_rootSeminorm_sub_tendsto_zero S
    (fun g ↦ (hS g).2) f (fun n ↦ d (j n)) hj
  have hTS (n : ℕ) : T (d n) = S (d n) := by
    change D.energyMeasureSeminorm A hA (Submodule.inclusion hED (d n)) = _
    rw [D.energyMeasureSeminorm_apply, heq n, (hS (d n)).1]
  have hlim : T f = S f :=
    tendsto_nhds_unique (by simpa only [hTS] using hlimT) hlimS
  change D.energyMeasureSeminorm A hA (Submodule.inclusion hED f) = S f at hlim
  rw [D.energyMeasureSeminorm_apply, (hS f).1, Measure.real, Measure.real] at hlim
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have ht := (Real.rpow_left_inj ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (inv_ne_zero hp.ne')).mp hlim
  have hfin : ((E.energyMeasure f).withDensity w) A ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top (E.energyMeasure f) A))
    exact withDensity_le_smul_of_bound (E.energyMeasure f) hC A
  calc
    _ = ENNReal.ofReal ((D.energyMeasure (Submodule.inclusion hED f)) A).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal (((E.energyMeasure f).withDensity w) A).toReal := congrArg ENNReal.ofReal ht
    _ = _ := ENNReal.ofReal_toReal hfin

/-- The weighted pointwise density ratios on an energy-dense sequence determine
a bounded common Borel density on the whole domain. -/
theorem exists_bounded_common_density_of_ae_proportional
    (D : SelfSimilarPEnergy p) (hED : E.domain ≤ D.domain)
    (C : ℝ≥0) (hC : 1 ≤ C)
    (hcomp : ∀ f : E.domain, D.energyMeasure (Submodule.inclusion hED f) ≤
      (C : ℝ≥0∞) • E.energyMeasure f)
    (d : ℕ → E.domain) (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0))
    (hpoint : ∀ᵐ x ∂E.energyReferenceMeasure d, ∃ c ∈ Icc ((C : ℝ)⁻¹) (C : ℝ),
      ∀ n,
        (D.energyMeasure (Submodule.inclusion hED (d n))).rnDeriv (E.energyReferenceMeasure d) x =
          ENNReal.ofReal c * (E.energyMeasure (d n)).rnDeriv (E.energyReferenceMeasure d) x) :
    ∃ a : CarpetPoints → ℝ, Measurable a ∧
      (∀ x, a x ∈ Icc ((C : ℝ)⁻¹) (C : ℝ)) ∧
      ∀ f : E.domain, D.energyMeasure (Submodule.inclusion hED f) =
        (E.energyMeasure f).withDensity (fun x ↦ ENNReal.ofReal (a x)) := by
  let μ := E.energyReferenceMeasure d
  have hdom (f : E.domain) : E.energyMeasure f ≪ μ :=
    E.energyMeasure_absolutelyContinuous_reference d hdense f
  let Γ₀ (n : ℕ) := E.energyMeasure (d n)
  let Γ (n : ℕ) := D.energyMeasure (Submodule.inclusion hED (d n))
  let r (n : ℕ) := (Γ₀ n).rnDeriv μ
  let t (n : ℕ) := (Γ n).rnDeriv μ
  have hr (n : ℕ) : Measurable (r n) := Measure.measurable_rnDeriv _ _
  have ht (n : ℕ) : Measurable (t n) := Measure.measurable_rnDeriv _ _
  have hΓ₀ (n : ℕ) : Γ₀ n = μ.withDensity (r n) := by
    have : (Γ₀ n).HaveLebesgueDecomposition μ :=
      Measure.haveLebesgueDecomposition_of_finiteMeasure
    exact (Measure.withDensity_rnDeriv_eq _ _ (hdom (d n))).symm
  have hΓ (n : ℕ) : Γ n = μ.withDensity (t n) := by
    have : (Γ n).HaveLebesgueDecomposition μ :=
      Measure.haveLebesgueDecomposition_of_finiteMeasure
    exact (Measure.withDensity_rnDeriv_eq _ _
      ((Measure.absolutelyContinuous_of_le_smul (hcomp (d n))).trans (hdom (d n)))).symm
  have hnonneg : 0 ≤ (C : ℝ)⁻¹ := inv_nonneg.mpr C.coe_nonneg
  obtain ⟨b, hb, _, hbIcc, hden⟩ := exists_common_density_of_ae_proportional (μ := μ)
    Γ₀ Γ id (E.energyReferenceWeight d) hr ht hΓ₀ hΓ rfl hnonneg hpoint
  let a (x : CarpetPoints) := max ((C : ℝ)⁻¹) (min (C : ℝ) (b x))
  have ha : Measurable a := measurable_const.max (measurable_const.min hb)
  have hle : (C : ℝ)⁻¹ ≤ (C : ℝ) := by
    have hC' : 1 ≤ (C : ℝ) := by exact_mod_cast hC
    exact ((inv_le_one₀ (zero_lt_one.trans_le hC')).mpr hC').trans hC'
  have haIcc (x : CarpetPoints) : a x ∈ Icc ((C : ℝ)⁻¹) (C : ℝ) :=
    ⟨le_max_left _ _, max_le hle (min_le_left _ _)⟩
  have hab : a =ᵐ[μ] b := hbIcc.mono fun x hx ↦ by
    change max ((C : ℝ)⁻¹) (min (C : ℝ) (b x)) = b x
    rw [min_eq_right hx.2, max_eq_right hx.1]
  have hden' (n : ℕ) : Γ n = (Γ₀ n).withDensity (fun x ↦ ENNReal.ofReal (a x)) := by
    rw [hden n]
    exact withDensity_congr_ae (((hdom (d n)).ae_eq hab).symm.mono fun _ hx ↦
      congrArg ENNReal.ofReal hx)
  have hroot (f : E.domain) : D.rootSeminorm (Submodule.inclusion hED f) ≤
      (C : ℝ) ^ p⁻¹ * E.rootSeminorm f := by
    have hmass := hcomp f univ
    rw [smul_apply, smul_eq_mul, D.energyMeasure_univ, E.energyMeasure_univ] at hmass
    have hpow := Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hmass)
      (inv_nonneg.mpr (zero_lt_one.trans E.one_lt_p).le)
    rw [ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal] at hpow
    rw [D.rootSeminorm_apply, E.rootSeminorm_apply]
    exact hpow.trans_eq (Real.mul_rpow C.coe_nonneg (E.energy f).property)
  refine ⟨a, ha, haIcc, fun f ↦ ?_⟩
  exact E.energyMeasure_eq_withDensity_of_energyDense D hED μ hdom d hdense hroot
    ha.ennreal_ofReal (fun x ↦ (ENNReal.ofReal_le_ofReal (haIcc x).2).trans_eq
      ENNReal.ofReal_coe_nnreal) hden' f

end CarpetEnergy.SelfSimilarPEnergy
