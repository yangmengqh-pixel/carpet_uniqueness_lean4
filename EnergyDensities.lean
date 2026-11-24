import EnergyDominance

/-!
# Pointwise seminorms of Radon–Nikodym densities

The triangle inequality for the roots of the masses on measurable sets
implies the pointwise inequality for the roots of the densities. Rational
level bounds reduce its exceptional set to a countable union of null sets.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The p-th root of the Radon–Nikodym density, as a real-valued Borel function. -/
noncomputable def energyDensityRoot (μ : Measure CarpetPoints) (f : E.domain)
    (x : CarpetPoints) : ℝ :=
  ((E.energyMeasure f).rnDeriv μ x).toReal ^ p⁻¹

theorem measurable_energyDensityRoot (μ : Measure CarpetPoints) (f : E.domain) :
    Measurable (E.energyDensityRoot μ f) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.pow_const _

theorem energyDensityRoot_nonneg (μ : Measure CarpetPoints) (f : E.domain) (x : CarpetPoints) :
    0 ≤ E.energyDensityRoot μ f x := Real.rpow_nonneg ENNReal.toReal_nonneg _

theorem ofReal_energyDensityRoot_pow (μ : Measure CarpetPoints) (f : E.domain)
    {x : CarpetPoints} (hx : (E.energyMeasure f).rnDeriv μ x ≠ ∞) :
    ENNReal.ofReal (E.energyDensityRoot μ f x ^ p) = (E.energyMeasure f).rnDeriv μ x := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  change ENNReal.ofReal ((((E.energyMeasure f).rnDeriv μ x).toReal ^ p⁻¹) ^ p) = _
  exact (congrArg ENNReal.ofReal (Real.rpow_inv_rpow ENNReal.toReal_nonneg hp.ne')).trans
    (ENNReal.ofReal_toReal hx)

private theorem toReal_mul_pow_inv (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) (m : ℝ≥0∞) :
    ((ENNReal.ofReal (t ^ p) * m).toReal) ^ p⁻¹ = t * m.toReal ^ p⁻¹ := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht _)]
  calc
    _ = (t ^ p) ^ p⁻¹ * m.toReal ^ p⁻¹ := Real.mul_rpow (Real.rpow_nonneg ht _) ENNReal.toReal_nonneg
    _ = _ := congrArg (· * m.toReal ^ p⁻¹) (Real.rpow_rpow_inv ht hp.ne')

private theorem measure_null_of_density_root_bounds
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (f g : E.domain)
    (hdom : ∀ v, E.energyMeasure v ≪ μ)
    {A : Set CarpetPoints} (hA : MeasurableSet A) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < c)
    (hfinite : ∀ x ∈ A, (E.energyMeasure f).rnDeriv μ x ≠ ∞ ∧
      (E.energyMeasure g).rnDeriv μ x ≠ ∞ ∧ (E.energyMeasure (f + g)).rnDeriv μ x ≠ ∞)
    (hleft : ∀ x ∈ A, E.energyDensityRoot μ f x ≤ a)
    (hright : ∀ x ∈ A, E.energyDensityRoot μ g x ≤ b)
    (hsum : ∀ x ∈ A, c ≤ E.energyDensityRoot μ (f + g) x) :
    μ A = 0 := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hc : 0 ≤ c := (add_nonneg ha hb).trans hab.le
  have hupper (v : E.domain) {t : ℝ} (ht : 0 ≤ t)
      (hfin : ∀ x ∈ A, (E.energyMeasure v).rnDeriv μ x ≠ ∞)
      (hbound : ∀ x ∈ A, E.energyDensityRoot μ v x ≤ t) :
      E.energyMeasureSeminorm A hA v ≤ t * (μ A).toReal ^ p⁻¹ := by
    have hdec : (E.energyMeasure v).HaveLebesgueDecomposition μ :=
      Measure.haveLebesgueDecomposition_of_finiteMeasure
    have hmass : E.energyMeasure v A ≤ ENNReal.ofReal (t ^ p) * μ A := by
      rw [← Measure.setLIntegral_rnDeriv (hdom v) A, ← setLIntegral_const]
      apply lintegral_mono_ae
      apply (ae_restrict_iff' hA).mpr
      exact Eventually.of_forall fun x hx ↦ by
        rw [← E.ofReal_energyDensityRoot_pow μ v (hfin x hx)]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (E.energyDensityRoot_nonneg μ v x) (hbound x hx) hp.le)
    have h := Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hmass)
      (inv_nonneg.mpr hp.le)
    exact h.trans_eq (toReal_mul_pow_inv hp ht (μ A))
  have hlower : c * (μ A).toReal ^ p⁻¹ ≤ E.energyMeasureSeminorm A hA (f + g) := by
    have hdec : (E.energyMeasure (f + g)).HaveLebesgueDecomposition μ :=
      Measure.haveLebesgueDecomposition_of_finiteMeasure
    have hmass : ENNReal.ofReal (c ^ p) * μ A ≤ E.energyMeasure (f + g) A := by
      rw [← Measure.setLIntegral_rnDeriv (hdom (f + g)) A, ← setLIntegral_const]
      apply lintegral_mono_ae
      apply (ae_restrict_iff' hA).mpr
      exact Eventually.of_forall fun x hx ↦ by
        rw [← E.ofReal_energyDensityRoot_pow μ (f + g) (hfinite x hx).2.2]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hc (hsum x hx) hp.le)
    have h := Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (measure_ne_top _ _) hmass) (inv_nonneg.mpr hp.le)
    exact (toReal_mul_pow_inv hp hc (μ A)).symm.le.trans h
  have h := hlower.trans ((map_add_le_add (E.energyMeasureSeminorm A hA) f g).trans
    (add_le_add (hupper f ha (fun x hx ↦ (hfinite x hx).1) hleft)
      (hupper g hb (fun x hx ↦ (hfinite x hx).2.1) hright)))
  rw [← add_mul] at h
  by_contra hA0
  have hpos : 0 < (μ A).toReal ^ p⁻¹ :=
    Real.rpow_pos_of_pos (ENNReal.toReal_pos hA0 (measure_ne_top _ _)) _
  exact hab.not_ge (le_of_mul_le_mul_right h hpos)

/-- The roots of the densities satisfy the triangle inequality almost everywhere. -/
theorem ae_energyDensityRoot_add_le (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (hdom : ∀ f, E.energyMeasure f ≪ μ) (f g : E.domain) :
    ∀ᵐ x ∂μ, E.energyDensityRoot μ (f + g) x ≤
      E.energyDensityRoot μ f x + E.energyDensityRoot μ g x := by
  let A (a b c : ℚ) : Set CarpetPoints :=
    {x | (E.energyMeasure f).rnDeriv μ x ≠ ∞ ∧
      (E.energyMeasure g).rnDeriv μ x ≠ ∞ ∧ (E.energyMeasure (f + g)).rnDeriv μ x ≠ ∞} ∩
    ({x | E.energyDensityRoot μ f x ≤ (a : ℝ)} ∩
      {x | E.energyDensityRoot μ g x ≤ (b : ℝ)} ∩
      {x | (c : ℝ) ≤ E.energyDensityRoot μ (f + g) x})
  have hnull (a b c : ℚ) (ha : 0 ≤ (a : ℝ)) (hb : 0 ≤ (b : ℝ))
      (hab : (a : ℝ) + (b : ℝ) < (c : ℝ)) : μ (A a b c) = 0 := by
    have hne (v : E.domain) : MeasurableSet {x | (E.energyMeasure v).rnDeriv μ x ≠ ∞} :=
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl
    have hm : MeasurableSet (A a b c) :=
      ((hne f).inter ((hne g).inter (hne (f + g)))).inter
        ((measurableSet_le (E.measurable_energyDensityRoot μ f) measurable_const).inter
          (measurableSet_le (E.measurable_energyDensityRoot μ g) measurable_const) |>.inter
          (measurableSet_le measurable_const (E.measurable_energyDensityRoot μ (f + g))))
    exact E.measure_null_of_density_root_bounds μ f g hdom hm ha hb hab
      (fun _ hx ↦ hx.1) (fun _ hx ↦ hx.2.1.1) (fun _ hx ↦ hx.2.1.2) (fun _ hx ↦ hx.2.2)
  have hae : ∀ᵐ x ∂μ, ∀ a b c : ℚ, 0 ≤ (a : ℝ) → 0 ≤ (b : ℝ) →
      (a : ℝ) + (b : ℝ) < (c : ℝ) → x ∉ A a b c := by
    simp only [ae_all_iff]
    intro a b c ha hb hab
    exact measure_eq_zero_iff_ae_notMem.mp (hnull a b c ha hb hab)
  filter_upwards [hae, (E.energyMeasure f).rnDeriv_lt_top μ, (E.energyMeasure g).rnDeriv_lt_top μ,
    (E.energyMeasure (f + g)).rnDeriv_lt_top μ] with x hx hf hg hfg
  by_contra! h
  let rf := E.energyDensityRoot μ f x
  let rg := E.energyDensityRoot μ g x
  let rfg := E.energyDensityRoot μ (f + g) x
  change rf + rg < rfg at h
  obtain ⟨a, ha, haf⟩ := exists_rat_btwn (show rf < rfg - rg by linarith only [h])
  obtain ⟨b, hb, hbf⟩ := exists_rat_btwn (show rg < rfg - (a : ℝ) by linarith only [haf])
  obtain ⟨c, hc, hcf⟩ := exists_rat_btwn
    (show (a : ℝ) + (b : ℝ) < rfg by linarith only [hbf])
  exact hx a b c ((E.energyDensityRoot_nonneg μ f x).trans ha.le)
    ((E.energyDensityRoot_nonneg μ g x).trans hb.le) hc
    ⟨⟨hf.ne, hg.ne, hfg.ne⟩, ⟨ha.le, hb.le⟩, hcf.le⟩

/-- The density roots are absolutely homogeneous almost everywhere. -/
theorem ae_energyDensityRoot_smul (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (c : ℝ) (f : E.domain) :
    ∀ᵐ x ∂μ, E.energyDensityRoot μ (c • f) x = |c| * E.energyDensityRoot μ f x := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hdec : (E.energyMeasure f).HaveLebesgueDecomposition μ :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  have h := Measure.rnDeriv_smul_left_of_ne_top (E.energyMeasure f) μ
    (r := ENNReal.ofReal (|c| ^ p)) ENNReal.ofReal_ne_top
  rw [← E.energyMeasure_smul] at h
  filter_upwards [h] with x hx
  change (E.energyMeasure (c • f)).rnDeriv μ x =
    ENNReal.ofReal (|c| ^ p) * (E.energyMeasure f).rnDeriv μ x at hx
  change (((E.energyMeasure (c • f)).rnDeriv μ x).toReal) ^ p⁻¹ =
    |c| * (((E.energyMeasure f).rnDeriv μ x).toReal) ^ p⁻¹
  rw [hx]
  exact toReal_mul_pow_inv hp (abs_nonneg c) _

/-- On any countable rational subspace all density-root seminorm identities
hold simultaneously outside a single null set. -/
theorem ae_exists_energyDensityRoot_seminorm (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (hdom : ∀ f, E.energyMeasure f ≪ μ) (D : Submodule ℚ E.domain) [Countable D] :
    ∀ᵐ x ∂μ, ∃ q : Seminorm ℚ D, ∀ f : D, q f = E.energyDensityRoot μ (f : E.domain) x := by
  have h₁ : ∀ᵐ x ∂μ, ∀ f g : D, E.energyDensityRoot μ (↑f + ↑g) x ≤
      E.energyDensityRoot μ (f : E.domain) x + E.energyDensityRoot μ (g : E.domain) x := by
    exact ae_all_iff.mpr fun f ↦ ae_all_iff.mpr fun g ↦ E.ae_energyDensityRoot_add_le μ hdom _ _
  have h₂ : ∀ᵐ x ∂μ, ∀ (c : ℚ) (f : D),
      E.energyDensityRoot μ ((c • f : D) : E.domain) x =
        ‖c‖ * E.energyDensityRoot μ (f : E.domain) x := by
    refine ae_all_iff.mpr fun c ↦ ae_all_iff.mpr fun f ↦ ?_
    change ∀ᵐ x ∂μ, E.energyDensityRoot μ (c • (f : E.domain)) x =
      ‖c‖ * E.energyDensityRoot μ (f : E.domain) x
    rw [← Rat.cast_smul_eq_qsmul ℝ c (f : E.domain), ← Rat.norm_cast_real c, Real.norm_eq_abs]
    exact E.ae_energyDensityRoot_smul μ (c : ℝ) (f : E.domain)
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  let q : Seminorm ℚ D :=
    Seminorm.of (fun f : D ↦ E.energyDensityRoot μ (f : E.domain) x) hx₁ hx₂
  exact ⟨q, fun _ ↦ rfl⟩

/-- Comparison of energy measures gives the corresponding comparison of their
pointwise density roots with respect to a common finite dominating measure. -/
theorem ae_energyDensityRoot_le_of_energyMeasure_le_smul
    (D : SelfSimilarPEnergy p) (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (f : E.domain) (g : D.domain) (hf : E.energyMeasure f ≪ μ) (hg : D.energyMeasure g ≪ μ)
    (C : ℝ≥0) (h : E.energyMeasure f ≤ (C : ℝ≥0∞) • D.energyMeasure g) :
    ∀ᵐ x ∂μ, E.energyDensityRoot μ f x ≤ (C : ℝ) ^ p⁻¹ * D.energyDensityRoot μ g x := by
  let m := E.energyMeasure f
  let n := D.energyMeasure g
  have hm : m.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hn : n.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hder : ∀ᵐ x ∂μ, m.rnDeriv μ x ≤ (C : ℝ≥0∞) * n.rnDeriv μ x := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv m μ)
    intro A _ _
    calc
      (∫⁻ x in A, m.rnDeriv μ x ∂μ) = m A := Measure.setLIntegral_rnDeriv hf A
      _ ≤ (C : ℝ≥0∞) * n A := h A
      _ = ∫⁻ x in A, (C : ℝ≥0∞) * n.rnDeriv μ x ∂μ := by
        rw [lintegral_const_mul _ (Measure.measurable_rnDeriv n μ), Measure.setLIntegral_rnDeriv hg]
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  filter_upwards [hder, n.rnDeriv_ne_top μ] with x hx hfin
  have hfin' : (C : ℝ≥0∞) * n.rnDeriv μ x ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  change (m.rnDeriv μ x).toReal ^ p⁻¹ ≤ (C : ℝ) ^ p⁻¹ * (n.rnDeriv μ x).toReal ^ p⁻¹
  calc
    _ ≤ (((C : ℝ≥0∞) * n.rnDeriv μ x).toReal) ^ p⁻¹ := Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono hfin' hx) (inv_nonneg.mpr hp.le)
    _ = _ := by
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
      exact Real.mul_rpow C.coe_nonneg ENNReal.toReal_nonneg

end CarpetEnergy.SelfSimilarPEnergy
