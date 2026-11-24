import EnergyContinuousLogTest
import EnergyLocalSmoothChainBound
import EnergyApproximateVariation

/-!
# Logarithmic energy bounds for graph approximations of minimizers
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3800000 in
/-- The log energy on an open set is controlled by the weighted
logarithmic integral for any cutoff equal to one there. -/
theorem exists_log_core_energy_le
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {V : Set CarpetPoints} (hV : IsOpen V)
    (f χ : E.continuousCore) (hf₀ : ∀ x, 0 ≤ f.val x)
    (hχ : ∀ x, χ.val x ∈ Icc (0 : ℝ) 1) (hχ₁ : ∀ x ∈ V, χ.val x = 1)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ L : E.continuousCore, (∀ x, L.val x = Real.log (f.val x + ε)) ∧
      (E.energyMeasure (E.continuousCoreToDomain L)).real V ≤
        ∫ x, (χ.val x) ^ m * (f.val x + ε) ^ (-p)
          ∂E.energyMeasure (E.continuousCoreToDomain f) := by
  obtain ⟨S, hS, hSp, hSid⟩ := exists_smooth_positive_shift hε
  let ψ : ℝ → ℝ := Real.log ∘ S
  have hψ : ContDiff ℝ 1 ψ := hS.log (fun t ↦ (hSp t).ne')
  let u : Fin 1 → E.continuousCore := fun _ ↦ f
  let P : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let φ : (Fin 1 → ℝ) → ℝ := ψ ∘ P
  obtain ⟨L, hL₀⟩ := E.exists_core_comp_contDiff hc u φ (hψ.comp P.contDiff)
  have hL (y : CarpetPoints) : L.val y = ψ (f.val y) := hL₀ y
  have hlog (y : CarpetPoints) : L.val y = Real.log (f.val y + ε) := by
    rw [hL]
    exact congrArg Real.log (hSid _ (hf₀ y)).1
  let W (y : CarpetPoints) := (f.val y + ε) ^ (-p)
  have hW (y : CarpetPoints) : |deriv ψ (f.val y)| ^ p = W y := by
    have hd := (Real.hasDerivAt_log (hSp (f.val y)).ne').comp _ (hSid _ (hf₀ y)).2
    change HasDerivAt ψ _ (f.val y) at hd
    rw [hd.deriv, (hSid _ (hf₀ y)).1, mul_one,
      abs_of_pos (inv_pos.mpr (add_pos_of_nonneg_of_pos (hf₀ y) hε)), ← Real.rpow_neg_eq_inv_rpow]
  let μ := E.energyMeasure (E.continuousCoreToDomain f)
  have hWc : Continuous W := (f.val.continuous.add continuous_const).rpow_const
    (fun y ↦ Or.inl (add_pos_of_nonneg_of_pos (hf₀ y) hε).ne')
  have hWI : Integrable (fun y ↦ (χ.val y) ^ m * W y) μ :=
    ((χ.val.continuous.pow _).mul hWc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlocal := E.energyMeasure_real_smooth_comp_le_open h hc f L ψ hψ hL hV
  simp only [hW] at hlocal
  refine ⟨L, hlog, hlocal.trans ?_⟩
  change (∫ y in V, W y ∂μ) ≤ ∫ y, (χ.val y) ^ m * W y ∂μ
  have hBW : (∫ y in V, W y ∂μ) = ∫ y in V, (χ.val y) ^ m * W y ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
    rw [hχ₁ y hy, one_pow, one_mul]
  rw [hBW]
  simpa only [Measure.restrict_univ] using setIntegral_mono_set hWI.restrict
    (Eventually.of_forall fun y ↦ mul_nonneg (pow_nonneg (hχ y).1 _)
      (Real.rpow_nonneg (add_nonneg (hf₀ y) hε.le) _))
    (Eventually.of_forall (subset_univ V))

set_option maxHeartbeats 3900000 in
/-- At any fixed positive logarithmic shift, the eventual bound is
independent of the shift and the minimizing profile. -/
theorem eventually_exists_log_core_energy_le
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (hs : HasUniformSymmetricIncrement (fun f ↦ (E.energy f : ℝ)))
    {U V : Set CarpetPoints} (hU : MeasurableSet U) (hV : IsOpen V)
    (f : E.domain) (hf : E.MinimizesWithExterior Uᶜ f)
    (u : ℕ → E.continuousCore) (hu₀ : ∀ n x, 0 ≤ (u n).val x)
    (hu : Tendsto (fun n ↦ E.toGraph (E.continuousCoreToDomain (u n))) atTop (𝓝 (E.toGraph f)))
    (χ : E.continuousCore) (hχ : ∀ x, χ.val x ∈ Icc (0 : ℝ) 1)
    (hχ₁ : ∀ x ∈ V, χ.val x = 1) (hχ₀ : ∀ x ∉ U, χ.val x = 0)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) (m : ℕ) (hm : p ≤ (m : ℝ)) :
    ∀ᶠ n in atTop, ∃ L : E.continuousCore, (∀ x, L.val x = Real.log ((u n).val x + ε)) ∧
      (E.energyMeasure (E.continuousCoreToDomain L)).real V ≤
        max b (((2 * (m : ℝ)) / (p - 1)) ^ p * (E.energy (E.continuousCoreToDomain χ) : ℝ)) := by
  let d (n : ℕ) := E.continuousCoreToDomain (u n)
  let dχ := E.continuousCoreToDomain χ
  let I (n : ℕ) := ∫ x, (χ.val x) ^ m * ((u n).val x + ε) ^ (-p) ∂E.energyMeasure (d n)
  choose v hv₀ hvR hvI using fun n ↦ E.exists_logarithmic_test h hc (u n) χ (hu₀ n)
    hχ hχ₀ hε m hm
  let w (n : ℕ) := E.continuousCoreToDomain (v n)
  have hw₀ (n : ℕ) : ∀ᵐ x ∂carpetMeasure.restrict Uᶜ, (w n : CarpetLp p) x = 0 := by
    filter_upwards [ae_restrict_of_ae (continuousLp_ae_eq p (v n).val),
      ae_restrict_mem hU.compl] with x hx hxU
    exact hx.trans (hv₀ n x hxU)
  let B := E.rootSeminorm f + 1
  have hdR : ∀ᶠ n in atTop, E.rootSeminorm (d n) ≤ B := by
    have hd : Tendsto (fun n ↦ ‖E.toGraph (d n) - E.toGraph f‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hu
    filter_upwards [hd.eventually_lt_const zero_lt_one] with n hn
    have hN : E.rootSeminorm (d n - f) ≤ ‖E.toGraph (d n - f)‖ := E.rootSeminorm_le_graphSeminorm _
    change _ ≤ ‖E.toGraph (d n) - E.toGraph f‖ at hN
    have hsum := map_add_le_add E.rootSeminorm (d n - f) f
    rw [sub_add_cancel] at hsum
    dsimp only [B]
    linarith
  let G := (p - 1) * ε ^ (-p) * B + (m : ℝ) * ε ^ (1 - p) * E.rootSeminorm dχ
  have hwR : ∀ᶠ n in atTop, E.rootSeminorm (w n) ≤ G := by
    filter_upwards [hdR] with n hn
    exact (hvR n).trans (add_le_add (mul_le_mul_of_nonneg_left hn
      (mul_nonneg (sub_nonneg.mpr E.one_lt_p.le) (Real.rpow_nonneg hε.le _))) le_rfl)
  have hvlim := E.tendsto_variation_zero_of_graph_tendsto h hs f hf d w hu hw₀ hwR
  have hpos : 0 < (p - 1) * b / 2 := half_pos (mul_pos (sub_pos.mpr E.one_lt_p) hb)
  have habs := continuous_abs.continuousAt.tendsto.comp hvlim
  rw [abs_zero] at habs
  filter_upwards [habs.eventually_lt_const hpos] with n hn
  obtain ⟨L, hL, hLE⟩ := E.exists_log_core_energy_le h hc hV (u n) χ (hu₀ n) hχ hχ₁ hε m
  refine ⟨L, hL, hLE.trans ?_⟩
  change I n ≤ _
  by_cases hib : I n ≤ b
  · exact hib.trans (le_max_left _ _)
  have htest : (p - 1) * I n ≤ (m : ℝ) *
      ((I n) ^ p.conjExponent⁻¹ * (E.energy dχ : ℝ) ^ p⁻¹) +
      |E.variation h (d n) (w n)| := hvI n
  have hbd := mul_le_mul_of_nonneg_left (le_of_not_ge hib) (sub_nonneg.mpr E.one_lt_p.le)
  change |E.variation h (d n) (w n)| < (p - 1) * b / 2 at hn
  have hh : (p - 1) * I n ≤ (2 * (m : ℝ)) *
      ((I n) ^ p.conjExponent⁻¹ * (E.energy dχ : ℝ) ^ p⁻¹) := by
    nlinarith only [htest, hn, hbd]
  exact (log_budget_of_holder (Real.HolderConjugate.conjExponent E.one_lt_p)
    (hb.le.trans (le_of_not_ge hib)) (NNReal.coe_nonneg _)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hh).trans (le_max_right _ _)

end CarpetEnergy.SelfSimilarPEnergy
