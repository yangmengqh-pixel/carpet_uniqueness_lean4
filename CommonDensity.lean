import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# A common density for a countable family of energy measures

This is the integration and normalization step of Proposition 7.5 of
*On the uniqueness of p-energy on the Sierpiński carpet*.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

variable {X F J : Type*} [MeasurableSpace X] [Countable J] {μ : Measure X}

/-- A weighted sum of canonical measures equal to the reference measure
normalizes the corresponding weighted sum of densities to one. -/
theorem ae_tsum_density_eq_one [SigmaFinite μ] (d : J → F) (w : J → ℝ≥0∞)
    {r : F → X → ℝ≥0∞} (hr : ∀ f, Measurable (r f))
    (hμ : μ = Measure.sum (fun j ↦ w j • μ.withDensity (r (d j)))) :
    (fun x ↦ ∑' j, w j * r (d j) x) =ᵐ[μ] fun _ ↦ 1 := by
  have hmeas : Measurable (fun x ↦ ∑' j, w j * r (d j) x) :=
    Measurable.tsum fun j ↦ measurable_const.mul (hr (d j))
  apply (withDensity_eq_iff_of_sigmaFinite hmeas.aemeasurable measurable_const.aemeasurable).mp
  rw [withDensity_const, one_smul]
  apply Measure.ext
  intro A hA
  rw [withDensity_apply _ hA]
  rw [lintegral_tsum (f := fun j x ↦ w j * r (d j) x) (fun j ↦ (measurable_const.mul (hr (d j))).aemeasurable)]
  conv_rhs => rw [hμ]
  rw [Measure.sum_apply _ hA]
  congr 1
  funext j
  rw [lintegral_const_mul _ (hr (d j)), smul_apply, withDensity_apply _ hA, smul_eq_mul]

/-- Construct the common Borel density as the weighted sum of the competing
densities. The pointwise proportionality input is used simultaneously for
the whole countable family. -/
theorem exists_common_density_of_ae_proportional [SigmaFinite μ]
    (Γ₀ Γ : F → Measure X) (d : J → F) (w : J → ℝ≥0∞)
    {r t : F → X → ℝ≥0∞} (hr : ∀ f, Measurable (r f))
    (ht : ∀ f, Measurable (t f))
    (hΓ₀ : ∀ f, Γ₀ f = μ.withDensity (r f))
    (hΓ : ∀ f, Γ f = μ.withDensity (t f))
    (hμ : μ = Measure.sum (fun j ↦ w j • Γ₀ (d j)))
    {lower upper : ℝ} (hnonneg : 0 ≤ lower)
    (pointwise : ∀ᵐ x ∂μ, ∃ c ∈ Icc lower upper,
      ∀ f, t f x = ENNReal.ofReal c * r f x) :
    ∃ a : X → ℝ, Measurable a ∧ (∀ x, 0 ≤ a x) ∧
      (∀ᵐ x ∂μ, a x ∈ Icc lower upper) ∧
      ∀ f, Γ f = (Γ₀ f).withDensity fun x ↦ ENNReal.ofReal (a x) := by
  let b : X → ℝ≥0∞ := fun x ↦ ∑' j, w j * t (d j) x
  let a : X → ℝ := fun x ↦ (b x).toReal
  have hb : Measurable b := Measurable.tsum fun j ↦ measurable_const.mul (ht (d j))
  have ha : Measurable a := hb.ennreal_toReal
  have hnorm := ae_tsum_density_eq_one d w hr (by simpa only [hΓ₀] using hμ)
  have hprops : ∀ᵐ x ∂μ, a x ∈ Icc lower upper ∧
      ∀ f, t f x = r f x * ENNReal.ofReal (a x) := by
    filter_upwards [hnorm, pointwise] with x hn hx
    obtain ⟨c, hc, hct⟩ := hx
    have hn' : (∑' j, w j * r (d j) x) = 1 := hn
    have hbx : b x = ENNReal.ofReal c := by
      change (∑' j, w j * t (d j) x) = ENNReal.ofReal c
      simp only [hct, mul_left_comm (w _) (ENNReal.ofReal c),
        ENNReal.tsum_mul_left, hn', mul_one]
    have hax : a x = c := by
      change (b x).toReal = c
      rw [hbx, ENNReal.toReal_ofReal (hnonneg.trans hc.1)]
    refine ⟨hax ▸ hc, fun f ↦ ?_⟩
    rw [hct, hax, mul_comm]
  refine ⟨a, ha, fun _ ↦ ENNReal.toReal_nonneg, hprops.mono (fun _ hx ↦ hx.1), fun f ↦ ?_⟩
  rw [hΓ, hΓ₀, ← withDensity_mul μ (hr f) ha.ennreal_ofReal]
  exact withDensity_congr_ae <| hprops.mono fun x hx ↦ hx.2 f

/-- The weighted sum over an energy-dense family dominates each measure.
Here the root of the mass of a measurable set is a seminorm bounded by
the root of the total energy, as used in Sections 6 and 7. -/
theorem absolutelyContinuous_weighted_sum_of_energy_approximation
    [AddCommGroup F] [Module ℝ F] (Γ : F → Measure X)
    (hfinite : ∀ f, IsFiniteMeasure (Γ f))
    (d : J → F) (w : J → ℝ≥0∞) (hw : ∀ j, w j ≠ 0)
    (energyRoot : F → ℝ) {p : ℝ} (hp : 0 < p)
    (seminormOnSet : ∀ A : Set X, MeasurableSet A → ∃ S : Seminorm ℝ F,
      ∀ f, S f = ((Γ f A).toReal ^ p⁻¹) ∧ S f ≤ energyRoot f)
    (approx : ∀ f, ∃ j : ℕ → J,
      Tendsto (fun n ↦ energyRoot (f - d (j n))) atTop (𝓝 0)) :
    ∀ f, Γ f ≪ Measure.sum (fun j ↦ w j • Γ (d j)) := by
  intro f
  apply Measure.AbsolutelyContinuous.mk
  intro A hAm hA
  have hnull (j : J) : Γ (d j) A = 0 := by
    have hz := Measure.sum_apply_eq_zero.mp hA j
    rw [smul_apply, smul_eq_mul, mul_eq_zero] at hz
    exact hz.resolve_left (hw j)
  obtain ⟨S, hS⟩ := seminormOnSet A hAm
  have hSd (j : J) : S (d j) = 0 := by
    rw [(hS _).1, hnull j, ENNReal.toReal_zero, Real.zero_rpow (inv_ne_zero hp.ne')]
  obtain ⟨j, hj⟩ := approx f
  have hle : S f ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hj
    filter_upwards with n
    calc
      S f = S ((f - d (j n)) + d (j n)) := by rw [sub_add_cancel]
      _ ≤ S (f - d (j n)) + S (d (j n)) := map_add_le_add S _ _
      _ ≤ energyRoot (f - d (j n)) := by rw [hSd, add_zero]; exact (hS _).2
  have hf := le_antisymm hle (apply_nonneg S f)
  have : IsFiniteMeasure (Γ f) := hfinite f
  rw [(hS f).1, Real.rpow_eq_zero_iff_of_nonneg ENNReal.toReal_nonneg] at hf
  calc
    Γ f A = ENNReal.ofReal (Γ f A).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = 0 := by rw [hf.1, ENNReal.ofReal_zero]

end CarpetEnergy
