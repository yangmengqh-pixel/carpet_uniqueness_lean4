import EnergyPairDensityBounds

/-!
# Integrating directional density estimates

An upper and lower bound on a set where a cell is concentrated gives
two-sided estimates for any portion of the cell. The error is
proportional to the cell mass, so it survives normalization.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

theorem measure_bounds_by_density {ν μ : Measure CarpetPoints} [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (hac : ν ≪ μ) {C : Set CarpetPoints} (hC : MeasurableSet C)
    {T : Set CarpetPoints} (hT : MeasurableSet T) (L U : ℝ≥0∞)
    (hL : ∀ᵐ x ∂μ, x ∈ C → L ≤ ν.rnDeriv μ x)
    (hU : ∀ᵐ x ∂μ, x ∈ C → ν.rnDeriv μ x ≤ U) :
    L * μ (T ∩ C) ≤ ν (T ∩ C) ∧ ν (T ∩ C) ≤ U * μ (T ∩ C) := by
  let : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  rw [← Measure.setLIntegral_rnDeriv hac, ← setLIntegral_const, ← setLIntegral_const]
  exact ⟨lintegral_mono_ae ((ae_restrict_iff' (hT.inter hC)).mpr
    (hL.mono fun _ hx hh ↦ hx hh.2)),
    lintegral_mono_ae ((ae_restrict_iff' (hT.inter hC)).mpr
      (hU.mono fun _ hx hh ↦ hx hh.2))⟩

private theorem measure_rnDeriv_le_of_le_ae {ν μ : Measure CarpetPoints}
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (hac : ν ≪ μ) (U : ℝ≥0∞)
    (hU : ∀ᵐ x ∂μ, ν.rnDeriv μ x ≤ U) (A : Set CarpetPoints) (_hA : MeasurableSet A) :
    ν A ≤ U * μ A := by
  let : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  rw [← Measure.setLIntegral_rnDeriv hac, ← setLIntegral_const]
  exact lintegral_mono_ae (ae_restrict_of_ae hU)

/-- Integrated errors for a Borel portion of a cell whose mass is
concentrated where the density is close to a constant. -/
theorem measure_directional_sandwich {ν μ : Measure CarpetPoints}
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (hac : ν ≪ μ)
    {C T K : Set CarpetPoints} (hC : MeasurableSet C) (hT : MeasurableSet T) (hTK : T ⊆ K)
    (θ ε U : ℝ≥0∞) (hU : ∀ᵐ x ∂μ, ν.rnDeriv μ x ≤ U)
    (hclose : ∀ x ∈ C, ν.rnDeriv μ x ≤ θ + ε ∧ θ ≤ ν.rnDeriv μ x + ε)
    (hsmall : μ (K ∩ Cᶜ) ≤ ε * μ K) :
    ν T ≤ θ * μ T + (ε + U * ε) * μ K ∧
      θ * μ T ≤ ν T + (ε + θ * ε) * μ K := by
  let : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hmν := measure_inter_add_sdiff T hC (μ := ν)
  have hmμ := measure_inter_add_sdiff T hC (μ := μ)
  have hle : μ (T \ C) ≤ ε * μ K :=
    (measure_mono (show T \ C ⊆ K ∩ Cᶜ from fun _ hx ↦ ⟨hTK hx.1, hx.2⟩)).trans hsmall
  have hTc : μ (T ∩ C) ≤ μ T := measure_mono inter_subset_left
  have ht := hTc.trans (measure_mono hTK)
  have h₁ : ν (T ∩ C) ≤ (θ + ε) * μ (T ∩ C) :=
    (measure_bounds_by_density hac hC hT 0 (θ + ε)
      (Eventually.of_forall fun _ _ ↦ bot_le)
      (Eventually.of_forall fun x hx ↦ (hclose x hx).1)).2
  have h₂ : θ * μ (T ∩ C) ≤ ν (T ∩ C) + ε * μ (T ∩ C) := by
    rw [← Measure.setLIntegral_rnDeriv hac, ← setLIntegral_const, ← setLIntegral_const,
      ← lintegral_add_right _ measurable_const]
    exact lintegral_mono_ae ((ae_restrict_iff' (hT.inter hC)).mpr
      (Eventually.of_forall fun x hx ↦ (hclose x hx.2).2))
  constructor
  · calc
      ν T = ν (T ∩ C) + ν (T \ C) := hmν.symm
      _ ≤ (θ + ε) * μ (T ∩ C) + U * μ (T \ C) := add_le_add h₁
        (measure_rnDeriv_le_of_le_ae hac U hU _ (hT.diff hC))
      _ ≤ (θ * μ T + ε * μ K) + U * (ε * μ K) := by
        rw [add_mul]
        exact add_le_add (add_le_add (mul_le_mul' le_rfl hTc) (mul_le_mul' le_rfl ht))
          (mul_le_mul' le_rfl hle)
      _ = _ := by rw [add_mul, mul_assoc, add_assoc]
  · calc
      θ * μ T = θ * μ (T ∩ C) + θ * μ (T \ C) := by nth_rw 1 [← hmμ]; rw [mul_add]
      _ ≤ (ν (T ∩ C) + ε * μ (T ∩ C)) + θ * μ (T \ C) :=
        add_le_add h₂ le_rfl
      _ ≤ (ν T + ε * μ K) + θ * (ε * μ K) :=
        add_le_add (add_le_add (measure_mono inter_subset_left) (mul_le_mul' le_rfl ht))
          (mul_le_mul' le_rfl hle)
      _ = _ := by rw [add_mul, mul_assoc, add_assoc]

end CarpetEnergy
