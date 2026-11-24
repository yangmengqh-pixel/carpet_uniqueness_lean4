import EnergyHarmonicSupport
import EnergyAdjacentCellMeans

/-!
# Normalization for harmonic blowups

The word pullback is centered at its cell mean and scaled to unit energy.
The remaining compactness property is stated for these normalized
pullbacks, in the form used by the zero-one proof.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem energyMeasure_add_constant (f : E.domain) (c : ℝ) :
    E.energyMeasure (f + ⟨constantLp p c, E.constant_mem c⟩) = E.energyMeasure f := by
  let g : E.domain := ⟨constantLp p c, E.constant_mem c⟩
  have hc : E.energy g = 0 := (E.zero_iff_constant g).2 ⟨c, rfl⟩
  have hΓ : E.energyMeasure g = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    rw [E.energyMeasure_univ, hc, ENNReal.coe_zero]
  ext A hA
  apply E.energyMeasure_apply_eq_of_sub_null hA
  change E.energyMeasure (f + g - f) A = 0
  rw [add_sub_cancel_left, hΓ]
  simp

theorem IsInteriorHarmonic.smul {f : E.domain}
    (hf : E.IsInteriorHarmonic f) (a : ℝ) : E.IsInteriorHarmonic (a • f) := by
  intro u hu htrace
  by_cases ha : a = 0
  · rw [ha, zero_smul, zero_add]
    exact (show E.energy 0 = 0 from (E.zero_iff_constant 0).2 ⟨0, by
      apply Lp.ext
      exact (Lp.coeFn_zero _ _ _).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure 0).symm⟩)
      ▸ zero_le
  let U : E.domain := ⟨continuousLp p u, hu⟩
  let v := a⁻¹ • u
  have hv : continuousLp p v = ((a⁻¹ • U : E.domain) : CarpetLp p) :=
    (SelfSimilarComponent.continuousLpLinear p).map_smul _ _
  have hv' : continuousLp p v ∈ E.domain := hv.symm ▸ (a⁻¹ • U).property
  have hV : (⟨continuousLp p v, hv'⟩ : E.domain) = a⁻¹ • U := Subtype.ext hv
  have h := hf v hv' (fun x hx ↦ by change a⁻¹ * u x = 0; rw [htrace x hx, mul_zero])
  rw [hV] at h
  have he : a • (f + a⁻¹ • U) = a • f + U := by rw [smul_add, smul_inv_smul₀ ha]
  apply NNReal.coe_le_coe.mp
  change (E.energy (a • f) : ℝ) ≤ (E.energy (a • f + U) : ℝ)
  rw [← he, E.smul_energy, E.smul_energy]
  exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr h) (Real.rpow_nonneg (abs_nonneg _) _)

theorem pullback_energy_pos_of_mass {f : E.domain} (w : List (Fin 8))
    (hw : 0 < E.energyMeasure f (range (wordMap w))) :
    0 < E.energy (E.pullbackWord w f) := by
  by_contra! h
  have hz : E.energy (E.pullbackWord w f) = 0 := nonpos_iff_eq_zero.mp h
  rw [E.energyMeasure_range_word, hz, ENNReal.coe_zero, mul_zero] at hw
  exact (lt_irrefl _ hw)

/-- Scale a positive finite energy to one. -/
noncomputable def unitEnergyScale (f : E.domain) : ℝ :=
  ((E.energy f : ℝ) ^ p⁻¹)⁻¹

theorem unitEnergyScale_pos {f : E.domain} (hf : 0 < E.energy f) : 0 < E.unitEnergyScale f :=
  inv_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hf) _)

theorem unitEnergyScale_rpow {f : E.domain} (hf : 0 < E.energy f) :
    |E.unitEnergyScale f| ^ p = (E.energy f : ℝ)⁻¹ := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  rw [abs_of_nonneg (E.unitEnergyScale_pos hf).le, unitEnergyScale,
    Real.inv_rpow (Real.rpow_nonneg (NNReal.coe_nonneg _) _),
    Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne']

theorem energy_unitEnergyScale_smul {f : E.domain} (hf : 0 < E.energy f) :
    E.energy (E.unitEnergyScale f • f) = 1 := by
  apply NNReal.eq
  have h : (E.energy f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  rw [E.smul_energy, E.unitEnergyScale_rpow hf, inv_mul_cancel₀ h]
  rfl

/-- Pull back, subtract the cell mean, and normalize to unit energy. -/
noncomputable def normalizedWordPullback (w : List (Fin 8)) (f : E.domain) : E.domain :=
  E.unitEnergyScale (E.pullbackWord w f) •
    (E.pullbackWord w f + ⟨constantLp p (-E.wordMean w f), E.constant_mem _⟩)

theorem energy_normalizedWordPullback (w : List (Fin 8)) (f : E.domain)
    (h : 0 < E.energy (E.pullbackWord w f)) : E.energy (E.normalizedWordPullback w f) = 1 := by
  apply NNReal.eq
  have he : (E.energy (E.pullbackWord w f) : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  rw [normalizedWordPullback, E.smul_energy, E.add_constant, E.unitEnergyScale_rpow h, inv_mul_cancel₀ he]
  rfl

/-- Specialized harmonic blowup compactness needed in the zero-one
argument. This is the compactness input from Proposition 4.2 applied to
normalized pullbacks of an interior-harmonic function. -/
def HasInteriorHarmonicCompactness : Prop :=
  ∀ (f : E.domain), E.IsInteriorHarmonic f →
    ∀ (n : ℕ → ℕ) (w : ∀ k, Fin (n k) → Fin 8),
      (∀ k, k ≤ n k) →
      (∀ k, 0 < E.energyMeasure f (range (wordMap (List.ofFn (w k))))) →
      (∃ a : ℝ≥0∞, 0 < a ∧ ∀ k, a * E.energyMeasure f (wordCellUnion (cellNeighborhood (w k) 3)) ≤
        E.energyMeasure f (range (wordMap (List.ofFn (w k))))) →
      (∀ k, wordCellUnion (cellNeighborhood (w k) 3) ⊆ carpetOuterBoundaryᶜ) →
      ∃ (j : ℕ → ℕ) (g : E.domain) (u : C(CarpetPoints, ℝ)), StrictMono j ∧
        continuousLp p u = (g : CarpetLp p) ∧
        Tendsto (fun k ↦ E.toGraph (E.normalizedWordPullback (List.ofFn (w (j k))) f))
          atTop (𝓝 (E.toGraph g))

end CarpetEnergy.SelfSimilarPEnergy
