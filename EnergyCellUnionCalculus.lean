import EnergyCellHarmonicReplacement
import EnergyBoundaryNullity
import EnergyLipschitz

/-!
# Energy-measure calculus on a union of cells

The cell energy is the mass of the union. This transfers the energy
measure triangle and composition inequalities to local energies.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem cellUnionEnergy_eq_energyMeasure_real {n : ℕ} (S : Finset (Fin n → Fin 8))
    (f : E.domain) : E.cellUnionEnergy S f = (E.energyMeasure f).real (wordCellUnion S) := by
  unfold Measure.real
  rw [measure_wordCellUnion _ (E.energyMeasure_carpetCellBoundary_eq_zero
    E.energyMeasure_carpetOuterBoundary_eq_zero f n),
    ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
  simp only [E.energyMeasure_range_word, List.length_ofFn, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal E.isScalingFactor_scalingFactor.1.le, ENNReal.coe_toReal,
    ← Finset.mul_sum, cellUnionEnergy]

theorem cellUnionEnergy_nonneg {n : ℕ} (S : Finset (Fin n → Fin 8)) (f : E.domain) :
    0 ≤ E.cellUnionEnergy S f := by
  rw [E.cellUnionEnergy_eq_energyMeasure_real]
  exact ENNReal.toReal_nonneg

theorem cellUnionEnergy_sub_rpow_inv_le {n : ℕ} (S : Finset (Fin n → Fin 8)) (f g : E.domain) :
    E.cellUnionEnergy S (f - g) ^ p⁻¹ ≤ E.cellUnionEnergy S f ^ p⁻¹ + E.cellUnionEnergy S g ^ p⁻¹ := by
  simp only [E.cellUnionEnergy_eq_energyMeasure_real]
  let q := E.energyMeasureSeminorm (wordCellUnion S) (measurableSet_wordCellUnion S)
  change q (f - g) ≤ q f + q g
  exact map_sub_le_add q f g

theorem exists_cellUnionEnergy_comp_le {n : ℕ} (S : Finset (Fin n → Fin 8))
    {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (f : E.domain) :
    ∃ g : E.domain,
      (g : CarpetLp p) =ᵐ[carpetMeasure] φ ∘ (f : CarpetLp p) ∧
      E.cellUnionEnergy S g ≤ E.cellUnionEnergy S f := by
  obtain ⟨g, hg, hle⟩ := E.exists_energyMeasure_comp_le hφ f
  have hle' : E.energyMeasure g ≤ E.energyMeasure f := by
    simpa only [NNReal.one_rpow, ENNReal.coe_one, one_smul] using hle
  refine ⟨g, hg, ?_⟩
  simp only [E.cellUnionEnergy_eq_energyMeasure_real]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (hle' _)

end CarpetEnergy.SelfSimilarPEnergy
