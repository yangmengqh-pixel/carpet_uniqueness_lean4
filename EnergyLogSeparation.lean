import EnergyDistanceSpanningSeparation
import EnergyNormalizedHarmonic
import EnergyGlobalNormalization

/-!
# Applying the separation estimate to a shifted logarithm
-/

open Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 3100000 in
/-- A lower separation estimate for a normalized profile gives an
energy cost proportional to the (p)-th power of the separating gap. -/
theorem exists_energy_lower_of_distance_spanning_gap (hρ : E.scalingFactor ≤ 1) :
    ∃ A c : ℝ, 1 ≤ A ∧ 0 < c ∧
      ∀ (x : CarpetPoints) (R : ℝ), 0 < R → R ≤ 1 / 2 →
        ∀ (S T : Set CarpetPoints), S ⊆ ball x R → T ⊆ ball x R →
          Icc (R / 2) (3 * R / 4) ⊆ (fun y ↦ dist y x) '' S →
          Icc (R / 2) (3 * R / 4) ⊆ (fun y ↦ dist y x) '' T →
          ∀ (f : E.continuousCore) (a b : ℝ), a < b →
            (∀ y ∈ S, b ≤ f.val y) → (∀ y ∈ T, f.val y ≤ a) →
            c * R ^ (carpetSimilarityDimension - E.walkDimension) * (b - a) ^ p ≤
              (E.energyMeasure (E.continuousCoreToDomain f)).real (ball x (A * R)) := by
  obtain ⟨A, c, hA, hc, hsep⟩ := E.exists_energy_lower_of_distance_spanning_separation hρ
  refine ⟨A, c, hA, hc, fun x R hR hR' S T hS hT hSp hTp f a b hab hfS hfT ↦ ?_⟩
  let g := (b - a)⁻¹ • (f + E.constCore (-a))
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hgS (y : CarpetPoints) (hy : y ∈ S) : 1 ≤ g.val y := by
    change 1 ≤ (b - a)⁻¹ * (f.val y + -a)
    rw [← div_eq_inv_mul, le_div_iff₀ hgap, one_mul]
    linarith [hfS y hy]
  have hgT (y : CarpetPoints) (hy : y ∈ T) : g.val y ≤ 0 := by
    change (b - a)⁻¹ * (f.val y + -a) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hgap.le) (by linarith [hfT y hy])
  have hh := hsep x R hR hR' S T hS hT hSp hTp g hgS hgT
  let d := E.continuousCoreToDomain f
  have hΓ : E.energyMeasure (E.continuousCoreToDomain g) =
      ENNReal.ofReal ((b - a)⁻¹ ^ p) • E.energyMeasure d := by
    dsimp only [g]
    rw [map_smul, map_add, E.energyMeasure_smul, abs_of_pos (inv_pos.mpr hgap),
      E.continuousCoreToDomain_constCore, E.energyMeasure_add_constant]
  rw [hΓ, measureReal_def, smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (inv_nonneg.mpr hgap.le) _),
    Real.inv_rpow hgap.le, inv_mul_eq_div] at hh
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hgap p)).mp hh

end CarpetEnergy.SelfSimilarPEnergy
