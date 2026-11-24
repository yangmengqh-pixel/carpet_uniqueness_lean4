import EnergyHarmonicReplacement
import EnergyLatticeContraction

/-!
# Comparison of harmonic replacements

The minimum and maximum are competitors with the respective exterior
values. The lattice bound forces equality in both minimizing
inequalities, so uniqueness gives the comparison principle.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

theorem MinimizesWithExterior.ae_le {A : Set CarpetPoints} (hA : carpetMeasure A ≠ 0)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ E.energy f)) {f g : E.domain}
    (hf : E.MinimizesWithExterior A f) (hg : E.MinimizesWithExterior A g)
    (hfg : (f : CarpetLp p) ≤ᵐ[carpetMeasure.restrict A] (g : CarpetLp p)) :
    (f : CarpetLp p) ≤ᵐ[carpetMeasure] (g : CarpetLp p) := by
  obtain ⟨u, v, hu, hv, hsum⟩ := E.exists_lattice_energy_le hG f g
  have huf : (u : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (f : CarpetLp p) := by
    filter_upwards [hu.filter_mono (ae_mono Measure.restrict_le_self), hfg] with x hx hle
    exact hx.trans (min_eq_left hle)
  have hvg : (v : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (g : CarpetLp p) := by
    filter_upwards [hv.filter_mono (ae_mono Measure.restrict_le_self), hfg] with x hx hle
    exact hx.trans (max_eq_right hle)
  have hEuf : E.energy u = E.energy f := by
    have h := hf u huf
    have h' := hg v hvg
    exact le_antisymm (le_of_add_le_add_right (hsum.trans (add_le_add_right h' _))) h
  have humin : E.MinimizesWithExterior A u := by
    intro z hz
    rw [hEuf]
    exact hf z (hz.trans huf)
  have heq := MinimizesWithExterior.eq_of_ae_eq E hA humin hf huf
  rw [heq] at hu
  filter_upwards [hu] with x hx
  exact hx.le.trans (min_le_right _ _)

theorem MinimizesWithExterior.ae_nonneg {A : Set CarpetPoints} (hA : carpetMeasure A ≠ 0)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ E.energy f)) {f : E.domain}
    (hf : E.MinimizesWithExterior A f) (hn : ∀ᵐ x ∂carpetMeasure.restrict A, 0 ≤ (f : CarpetLp p) x) :
    ∀ᵐ x ∂carpetMeasure, 0 ≤ (f : CarpetLp p) x := by
  let z : E.domain := ⟨constantLp p 0, E.constant_mem 0⟩
  have hE : E.energy z = 0 := (E.zero_iff_constant z).mpr ⟨0, rfl⟩
  have hz : E.MinimizesWithExterior A z := by intro _ _; rw [hE]; exact zero_le
  have he : (z : CarpetLp p) =ᵐ[carpetMeasure] fun _ ↦ (0 : ℝ) :=
    Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure 0
  have hle : (z : CarpetLp p) ≤ᵐ[carpetMeasure.restrict A] (f : CarpetLp p) := by
    filter_upwards [he.filter_mono (ae_mono Measure.restrict_le_self), hn] with x hx hx'
    exact hx.le.trans hx'
  filter_upwards [MinimizesWithExterior.ae_le E hA hG hz hf hle, he] with x hx hx'
  exact hx'.symm.le.trans hx

end CarpetEnergy.SelfSimilarPEnergy
