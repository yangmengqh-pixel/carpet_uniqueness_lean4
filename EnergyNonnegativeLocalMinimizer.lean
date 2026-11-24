import EnergyCellUnionCalculus

/-!
# Nonnegative representatives of local minimizers on unions of cells
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 3700000 in
/-- Taking the positive part preserves the local minimizing property on
a union of cells where the original profile is nonnegative. -/
theorem exists_nonnegative_minimizer_ae_eq_on_wordCellUnion
    {n : ℕ} (S : Finset (Fin n → Fin 8)) (f : E.domain)
    (hf : E.MinimizesWithExterior (wordCellUnion Sᶜ) f)
    (hf₀ : ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion S), 0 ≤ (f : CarpetLp p) x) :
    ∃ g : E.domain, (∀ᵐ x ∂carpetMeasure, 0 ≤ (g : CarpetLp p) x) ∧
      (g : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion S)] (f : CarpetLp p) ∧
      E.MinimizesWithExterior (wordCellUnion Sᶜ) g := by
  obtain ⟨g, hg, _⟩ := E.exists_cellUnionEnergy_comp_le S Lp.lipschitzWith_pos_part f
  have hg₀ : ∀ᵐ x ∂carpetMeasure, 0 ≤ (g : CarpetLp p) x := hg.mono fun x hx ↦
    hx.symm ▸ le_max_right ((f : CarpetLp p) x) 0
  have heq : (g : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion S)] (f : CarpetLp p) := by
    filter_upwards [ae_restrict_of_ae hg, hf₀] with x hx hfx
    exact hx.trans (max_eq_left hfx)
  refine ⟨g, hg₀, heq, (E.minimizesWithExterior_wordCellUnion_iff S g).mpr ?_⟩
  intro u hu
  let v := u + (f - g)
  have hv (A : Set CarpetPoints) :
      ∀ᵐ x ∂carpetMeasure.restrict A, (v : CarpetLp p) x =
        (u : CarpetLp p) x + ((f : CarpetLp p) x - (g : CarpetLp p) x) := by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (u : CarpetLp p) ((f - g : E.domain) : CarpetLp p)),
      ae_restrict_of_ae (Lp.coeFn_sub (f : CarpetLp p) (g : CarpetLp p))] with x h₁ h₂
    change ((u : CarpetLp p) + ((f - g : E.domain) : CarpetLp p)) x = _
    rw [h₁, Pi.add_apply]
    change (u : CarpetLp p) x + ((f : CarpetLp p) - (g : CarpetLp p)) x = _
    rw [h₂, Pi.sub_apply]
  have hvext : (v : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion Sᶜ)] (f : CarpetLp p) := by
    filter_upwards [hv (wordCellUnion Sᶜ), hu] with x hx hx'
    rw [hx, hx']
    ring
  have hvint : (v : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion S)] (u : CarpetLp p) := by
    filter_upwards [hv (wordCellUnion S), heq] with x hx hx'
    rw [hx, hx', sub_self, add_zero]
  have h := (E.minimizesWithExterior_wordCellUnion_iff S f).mp hf v hvext
  rwa [← E.cellUnionEnergy_eq_of_ae_eq S heq, E.cellUnionEnergy_eq_of_ae_eq S hvint] at h

end CarpetEnergy.SelfSimilarPEnergy
