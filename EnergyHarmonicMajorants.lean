import EnergyHarmonicComparison
import EnergyCellUnionCalculus

/-!
# Nonnegative harmonic majorants

Replacing the positive part of a harmonic function gives a
nonnegative harmonic majorant. Its energy on the region is bounded
by the local energy of the original function.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem MinimizesWithExterior.neg {A : Set CarpetPoints} {f : E.domain}
    (hf : E.MinimizesWithExterior A f) : E.MinimizesWithExterior A (-f) := by
  intro g hg
  have hneg (v : E.domain) : (-v : E.domain) = (-1 : ℝ) • v := (neg_one_smul ℝ v).symm
  have henergy (v : E.domain) : E.energy (-v) = E.energy v := by
    apply NNReal.eq
    rw [hneg, E.smul_energy, abs_neg, abs_one, Real.one_rpow, one_mul]
  rw [henergy, ← henergy g]
  apply hf
  filter_upwards [(Lp.coeFn_neg (g : CarpetLp p)).filter_mono (ae_mono Measure.restrict_le_self),
    (Lp.coeFn_neg (f : CarpetLp p)).filter_mono (ae_mono Measure.restrict_le_self), hg] with x h₁ h₂ h₃
  change ((-(g : CarpetLp p)) : CarpetLp p) x = -((g : CarpetLp p) x) at h₁
  change ((-(f : CarpetLp p)) : CarpetLp p) x = -((f : CarpetLp p) x) at h₂
  change (g : CarpetLp p) x = ((-(f : CarpetLp p)) : CarpetLp p) x at h₃
  change ((-(g : CarpetLp p)) : CarpetLp p) x = (f : CarpetLp p) x
  rw [h₁, h₃, h₂, neg_neg]

theorem MinimizesWithExterior.add_constant {A : Set CarpetPoints} {f : E.domain}
    (hf : E.MinimizesWithExterior A f) (c : ℝ) :
    E.MinimizesWithExterior A (f + ⟨constantLp p c, E.constant_mem c⟩) := by
  intro g hg
  let a : E.domain := ⟨constantLp p c, E.constant_mem c⟩
  let z := g - a
  have hza : z + a = g := sub_add_cancel _ _
  change E.energy (f + a) ≤ E.energy g
  rw [← hza, E.add_constant f c, E.add_constant z c]
  apply hf
  filter_upwards [hg, (Lp.coeFn_sub (g : CarpetLp p) (a : CarpetLp p)).filter_mono
    (ae_mono Measure.restrict_le_self), (Lp.coeFn_add (f : CarpetLp p) (a : CarpetLp p)).filter_mono
    (ae_mono Measure.restrict_le_self)] with x h₁ h₂ h₃
  change (g : CarpetLp p) x = ((f : CarpetLp p) + (a : CarpetLp p)) x at h₁
  change ((g : CarpetLp p) - (a : CarpetLp p)) x = (g : CarpetLp p) x - (a : CarpetLp p) x at h₂
  change ((f : CarpetLp p) + (a : CarpetLp p)) x = (f : CarpetLp p) x + (a : CarpetLp p) x at h₃
  change ((g : CarpetLp p) - (a : CarpetLp p)) x = (f : CarpetLp p) x
  rw [h₂, h₁, h₃, add_sub_cancel_right]

variable [Fact (1 ≤ ENNReal.ofReal p)]

/-- The nonnegative replacement of the positive part dominates the
original harmonic function and uses no more local energy. -/
theorem exists_nonneg_harmonic_majorant {n : ℕ} (S : Finset (Fin n → Fin 8))
    (hA : carpetMeasure (wordCellUnion Sᶜ) ≠ 0)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ E.energy f)) (f : E.domain)
    (hf : E.MinimizesWithExterior (wordCellUnion Sᶜ) f) :
    ∃ t u : E.domain, ((t : CarpetLp p) =ᵐ[carpetMeasure] fun x ↦ max ((f : CarpetLp p) x) 0) ∧
      ((u : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion Sᶜ)] (t : CarpetLp p)) ∧
      E.MinimizesWithExterior (wordCellUnion Sᶜ) u ∧
      (∀ᵐ x ∂carpetMeasure, 0 ≤ (u : CarpetLp p) x) ∧
      ((f : CarpetLp p) ≤ᵐ[carpetMeasure] (u : CarpetLp p)) ∧
      E.cellUnionEnergy S t ≤ E.cellUnionEnergy S f ∧
      E.cellUnionEnergy S u ≤ E.cellUnionEnergy S t := by
  let A := wordCellUnion Sᶜ
  have hpos : LipschitzWith 1 (fun x : ℝ ↦ max x 0) :=
    (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).max_const 0
  obtain ⟨t, ht, htE⟩ := E.exists_cellUnionEnergy_comp_le S hpos f
  obtain ⟨u, hu, hmin⟩ := E.exists_harmonic_with_fixed_values A hA t
  have humin : E.MinimizesWithExterior A u := fun g hg ↦ hmin g (hg.trans hu)
  have hpos' : ∀ᵐ x ∂carpetMeasure.restrict A, 0 ≤ (u : CarpetLp p) x := by
    filter_upwards [hu, ht.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hx'
    rw [hx, hx']
    exact le_max_right _ _
  have hle : (f : CarpetLp p) ≤ᵐ[carpetMeasure.restrict A] (u : CarpetLp p) := by
    filter_upwards [hu, ht.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hx'
    rw [hx, hx']
    exact le_max_left _ _
  exact ⟨t, u, ht, hu, humin, MinimizesWithExterior.ae_nonneg E hA hG humin hpos',
    MinimizesWithExterior.ae_le E hA hG hf humin hle, htE,
    (E.minimizesWithExterior_wordCellUnion_iff S u).mp humin t hu.symm⟩

end CarpetEnergy.SelfSimilarPEnergy
