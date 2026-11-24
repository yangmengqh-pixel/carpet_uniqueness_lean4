import EnergyRelativeRootSeminorm

/-!
# The graph seminorm for a comparable energy
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- Combine the energy-root seminorm and the ambient Lp norm in an
`ℓ^p` sum. -/
noncomputable def relativeGraphSeminorm (S : Seminorm ℝ E.domain) : Seminorm ℝ E.domain :=
  Seminorm.of (fun f ↦ (S f ^ p + ‖(f : CarpetLp p)‖ ^ p) ^ p⁻¹) (by
    intro f g
    let a (f : E.domain) : Fin 2 → ℝ := ![S f, ‖(f : CarpetLp p)‖]
    have ha (f : E.domain) (i : Fin 2) : 0 ≤ a f i := by
      fin_cases i
      · exact apply_nonneg S f
      · exact norm_nonneg _
    have hsub (i : Fin 2) : a (f + g) i ≤ a f i + a g i := by
      fin_cases i
      · exact S.add_le' f g
      · exact norm_add_le (f : CarpetLp p) (g : CarpetLp p)
    have h := Real.Lp_add_le_of_nonneg (Finset.univ : Finset (Fin 2))
      (f := a f) (g := a g) E.one_lt_p.le (fun i _ ↦ ha f i) (fun i _ ↦ ha g i)
    have h' := (finitePowerSum_mono (zero_lt_one.trans E.one_lt_p) (ha (f + g)) hsub).trans
      (by simpa only [finitePowerSum, one_div] using h)
    simpa only [finitePowerSum, Fin.sum_univ_two, a, Matrix.cons_val_zero, Matrix.cons_val_one] using h') (by
      intro a f
      have hp := zero_lt_one.trans E.one_lt_p
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      change ((|a| * S f) ^ p + ‖a • (f : CarpetLp p)‖ ^ p) ^ p⁻¹ = _
      rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (apply_nonneg _ _),
        Real.mul_rpow (abs_nonneg _) (norm_nonneg _), ← mul_add,
        Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _)
          (add_nonneg (Real.rpow_nonneg (apply_nonneg _ _) _) (Real.rpow_nonneg (norm_nonneg _) _)),
        Real.rpow_rpow_inv (abs_nonneg _) hp.ne'])

theorem relativeGraphSeminorm_apply (S : Seminorm ℝ E.domain) (f : E.domain) :
    E.relativeGraphSeminorm S f = (S f ^ p + ‖(f : CarpetLp p)‖ ^ p) ^ p⁻¹ := rfl

theorem exists_relativeGraphSeminorm_comparison (G : E.domain → ℝ) (S : Seminorm ℝ E.domain)
    (hS : ∀ f, G f = S f ^ p) {A B : ℝ} (hA : 0 < A)
    (hcomp : ∀ f, A * (E.energy f : ℝ) ≤ G f ∧ G f ≤ B * (E.energy f : ℝ)) :
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ), ∀ f,
      a * E.graphSeminorm f ≤ E.relativeGraphSeminorm S f ∧
        E.relativeGraphSeminorm S f ≤ b * E.graphSeminorm f := by
  let α := min A 1
  let β := max B 1
  have hα : 0 < α := lt_min hA one_pos
  have hβ : 0 < β := zero_lt_one.trans_le (le_max_right _ _)
  have hp := zero_lt_one.trans E.one_lt_p
  refine ⟨α ^ p⁻¹, Real.rpow_pos_of_pos hα _, β ^ p⁻¹, Real.rpow_pos_of_pos hβ _, fun f ↦ ?_⟩
  let u := (E.energy f : ℝ)
  let v := ‖(f : CarpetLp p)‖ ^ p
  have hu : 0 ≤ u := NNReal.coe_nonneg _
  have hv : 0 ≤ v := Real.rpow_nonneg (norm_nonneg _) _
  have h₁ : α * (u + v) ≤ G f + v := by
    rw [mul_add]
    exact add_le_add ((mul_le_mul_of_nonneg_right (min_le_left A 1) hu).trans (hcomp f).1)
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right A 1) hv)
  have h₂ : G f + v ≤ β * (u + v) := by
    rw [mul_add]
    exact add_le_add ((hcomp f).2.trans (mul_le_mul_of_nonneg_right (le_max_left B 1) hu))
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_right B 1) hv)
  have hg : 0 ≤ G f := (mul_nonneg hA.le hu).trans (hcomp f).1
  rw [E.graphSeminorm_apply, energyGraphNorm, E.relativeGraphSeminorm_apply, ← hS]
  change α ^ p⁻¹ * (u + v) ^ p⁻¹ ≤ (G f + v) ^ p⁻¹ ∧
    (G f + v) ^ p⁻¹ ≤ β ^ p⁻¹ * (u + v) ^ p⁻¹
  rw [← Real.mul_rpow hα.le (add_nonneg hu hv), ← Real.mul_rpow hβ.le (add_nonneg hu hv)]
  exact ⟨Real.rpow_le_rpow (mul_nonneg hα.le (add_nonneg hu hv)) h₁ (inv_nonneg.mpr hp.le),
    Real.rpow_le_rpow (add_nonneg hg hv) h₂ (inv_nonneg.mpr hp.le)⟩

end CarpetEnergy.SelfSimilarPEnergy
