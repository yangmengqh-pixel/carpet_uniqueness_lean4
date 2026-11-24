import WeightedDiscreteMixedContraction
import EnergyGammaFiniteContraction
import CarpetLpTuple

/-!
# Generalized contractions of the limiting carpet energy

Cell lifting commutes with the transformed discrete averages.
Synchronized recovery, the graph mixed inequality, and convergence of
the lifts pass every finite-exponent generalized contraction through
the Γ-limit.
-/

open Filter Function Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy

/-- The power-sum expression on extended nonnegative values. -/
noncomputable def extendedFinitePowerSum {I : Type*} [Fintype I]
    (r : ℝ) (a : I → ℝ≥0∞) : ℝ≥0∞ := (∑ i, a i ^ r) ^ r⁻¹

theorem continuous_extendedFinitePowerSum {I : Type*} [Fintype I] (r : ℝ) :
    Continuous (extendedFinitePowerSum (I := I) r) := by
  apply ENNReal.continuous_rpow_const.comp
  exact continuous_finsetSum _ fun i _ ↦ ENNReal.continuous_rpow_const.comp (continuous_apply i)

theorem monotone_extendedFinitePowerSum {I : Type*} [Fintype I] {r : ℝ} (hr : 0 ≤ r) :
    Monotone (extendedFinitePowerSum (I := I) r) := by
  intro a b h
  exact ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ ↦ ENNReal.rpow_le_rpow (h i) hr)
    (inv_nonneg.mpr hr)

theorem extendedFinitePowerSum_ofReal {I : Type*} [Fintype I] {r : ℝ} (hr : 0 ≤ r)
    (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    extendedFinitePowerSum r (fun i ↦ ENNReal.ofReal (a i)) =
      ENNReal.ofReal (finitePowerSum r a) := by
  unfold extendedFinitePowerSum finitePowerSum
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (ha _) hr]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ Real.rpow_nonneg (ha i) _),
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i) _)
      (inv_nonneg.mpr hr)]

theorem le_extendedFinitePowerSum {I : Type*} [Fintype I] {r : ℝ} (hr : 0 < r)
    (a : I → ℝ≥0∞) (i : I) : a i ≤ extendedFinitePowerSum r a := by
  calc
    a i = (a i ^ r) ^ r⁻¹ := by rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]
    _ ≤ _ := ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun j : I ↦ a j ^ r) (fun _ _ ↦ bot_le) (Finset.mem_univ i))
      (inv_nonneg.mpr hr.le)

theorem extendedFinitePowerSum_lt_top {I : Type*} [Fintype I] {r : ℝ} (hr : 0 ≤ r)
    (a : I → ℝ≥0∞) (ha : ∀ i, a i < ∞) : extendedFinitePowerSum r a < ∞ := by
  apply ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hr)
  exact ENNReal.sum_ne_top.mpr fun i _ ↦ ENNReal.rpow_ne_top_of_nonneg hr (ha i).ne

variable {I O : Type*} [Fintype I] [Fintype O]

private theorem discreteCellEnergy_ne_top {p ρ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (n : ℕ) (u : CarpetLp p) : discreteCellEnergy p ρ n u ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Generalized p-contraction for finite exponent pairs in any
subsequential Γ-limit of the rescaled carpet graph energies. -/
theorem IsGammaLimit.discreteCellEnergy_mixed_contraction
    {p ρ q₁ q₂ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p) (hρ : 0 ≤ ρ)
    (h₁ : 0 < q₁) (h₁p : q₁ ≤ p) (h₂p : p ≤ q₂)
    {j : ℕ → ℕ} (hj : StrictMono j) {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p ρ (j n)) F)
    (T : (I → ℝ) → O → ℝ)
    (hT : ∀ x y, finitePowerSum q₂ (fun i ↦ |T x i - T y i|) ≤
        finitePowerSum q₁ (fun i ↦ |x i - y i|))
    {L : O → ℝ≥0} (hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i) (h0 : ∀ i, T 0 i = 0)
    (f : I → CarpetLp p) (hf : ∀ i, F (f i) < ∞) :
    let Tf := pointwiseLp T hLip h0 f
    (∀ i, F (Tf i) < ∞) ∧
      extendedFinitePowerSum (q₂ / p) (fun i ↦ F (Tf i)) ≤
        extendedFinitePowerSum (q₁ / p) (fun i ↦ F (f i)) := by
  have hp₀ := zero_lt_one.trans_le hp
  have h₂ := hp₀.trans_le h₂p
  let G := pointwiseLp (p := p) T hLip h0
  let Gₙ (n : ℕ) (u : I → CarpetLp p) := G (fun i ↦ cellAveraging p (j n) (u i))
  have hlim (k : ℕ → ℕ) (u : ℕ → I → CarpetLp p) (g : I → CarpetLp p)
      (hk : Tendsto k atTop atTop) (hu : Tendsto u atTop (𝓝 g)) :
      Tendsto (fun n ↦ Gₙ (k n) (u n)) atTop (𝓝 (G g)) := by
    have hh (i : I) := cellAveraging_tendsto_of_tendsto hp (hj.tendsto_atTop.comp hk)
      (tendsto_pi_nhds.mp hu i)
    exact ((continuous_pointwiseLp T hLip h0).tendsto g).comp (tendsto_pi_nhds.mpr hh)
  have hcomp (n : ℕ) (u : I → CarpetLp p) :
      extendedFinitePowerSum (q₂ / p) (fun i ↦ discreteCellEnergy p ρ (j n) (Gₙ n u i)) ≤
        extendedFinitePowerSum (q₁ / p) (fun i ↦ discreteCellEnergy p ρ (j n) (u i)) := by
    have h := CarpetEnergy.discreteCellEnergy_mixed_contraction hp₀ hρ h₁ h₁p h₂p (j n) T hT u (Gₙ n u)
      (fun w i ↦ ambientWordMean_pointwiseLp_cellAveraging T hLip h0 (j n) u w i)
    have ho := ENNReal.ofReal_le_ofReal h
    rw [← extendedFinitePowerSum_ofReal (div_nonneg h₂.le hp₀.le) _
      (fun _ ↦ ENNReal.toReal_nonneg),
      ← extendedFinitePowerSum_ofReal (div_nonneg h₁.le hp₀.le) _ (fun _ ↦ ENNReal.toReal_nonneg)] at ho
    simp only [ENNReal.ofReal_toReal (discreteCellEnergy_ne_top _ _)] at ho
    exact ho
  have h := hF.finite_contraction_of_approximate
    (extendedFinitePowerSum (q₁ / p)) (extendedFinitePowerSum (q₂ / p))
    (continuous_extendedFinitePowerSum _) (continuous_extendedFinitePowerSum _)
    (monotone_extendedFinitePowerSum (div_nonneg h₂.le hp₀.le)) Gₙ G hlim hcomp f hf
  exact ⟨fun i ↦ (le_extendedFinitePowerSum (div_pos h₂ hp₀) _ i).trans_lt
      (h.trans_lt (extendedFinitePowerSum_lt_top (div_nonneg h₁.le hp₀.le) _ hf)), h⟩

end CarpetEnergy
