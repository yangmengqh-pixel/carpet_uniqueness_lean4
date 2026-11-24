import CarpetDiscreteEnergy
import EnergyGammaTwoPoint
import ScalarPowerMidpoint

/-!
# Midpoint deficits of the discrete energies and their Γ-limits
-/

open Set
open scoped BigOperators ENNReal

namespace CarpetEnergy

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

private theorem discreteCellEnergy_midpoint_deficit_of_scalar {ρ ε C : ℝ} (hρ : 0 ≤ ρ)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (h : ∀ x y : ℝ, |x - y| ^ p + C * |(x + y) / 2| ^ p ≤
      (ε + C / 2) * (|x| ^ p + |y| ^ p))
    (n : ℕ) (f g : CarpetLp p) :
    discreteCellEnergy p ρ n (f - g) + ENNReal.ofReal C * discreteCellEnergy p ρ n ((1 / 2 : ℝ) • (f + g)) ≤
      ENNReal.ofReal (ε + C / 2) * (discreteCellEnergy p ρ n f + discreteCellEnergy p ρ n g) := by
  classical
  let W := Fin n → Fin 8
  let N (w : W) := Finset.univ.filter (fun v : W ↦ v ≠ w ∧
    (range (wordMap (List.ofFn w)) ∩ range (wordMap (List.ofFn v))).Nonempty)
  let d (u : CarpetLp p) (w v : W) :=
    ambientWordMean p (List.ofFn w) u - ambientWordMean p (List.ofFn v) u
  let x (u : CarpetLp p) := ∑ w : W, ∑ v ∈ N w, |d u w v| ^ p
  let a := ρ ^ n / 2
  let b := ε + C / 2
  let m := (1 / 2 : ℝ) • (f + g)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hx (u : CarpetLp p) : 0 ≤ x u :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hsub (w v : W) : d (f - g) w v = d f w v - d g w v := by
    dsimp only [d]
    simp only [map_sub]
    ring
  have hmid (w v : W) : d m w v = (d f w v + d g w v) / 2 := by
    dsimp only [d, m]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have ht : x (f - g) + C * x m ≤ b * (x f + x g) := by
    simp only [x, hsub, hmid, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    apply Finset.sum_le_sum
    intro v _
    exact h (d f w v) (d g w v)
  change ENNReal.ofReal (a * x (f - g)) + ENNReal.ofReal C * ENNReal.ofReal (a * x m) ≤
    ENNReal.ofReal b * (ENNReal.ofReal (a * x f) + ENNReal.ofReal (a * x g))
  have hax (u : CarpetLp p) : 0 ≤ a * x u := mul_nonneg ha (hx u)
  rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_add (hax _) (mul_nonneg hC (hax _)),
    ← ENNReal.ofReal_add (hax _) (hax _), ← ENNReal.ofReal_mul hb]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = a * (x (f - g) + C * x m) := by ring
    _ ≤ a * (b * (x f + x g)) := mul_le_mul_of_nonneg_left ht ha
    _ = _ := by ring

theorem IsGammaLimit.discreteCellEnergy_midpoint_deficit {ρ ε C : ℝ} (hρ : 0 ≤ ρ)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (h : ∀ x y : ℝ, |x - y| ^ p + C * |(x + y) / 2| ^ p ≤
      (ε + C / 2) * (|x| ^ p + |y| ^ p))
    {j : ℕ → ℕ} {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p ρ (j n)) F)
    (f g : CarpetLp p) (hf : F f < ∞) (hg : F g < ∞) :
    F (f - g) + ENNReal.ofReal C * F ((1 / 2 : ℝ) • (f + g)) ≤
      ENNReal.ofReal (ε + C / 2) * (F f + F g) := by
  let U (u : Fin 2 → CarpetLp p) := u 0 - u 1
  let V (u : Fin 2 → CarpetLp p) := (1 / 2 : ℝ) • (u 0 + u 1)
  have hU : Continuous U := (continuous_apply _).sub (continuous_apply _)
  have hV : Continuous V := ((continuous_apply (0 : Fin 2)).add (continuous_apply (1 : Fin 2))).const_smul (1 / 2 : ℝ)
  have hh (n : ℕ) (u : Fin 2 → CarpetLp p) :
      1 * discreteCellEnergy p ρ (j n) (U u) + ENNReal.ofReal C * discreteCellEnergy p ρ (j n) (V u) ≤
        ENNReal.ofReal (ε + C / 2) * discreteCellEnergy p ρ (j n) (u 0) +
          ENNReal.ofReal (ε + C / 2) * discreteCellEnergy p ρ (j n) (u 1) := by
    rw [one_mul, ← mul_add]
    exact discreteCellEnergy_midpoint_deficit_of_scalar hρ hε hC h (j n) (u 0) (u 1)
  have hfin (i : Fin 2) : F (![f, g] i) < ∞ := by
    fin_cases i
    · exact hf
    · exact hg
  have h' := hF.twoPoint_affine_bound U V hU hV ENNReal.one_ne_top
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hh ![f, g] hfin
  rw [one_mul, ← mul_add] at h'
  exact h'

end CarpetEnergy
