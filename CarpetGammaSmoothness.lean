import CarpetGammaHomogeneity
import ScalarPowerSmoothness

/-!
# Uniform symmetric increment through the discrete and Γ-limit energies
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

section Discrete

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

private theorem discreteCellEnergy_symmIncrement {ρ ε t : ℝ} (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (h : ∀ x y : ℝ, |x + t * y| ^ p + |x - t * y| ^ p - 2 * |x| ^ p ≤
      ε * |t| * (|x| ^ p + |y| ^ p))
    (n : ℕ) (f g : CarpetLp p) :
    discreteCellEnergy p ρ n (f + t • g) + discreteCellEnergy p ρ n (f - t • g) ≤
      ENNReal.ofReal (2 + ε * |t|) * discreteCellEnergy p ρ n f +
        ENNReal.ofReal (ε * |t|) * discreteCellEnergy p ρ n g := by
  classical
  let W := Fin n → Fin 8
  let N (w : W) := Finset.univ.filter (fun v : W ↦ v ≠ w ∧
    (range (wordMap (List.ofFn w)) ∩ range (wordMap (List.ofFn v))).Nonempty)
  let d (u : CarpetLp p) (w v : W) :=
    ambientWordMean p (List.ofFn w) u - ambientWordMean p (List.ofFn v) u
  let x (u : CarpetLp p) := ∑ w : W, ∑ v ∈ N w, |d u w v| ^ p
  let a := ρ ^ n / 2
  let b := ε * |t|
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := mul_nonneg hε (abs_nonneg t)
  have hx (u : CarpetLp p) : 0 ≤ x u :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hp (w v : W) : d (f + t • g) w v = d f w v + t * d g w v := by
    dsimp only [d]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hm (w v : W) : d (f - t • g) w v = d f w v - t * d g w v := by
    dsimp only [d]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have ht : x (f + t • g) + x (f - t • g) ≤ (2 + b) * x f + b * x g := by
    simp only [x, hp, hm, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    apply Finset.sum_le_sum
    intro v _
    have hh := h (d f w v) (d g w v)
    dsimp only [b]
    linarith only [hh, show (2 + ε * |t|) * |d f w v| ^ p + ε * |t| * |d g w v| ^ p =
      2 * |d f w v| ^ p + ε * |t| * (|d f w v| ^ p + |d g w v| ^ p) by ring]
  change ENNReal.ofReal (a * x (f + t • g)) + ENNReal.ofReal (a * x (f - t • g)) ≤
    ENNReal.ofReal (2 + b) * ENNReal.ofReal (a * x f) + ENNReal.ofReal b * ENNReal.ofReal (a * x g)
  have h₂b : 0 ≤ 2 + b := by positivity
  rw [← ENNReal.ofReal_add (mul_nonneg ha (hx _)) (mul_nonneg ha (hx _)),
    ← ENNReal.ofReal_mul h₂b, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (mul_nonneg h₂b (mul_nonneg ha (hx _))) (mul_nonneg hb (mul_nonneg ha (hx _)))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = a * (x (f + t • g) + x (f - t • g)) := by ring
    _ ≤ a * ((2 + b) * x f + b * x g) := mul_le_mul_of_nonneg_left ht ha
    _ = _ := by ring

theorem IsGammaLimit.discreteCellEnergy_uniform_symmIncrement {ρ : ℝ} (hp : 1 < p)
    (hρ : 0 ≤ ρ) {j : ℕ → ℕ} {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p ρ (j n)) F) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (f g : CarpetLp p), F f < ∞ → F g < ∞ →
      ∀ t : ℝ, |t| < δ →
        F (f + t • g) + F (f - t • g) ≤
          ENNReal.ofReal (2 + ε * |t|) * F f + ENNReal.ofReal (ε * |t|) * F g := by
  obtain ⟨δ, hδ, h⟩ := exists_abs_rpow_symmetric_increment hp hε
  refine ⟨δ, hδ, fun f g hf hg t ht ↦ ?_⟩
  let P (a : Fin 2 → ℝ≥0∞) :=
    ENNReal.ofReal (2 + ε * |t|) * a 0 + ENNReal.ofReal (ε * |t|) * a 1
  let Q (a : Fin 2 → ℝ≥0∞) := a 0 + a 1
  let G (u : Fin 2 → CarpetLp p) : Fin 2 → CarpetLp p :=
    ![u 0 + t • u 1, u 0 - t • u 1]
  have hP : Continuous P :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp (continuous_apply 0) |>.add
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp (continuous_apply 1))
  have hQ : Continuous Q := (continuous_apply 0).add (continuous_apply 1)
  have hQmono : Monotone Q := fun _ _ hab ↦ add_le_add (hab 0) (hab 1)
  have hG : Continuous G := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun u : Fin 2 → CarpetLp p ↦ u 0 + t • u 1)
      exact (continuous_apply 0).add ((continuous_apply 1).const_smul t)
    · change Continuous (fun u : Fin 2 → CarpetLp p ↦ u 0 - t • u 1)
      exact (continuous_apply 0).sub ((continuous_apply 1).const_smul t)
  have hbound : ∀ n (u : Fin 2 → CarpetLp p),
      Q (fun i ↦ discreteCellEnergy p ρ (j n) (G u i)) ≤ P (fun i ↦ discreteCellEnergy p ρ (j n) (u i)) :=
    fun n u ↦ discreteCellEnergy_symmIncrement hρ hε.le (fun x y ↦ h x y t ht) (j n) (u 0) (u 1)
  have hf' : ∀ i : Fin 2, F (![f, g] i) < ∞ := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  exact hF.finite_contraction_of_approximate P Q hP hQ hQmono (fun _ ↦ G) G
    (fun _ _ u _ hu ↦ (hG.tendsto u).comp hu) hbound ![f, g] hf'

end Discrete

end CarpetEnergy
