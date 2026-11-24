import CarpetGammaMidpoint
import EnergySelfSimilarization

/-!
# Midpoint deficits survive cell renormalization
-/

open Filter Function Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

section Renormalization

variable {X I : Type*} [AddCommGroup X] [Module ℝ X] [Fintype I]

theorem renormalizationMean_limit_midpoint_deficit
    {r ε C : ℝ} (hr : 0 ≤ r) (pull : I → X →ₗ[ℝ] X) {F G : X → ℝ}
    (hF : ∀ x y, F (x - y) + C * F ((1 / 2 : ℝ) • (x + y)) ≤
      (ε + C / 2) * (F x + F y)) {l : Filter ℕ} [l.NeBot]
    (hlim : ∀ x, Tendsto (fun n ↦ renormalizationMean r (fun i ↦ pull i) F n x) l (𝓝 (G x))) :
    ∀ x y, G (x - y) + C * G ((1 / 2 : ℝ) • (x + y)) ≤
      (ε + C / 2) * (G x + G y) := by
  let b := ε + C / 2
  let T : (X → ℝ) → X → ℝ := renormalize r (fun i ↦ pull i)
  let H (n : ℕ) := (T^[n]) F
  have hi (n : ℕ) (x y : X) :
      H n (x - y) + C * H n ((1 / 2 : ℝ) • (x + y)) ≤ b * (H n x + H n y) := by
    induction n generalizing x y with
    | zero => exact hF x y
    | succ n ih =>
      simp only [H, Function.iterate_succ_apply']
      unfold T renormalize
      simp only [map_sub, map_smul, map_add, ← mul_add r, mul_left_comm C r, mul_left_comm b r]
      apply mul_le_mul_of_nonneg_left _ hr
      change (∑ i, H n (pull i x - pull i y)) +
        C * (∑ i, H n ((1 / 2 : ℝ) • (pull i x + pull i y))) ≤
        b * ((∑ i, H n (pull i x)) + ∑ i, H n (pull i y))
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ ↦ ih (pull i x) (pull i y))
  intro x y
  let m := (1 / 2 : ℝ) • (x + y)
  have hm (n : ℕ) :
      renormalizationMean r (fun i ↦ pull i) F n (x - y) +
        C * renormalizationMean r (fun i ↦ pull i) F n m ≤
      b * (renormalizationMean r (fun i ↦ pull i) F n x +
        renormalizationMean r (fun i ↦ pull i) F n y) := by
    let a := 1 / ((n : ℝ) + 1)
    unfold renormalizationMean
    change a * (∑ k ∈ Finset.range (n + 1), H k (x - y)) +
      C * (a * ∑ k ∈ Finset.range (n + 1), H k m) ≤
      b * (a * (∑ k ∈ Finset.range (n + 1), H k x) +
        a * (∑ k ∈ Finset.range (n + 1), H k y))
    simp only [← mul_add a, mul_left_comm C a, mul_left_comm b a]
    apply mul_le_mul_of_nonneg_left _ (by dsimp only [a]; positivity)
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun k _ ↦ hi k x y)
  exact le_of_tendsto_of_tendsto ((hlim (x - y)).add ((hlim m).const_mul C))
    (((hlim x).add (hlim y)).const_mul b) (Eventually.of_forall hm)

end Renormalization

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

theorem renormalizedGammaLimit_midpoint_deficit
    {j : ℕ → ℕ} (hj : StrictMono j) {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F)
    {l : Filter ℕ} [l.NeBot] {G : E.domain → ℝ}
    (hlim : ∀ f, Tendsto (fun n ↦ renormalizationMean E.scalingFactor E.pullback
      (fun v : E.domain ↦ (F v).toReal) n f) l (𝓝 (G f)))
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (h : ∀ x y : ℝ, |x - y| ^ p + C * |(x + y) / 2| ^ p ≤
      (ε + C / 2) * (|x| ^ p + |y| ^ p)) :
    ∀ f g, G (f - g) + C * G ((1 / 2 : ℝ) • (f + g)) ≤
      (ε + C / 2) * (G f + G g) := by
  let pull (i : Fin 8) : E.domain →ₗ[ℝ] E.domain :=
    { toFun := E.pullback i
      map_add' := fun f g ↦ E.pullbackWord_add [i] f g
      map_smul' := fun a f ↦ E.pullbackWord_smul [i] a f }
  apply renormalizationMean_limit_midpoint_deficit E.isScalingFactor_scalingFactor.1.le pull _ hlim
  intro f g
  have hfinite (z : E.domain) : F z ≠ ∞ := by
    have heq := IsGammaLimit.discreteLimit_domain_eq E hj hF
    have hm : (z : CarpetLp p) ∈ {u | F u < ∞} := heq.symm ▸ z.property
    exact (show F z < ∞ from hm).ne
  have he := hF.discreteCellEnergy_midpoint_deficit E.isScalingFactor_scalingFactor.1.le hε hC h f g
    (lt_top_iff_ne_top.mpr (hfinite f)) (lt_top_iff_ne_top.mpr (hfinite g))
  let m := (1 / 2 : ℝ) • (f + g)
  change F (↑(f - g) : CarpetLp p) + ENNReal.ofReal C * F (↑m : CarpetLp p) ≤ _ at he
  have hsum := ENNReal.add_ne_top.mpr ⟨hfinite f, hfinite g⟩
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum) he
  rw [ENNReal.toReal_add (hfinite (f - g)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite m)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add (hfinite f) (hfinite g),
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal (by positivity : 0 ≤ ε + C / 2)] at hh
  exact hh

end SelfSimilarPEnergy

end CarpetEnergy
