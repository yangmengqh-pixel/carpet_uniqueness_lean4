import CarpetGammaSmoothness
import EnergySelfSimilarization

/-!
# Uniform symmetric increments after cell renormalization
-/

open Filter Function
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

/-- A symmetric increment bound with a modulus shared by all bases and
directions. -/
def HasUniformSymmetricIncrement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (F : X → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x y : X, ∀ t : ℝ, |t| < δ →
    F (x + t • y) + F (x - t • y) ≤ (2 + ε * |t|) * F x + ε * |t| * F y

section

variable {X I : Type*} [AddCommGroup X] [Module ℝ X] [Fintype I]

private theorem symmetricIncrement_apply_pos_sum {J : Type*} (s : Finset J)
    (U : J → X → ℝ) {b t : ℝ}
    (h : ∀ j ∈ s, ∀ x y : X,
      U j (x + t • y) + U j (x - t • y) ≤ (2 + b) * U j x + b * U j y)
    (x y : X) :
    (∑ j ∈ s, U j (x + t • y)) + (∑ j ∈ s, U j (x - t • y)) ≤
      (2 + b) * (∑ j ∈ s, U j x) + b * (∑ j ∈ s, U j y) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j hj ↦ h j hj x y)

theorem HasUniformSymmetricIncrement.of_renormalizationMean_limit
    {r : ℝ} (hr : 0 ≤ r) (pull : I → X →ₗ[ℝ] X) {F G : X → ℝ}
    (hF : HasUniformSymmetricIncrement F) {l : Filter ℕ} [l.NeBot]
    (hlim : ∀ x, Tendsto (fun n ↦ renormalizationMean r (fun i ↦ pull i) F n x) l (𝓝 (G x))) :
    HasUniformSymmetricIncrement G := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hF ε hε
  refine ⟨δ, hδ, fun x y t ht ↦ ?_⟩
  let b := ε * |t|
  let T : (X → ℝ) → X → ℝ := renormalize r (fun i ↦ pull i)
  let H (n : ℕ) := (T^[n]) F
  have hi (n : ℕ) (x y : X) :
      H n (x + t • y) + H n (x - t • y) ≤ (2 + b) * H n x + b * H n y := by
    induction n generalizing x y with
    | zero => exact h x y t ht
    | succ n ih =>
      simp only [H, Function.iterate_succ_apply']
      unfold T renormalize
      simp only [← mul_add r, mul_left_comm (2 + b) r, mul_left_comm b r]
      apply mul_le_mul_of_nonneg_left _ hr
      apply symmetricIncrement_apply_pos_sum Finset.univ (fun i z ↦ H n (pull i z))
      intro i _ a c
      rw [map_add, map_sub, map_smul]
      exact ih (pull i a) (pull i c)
  have hmean (n : ℕ) :
      renormalizationMean r (fun i ↦ pull i) F n (x + t • y) +
        renormalizationMean r (fun i ↦ pull i) F n (x - t • y) ≤
        (2 + b) * renormalizationMean r (fun i ↦ pull i) F n x +
          b * renormalizationMean r (fun i ↦ pull i) F n y := by
    let a := 1 / ((n : ℝ) + 1)
    unfold renormalizationMean
    change a * (∑ j ∈ Finset.range (n + 1), H j (x + t • y)) +
      a * (∑ j ∈ Finset.range (n + 1), H j (x - t • y)) ≤
      (2 + b) * (a * ∑ j ∈ Finset.range (n + 1), H j x) +
        b * (a * ∑ j ∈ Finset.range (n + 1), H j y)
    simp only [← mul_add a, mul_left_comm (2 + b) a, mul_left_comm b a]
    apply mul_le_mul_of_nonneg_left _ (by dsimp only [a]; positivity)
    exact symmetricIncrement_apply_pos_sum _ H (fun j _ ↦ hi j) x y
  exact le_of_tendsto_of_tendsto ((hlim _).add (hlim _))
    (((hlim x).const_mul (2 + b)).add ((hlim y).const_mul b)) (Eventually.of_forall hmean)

end

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

theorem gammaLimit_toReal_hasUniformSymmetricIncrement
    {j : ℕ → ℕ} (hj : StrictMono j) {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F) :
    HasUniformSymmetricIncrement (fun f : E.domain ↦ (F f).toReal) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hF.discreteCellEnergy_uniform_symmIncrement E.one_lt_p
    E.isScalingFactor_scalingFactor.1.le hε
  have ht (f : E.domain) : F f ≠ ⊤ := by
    have heq := IsGammaLimit.discreteLimit_domain_eq E hj hF
    have hm : (f : CarpetLp p) ∈ {u | F u < ∞} := heq.symm ▸ f.property
    exact (show F f < ∞ from hm).ne
  refine ⟨δ, hδ, fun f g t htδ ↦ ?_⟩
  have he := h f g (lt_top_iff_ne_top.mpr (ht f)) (lt_top_iff_ne_top.mpr (ht g)) t htδ
  change F (↑(f + t • g) : CarpetLp p) + F (↑(f - t • g) : CarpetLp p) ≤ _ at he
  have hf : (ENNReal.ofReal (2 + ε * |t|) * F f +
      ENNReal.ofReal (ε * |t|) * F g) ≠ ∞ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ht f), ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ht g)⟩
  have hh := ENNReal.toReal_mono hf he
  rwa [ENNReal.toReal_add (ht _) (ht _), ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ht f)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ht g)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 + ε * |t|),
    ENNReal.toReal_ofReal (mul_nonneg hε.le (abs_nonneg _))] at hh

theorem exists_selfSimilarized_discreteLimit_with_uniform_symmetric_increment :
    ∃ G : E.domain → ℝ,
      (∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ f, A * (E.energy f : ℝ) ≤ G f ∧ G f ≤ B * (E.energy f : ℝ)) ∧
      (∀ f, G f = E.scalingFactor * ∑ i, G (E.pullback i f)) ∧
      HasUniformSymmetricIncrement G := by
  obtain ⟨j, F, l, G, A, hA, B, hB, hj, hF, hl₀, _, hcomp, hlim, he⟩ :=
    E.exists_selfSimilarized_discreteLimit
  let : l.NeBot := hl₀
  let pull (i : Fin 8) : E.domain →ₗ[ℝ] E.domain :=
    { toFun := E.pullback i
      map_add' := fun f g ↦ E.pullbackWord_add [i] f g
      map_smul' := fun a f ↦ E.pullbackWord_smul [i] a f }
  exact ⟨G, ⟨A, hA, B, hB, hcomp⟩, he,
    HasUniformSymmetricIncrement.of_renormalizationMean_limit E.isScalingFactor_scalingFactor.1.le
      pull (E.gammaLimit_toReal_hasUniformSymmetricIncrement hj hF) hlim⟩

end SelfSimilarPEnergy

end CarpetEnergy
