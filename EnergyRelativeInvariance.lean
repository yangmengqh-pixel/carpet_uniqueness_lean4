import CarpetGammaSymmetry
import EnergySelfSimilarization

/-!
# Homogeneity, constants, and symmetries of the renormalized limit
-/

open Filter Function MeasureTheory
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

section Transform

variable {X I : Type*} [Fintype I]

theorem renormalizationMean_limit_eq_mul_of_transform
    (r : ℝ) (pull : I → X → X) {F G : X → ℝ} (s : X → X) (c : ℝ)
    (π : Equiv.Perm I) (hs : ∀ i x, pull i (s x) = s (pull (π i) x))
    (hF : ∀ x, F (s x) = c * F x) {l : Filter ℕ} [l.NeBot]
    (hlim : ∀ x, Tendsto (fun n ↦ renormalizationMean r pull F n x) l (𝓝 (G x))) :
    ∀ x, G (s x) = c * G x := by
  let T := renormalize r pull
  let H (n : ℕ) := (T^[n]) F
  have hi (n : ℕ) (x : X) : H n (s x) = c * H n x := by
    induction n generalizing x with
    | zero => exact hF x
    | succ n ih =>
      simp only [H, Function.iterate_succ_apply']
      change r * (∑ i, H n (pull i (s x))) = c * (r * ∑ i, H n (pull i x))
      simp only [hs, ih, ← Finset.mul_sum]
      rw [mul_left_comm r c]
      have hsum : ∑ i, H n (pull (π i) x) = ∑ i, H n (pull i x) :=
        Fintype.sum_equiv π _ _ (fun _ ↦ rfl)
      rw [hsum]
  have hm (n : ℕ) (x : X) :
      renormalizationMean r pull F n (s x) = c * renormalizationMean r pull F n x := by
    unfold renormalizationMean
    change (1 / ((n : ℝ) + 1)) * (∑ k ∈ Finset.range (n + 1), H k (s x)) =
      c * ((1 / ((n : ℝ) + 1)) * (∑ k ∈ Finset.range (n + 1), H k x))
    simp only [hi, ← Finset.mul_sum, mul_left_comm (1 / ((n : ℝ) + 1)) c]
  intro x
  apply tendsto_nhds_unique (hlim (s x))
  simpa only [hm] using (hlim x).const_mul c

end Transform

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem pullbackWord_constant (w : List (Fin 8)) (a : ℝ) :
    E.pullbackWord w (⟨constantLp p a, E.constant_mem a⟩ : E.domain) =
      ⟨constantLp p a, E.constant_mem a⟩ := by
  apply Subtype.ext
  apply Lp.ext
  exact (E.pullbackWord_isLpPullback w _).trans
    (((quasiMeasurePreserving_wordMap w).ae_eq_comp (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a)).trans
      (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a).symm)

theorem renormalizedGammaLimit_invariance {j : ℕ → ℕ} {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F)
    {l : Filter ℕ} [l.NeBot] {G : E.domain → ℝ}
    (hlim : ∀ f, Tendsto (fun n ↦ renormalizationMean E.scalingFactor E.pullback
      (fun v : E.domain ↦ (F v).toReal) n f) l (𝓝 (G f))) :
    (∀ a : ℝ, ∀ f, G (a • f) = |a| ^ p * G f) ∧
      (∀ a : ℝ, ∀ f, G (f + ⟨constantLp p a, E.constant_mem a⟩) = G f) ∧
      (∀ σ f, G (E.pullbackSymmetry σ f) = G f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply renormalizationMean_limit_eq_mul_of_transform E.scalingFactor E.pullback
      (fun f : E.domain ↦ a • f) (|a| ^ p) (Equiv.refl _) _ _ hlim
    · intro i f
      exact E.pullbackWord_smul [i] a f
    · intro f
      change (F (a • (f : CarpetLp p))).toReal = _
      rw [hF.discreteCellEnergy_smul (zero_lt_one.trans E.one_lt_p) a f, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _)]
  · intro a f
    let c : E.domain := ⟨constantLp p a, E.constant_mem a⟩
    have h (i : Fin 8) (z : E.domain) : E.pullback i (z + c) = E.pullback i z + c := by
      change E.pullbackWord [i] (z + c) = E.pullbackWord [i] z + c
      rw [E.pullbackWord_add, E.pullbackWord_constant]
    have hF' (z : E.domain) : (F (↑(z + c) : CarpetLp p)).toReal = 1 * (F z).toReal := by
      change (F ((z : CarpetLp p) + constantLp p a)).toReal = _
      rw [hF.discreteCellEnergy_add_constant, one_mul]
    have he := renormalizationMean_limit_eq_mul_of_transform E.scalingFactor E.pullback
      (fun z : E.domain ↦ z + c) 1 (Equiv.refl _) h hF' hlim f
    exact he.trans (one_mul (G f))
  · intro σ f
    obtain ⟨e, he⟩ := exists_carpetSymmetry_cellPerm σ
    have h (i : Fin 8) (z : E.domain) :
        E.pullback i (E.pullbackSymmetry σ z) = E.pullbackSymmetry σ (E.pullback (e i) z) :=
      E.pullbackWord_pullbackSymmetry σ e he [i] z
    have ha (z : E.domain) : (E.pullbackSymmetry σ z : CarpetLp p) = carpetSymmetryLp σ z := by
      apply Lp.ext
      exact (symmetryPullback_isLpPullback σ (z : CarpetLp p)).trans (carpetSymmetryLp_ae (p := p) σ (z : CarpetLp p)).symm
    have hF' (z : E.domain) : (F (E.pullbackSymmetry σ z)).toReal = 1 * (F z).toReal := by
      rw [ha, hF.discreteCellEnergy_carpetSymmetryLp, one_mul]
    have h' := renormalizationMean_limit_eq_mul_of_transform E.scalingFactor E.pullback
      (E.pullbackSymmetry σ) 1 e h hF' hlim f
    exact h'.trans (one_mul (G f))

end SelfSimilarPEnergy

end CarpetEnergy
