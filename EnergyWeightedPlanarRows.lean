import EnergyVariationAffineLimit
import WeightedPlanarTest
import CarpetEnergyRiemannSums

/-!
# Planar row estimates for a stationary harmonic pair
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 2600000 in
/-- The stationary directional variations leave a single weight
variation. Hölder on the cell decomposition bounds it by the
appropriate weighted integral of the test function. -/
theorem abs_weighted_planar_row_le (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (f : E.domain) (hf : E.IsInteriorHarmonic f)
    (g : Fin 2 → E.continuousCore) (μ : Measure CarpetPoints) [IsFiniteMeasure μ]
    (hμ : ∀ n, μ (carpetCellBoundary n) = 0)
    (hstat : ∀ i : Fin 2, ∀ t : ℝ,
      E.energyMeasure (f + t • E.continuousCoreToDomain (g i)) =
        ((E.energy (f + t • E.continuousCoreToDomain (g i)) : NNReal) : ℝ≥0∞) • μ)
    (χ : E.continuousCore) (hχ : ∀ x ∈ carpetOuterBoundary, χ.val x = 0)
    (ω : ℝ → ℝ) (hω : ContDiff ℝ 1 ω) (hω0 : ω 0 = 0)
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) :
    let q := p.conjExponent
    let G := E.continuousCoreTuple g
    |∑ i : Fin 2, E.variation h f (E.continuousCoreToDomain (g i)) *
        ∫ x, ω (χ.val x) * fderiv ℝ φ (G x) (planarDirection i) ∂μ| ≤
      (∫ x, |deriv ω (χ.val x) * φ (G x)| ^ q ∂E.energyMeasure f) ^ q⁻¹ *
        (E.energy (E.continuousCoreToDomain χ) : ℝ) ^ p⁻¹ := by
  classical
  let q := p.conjExponent
  let G := E.continuousCoreTuple g
  let χ₀ := E.continuousCoreToDomain χ
  let u : Fin 3 → E.continuousCore := Fin.cons χ g
  let Φ := weightedPlanarTest ω φ
  have hΦ := contDiff_weightedPlanarTest ω hω φ hφ
  have hu0 (x : CarpetPoints) : E.continuousCoreTuple u x 0 = χ.val x := rfl
  have huTail (x : CarpetPoints) : planarTail (E.continuousCoreTuple u x) = G x := by
    ext i
    change (u i.succ).val x = (g i).val x
    simp only [u, Fin.cons_succ]
  obtain ⟨v, hv⟩ := E.exists_core_comp_contDiff hc u Φ hΦ
  have hvTrace (x : CarpetPoints) (hx : x ∈ carpetOuterBoundary) : v.val x = 0 := by
    rw [hv, show Φ (E.continuousCoreTuple u x) = ω (E.continuousCoreTuple u x 0) *
        φ (planarTail (E.continuousCoreTuple u x)) from rfl,
      hu0, hχ x hx, hω0, zero_mul]
  have hvZero := E.variation_eq_zero_of_interior_harmonic h f hf v hvTrace
  let z := bottomPoint 0
  have hlim := E.tendsto_affineVariationSum h hc f u Φ hΦ v hv z
  rw [hvZero] at hlim
  let Q (i : Fin 2) : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ ω (χ.val x) * fderiv ℝ φ (G x) (planarDirection i),
      (hω.continuous.comp χ.val.continuous).mul
        (((hφ.continuous_fderiv (by norm_num)).comp G.continuous).clm_apply continuous_const)⟩
  let C : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ deriv ω (χ.val x) * φ (G x),
      (((contDiff_one_iff_deriv.mp hω).2).comp χ.val.continuous).mul (hφ.continuous.comp G.continuous)⟩
  let Cq : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ |C x| ^ q,
      C.continuous.abs.rpow_const (fun _ ↦ Or.inr (Real.HolderConjugate.conjExponent E.one_lt_p).symm.nonneg)⟩
  let M (i : Fin 2) := E.variation h f (E.continuousCoreToDomain (g i))
  let X (n : ℕ) := ∑ i : Fin 2, M i * ∑ w : Fin n → Fin 8,
    Q i (wordMap (List.ofFn w) z) * μ.real (range (wordMap (List.ofFn w)))
  let I := ∑ i : Fin 2, M i * ∫ x, Q i x ∂μ
  let Y (n : ℕ) := E.scalingFactor ^ n * ∑ w : Fin n → Fin 8,
    C (wordMap (List.ofFn w) z) *
      E.variation h (E.pullbackWord (List.ofFn w) f) (E.pullbackWord (List.ofFn w) χ₀)
  have hX : Tendsto X atTop (𝓝 I) :=
    tendsto_finsetSum _ (fun i _ ↦ (tendsto_wordCell_riemannSum μ hμ (Q i) z).const_mul (M i))
  have he (n : ℕ) : E.affineVariationSum h f u Φ z n = Y n + X n := by
    unfold affineVariationSum
    simp only [Φ, Fin.sum_univ_succ (n := 2), fderiv_weightedPlanarTest_zero ω hω φ hφ,
      fderiv_weightedPlanarTest_succ ω hω φ hφ, hu0, huTail]
    have huCons0 : u 0 = χ := by simp only [u, Fin.cons_zero]
    have huCons (i : Fin 2) : u i.succ = g i := by simp only [u, Fin.cons_succ]
    simp only [huCons0, huCons]
    rw [Finset.sum_add_distrib, mul_add]
    change Y n + E.scalingFactor ^ n * (∑ w : Fin n → Fin 8,
      ∑ i : Fin 2, Q i (wordMap (List.ofFn w) z) *
        E.variation h (E.pullbackWord (List.ofFn w) f)
          (E.pullbackWord (List.ofFn w) (E.continuousCoreToDomain (g i)))) = Y n + X n
    congr 1
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have hcell := E.variation_word_of_stationary_density h f (E.continuousCoreToDomain (g i))
      μ (hstat i) (List.ofFn w)
    rw [List.length_ofFn] at hcell
    rw [mul_left_comm, hcell]
    dsimp only [M]
    ring
  have hY : Tendsto Y atTop (𝓝 (-I)) := by
    have ht := hlim.sub hX
    have he' : (fun n ↦ E.affineVariationSum h f u Φ z n - X n) = Y := by
      funext n
      rw [he, add_sub_cancel_right]
    rw [he', zero_sub] at ht
    exact ht
  let T (n : ℕ) := ∑ w : Fin n → Fin 8,
    Cq (wordMap (List.ofFn w) z) * (E.energyMeasure f).real (range (wordMap (List.ofFn w)))
  let J := ∫ x, Cq x ∂E.energyMeasure f
  have hT : Tendsto T atTop (𝓝 J) :=
    tendsto_wordCell_riemannSum (E.energyMeasure f)
      (E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero f) Cq z
  have hnonneg : 0 ≤ J := integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hbound (n : ℕ) : |Y n| ≤ T n ^ q⁻¹ * (E.energy χ₀ : ℝ) ^ p⁻¹ :=
    E.abs_word_variation_sum_le (Real.HolderConjugate.conjExponent E.one_lt_p) h n f χ₀
      (fun w ↦ C (wordMap (List.ofFn w) z))
  have hpower := ((Real.continuous_rpow_const (inv_nonneg.mpr
    (Real.HolderConjugate.conjExponent E.one_lt_p).symm.nonneg)).tendsto J).comp hT
  have habs := (continuous_abs.tendsto (-I)).comp hY
  have hres := le_of_tendsto_of_tendsto habs (hpower.mul_const ((E.energy χ₀ : ℝ) ^ p⁻¹))
    (Eventually.of_forall hbound)
  rw [abs_neg] at hres
  exact hres

end CarpetEnergy.SelfSimilarPEnergy
