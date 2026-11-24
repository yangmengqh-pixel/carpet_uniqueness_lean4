import EnergyCoreAffineApproximation
import EnergyVariationHolder

/-!
# First variation of a smooth composition as a cell limit
-/

open Filter Function Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The affine first-variation sums associated with sampling a smooth
test on each word cell. -/
noncomputable def affineVariationSum (h : E.HasLinearFirstVariations)
    {m : ℕ} (f : E.domain) (u : Fin m → E.continuousCore)
    (φ : (Fin m → ℝ) → ℝ) (z : CarpetPoints) (n : ℕ) : ℝ :=
  E.scalingFactor ^ n * ∑ w : Fin n → Fin 8,
    ∑ i : Fin m, fderiv ℝ φ (E.continuousCoreTuple u (wordMap (List.ofFn w) z)) (Pi.single i 1) *
      E.variation h (E.pullbackWord (List.ofFn w) f)
        (E.pullbackWord (List.ofFn w) (E.continuousCoreToDomain (u i)))

set_option maxHeartbeats 2300000 in
/-- Uniform first-order approximation on shrinking cells allows the
derivative of a smooth composition to be taken in the sum of cell
variations. -/
theorem tendsto_affineVariationSum (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    {m : ℕ} (f : E.domain) (u : Fin m → E.continuousCore)
    (φ : (Fin m → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (v : E.continuousCore)
    (hv : ∀ x, v.val x = φ (E.continuousCoreTuple u x)) (z : CarpetPoints) :
    Tendsto (E.affineVariationSum h f u φ z) atTop
      (𝓝 (E.variation h f (E.continuousCoreToDomain v))) := by
  classical
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent E.one_lt_p
  let U := E.continuousCoreTuple u
  obtain ⟨R, hR⟩ := E.exists_closedBall_coreTuple u
  have hU := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous U.continuous)
  let B := (E.energy f : ℝ) ^ q⁻¹ *
    (∑ j : Fin m, (E.energy (E.continuousCoreToDomain (u j)) : ℝ)) ^ p⁻¹
  have hB : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)
    (Real.rpow_nonneg (Finset.sum_nonneg (fun _ _ ↦ NNReal.coe_nonneg _)) _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let b : ℝ≥0 := ⟨ε / (B + 1), div_nonneg hε.le (by positivity)⟩
  have hb : 0 < b := by exact_mod_cast (div_pos hε (by positivity) : 0 < ε / (B + 1))
  obtain ⟨δ, hδ, hext⟩ := exists_uniform_lipschitz_extension_of_affine_remainder φ hφ R hb
  obtain ⟨r, hr, hdist⟩ := hU δ hδ
  have hdiam : Tendsto (fun n : ℕ ↦ (1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_const
        (diam (univ : Set CarpetPoints))
  filter_upwards [hdiam.eventually_lt_const hr] with n hn
  let W := Fin n → Fin 8
  let wList (w : W) := List.ofFn w
  let point (w : W) := wordMap (wList w) z
  let D (w : W) := fderiv ℝ φ (U (point w))
  let pulls (w : W) (i : Fin m) := E.wordPullbackCore (wList w) (u i)
  let vpull (w : W) := E.wordPullbackCore (wList w) v
  let f' (w : W) := E.pullbackWord (wList w) f
  let c := E.scalingFactor ^ n
  have hc₀ : 0 ≤ c := pow_nonneg E.isScalingFactor_scalingFactor.1.le _
  let a (w : W) := c * (E.energy (f' w) : ℝ)
  let d (w : W) := c * ∑ i : Fin m, (E.energy (E.continuousCoreToDomain (pulls w i)) : ℝ)
  have ha (w : W) : 0 ≤ a w := mul_nonneg hc₀ (NNReal.coe_nonneg _)
  have hd (w : W) : 0 ≤ d w := mul_nonneg hc₀ (Finset.sum_nonneg (fun _ _ ↦ NNReal.coe_nonneg _))
  have hs₁ : (∑ w, a w) = (E.energy f : ℝ) := by
    dsimp only [a, f', wList, c]
    rw [← Finset.mul_sum, ← E.energy_eq_sum_words n f]
  have hs₂ : (∑ w, d w) = ∑ i : Fin m, (E.energy (E.continuousCoreToDomain (u i)) : ℝ) := by
    simp only [d, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pulls, E.continuousCoreToDomain_wordPullbackCore, wList, c]
    rw [← Finset.mul_sum, ← E.energy_eq_sum_words n (E.continuousCoreToDomain (u i))]
  have herror (w : W) :
      let e := E.variation h (f' w)
        (E.continuousCoreToDomain (vpull w - E.linearCoreTuple (D w) (pulls w)))
      c * |e| ≤ (b : ℝ) * (a w ^ q⁻¹ * d w ^ p⁻¹) := by
    have hRw : U (point w) ∈ closedBall 0 R := hR _
    obtain ⟨ψ, hψ, hEq⟩ := hext (U (point w)) hRw
    have hval (x : CarpetPoints) :
        (vpull w).val x = φ (E.continuousCoreTuple (pulls w) x) := hv (wordMap (wList w) x)
    have hvsmall (x : CarpetPoints) :
        E.continuousCoreTuple (pulls w) x ∈ closedBall (U (point w)) δ := by
      change dist (U (wordMap (wList w) x)) (U (point w)) ≤ δ
      exact (hdist ((wordMap_dist_le n w (mem_range_self x) (mem_range_self z)).trans_lt hn)).le
    have hr := E.rootSeminorm_affine_remainder_le hc (pulls w) (vpull w) φ (D w)
      hval hvsmall ψ hb hψ hEq
    have hl := E.abs_variation_le h (f' w)
      (E.continuousCoreToDomain (vpull w - E.linearCoreTuple (D w) (pulls w)))
    have hroot := Real.rpow_nonneg (apply_nonneg E.rootSeminorm (f' w)) (p - 1)
    have hbnd := hl.trans (mul_le_mul_of_nonneg_left hr hroot)
    rw [E.rootSeminorm_rpow_conj hpq] at hbnd
    simp only [finitePowerSum, E.rootSeminorm_rpow_eq_energy] at hbnd
    have hsum : 0 ≤ ∑ i : Fin m, (E.energy (E.continuousCoreToDomain (pulls w i)) : ℝ) :=
      Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _
    have hpows := weighted_root_product_eq_mass_product hpq hc₀
      (NNReal.coe_nonneg (E.energy (f' w))) hsum
    dsimp only
    calc
      _ ≤ c * ((E.energy (f' w) : ℝ) ^ q⁻¹ *
        ((b : ℝ) * (∑ i, (E.energy (E.continuousCoreToDomain (pulls w i)) : ℝ)) ^ p⁻¹)) :=
        mul_le_mul_of_nonneg_left hbnd hc₀
      _ = (b : ℝ) * (c * ((E.energy (f' w) : ℝ) ^ q⁻¹ *
        (∑ i, (E.energy (E.continuousCoreToDomain (pulls w i)) : ℝ)) ^ p⁻¹)) := by ring
      _ = _ := by rw [hpows]
  let V (w : W) := E.variation h (f' w)
    (E.continuousCoreToDomain (vpull w - E.linearCoreTuple (D w) (pulls w)))
  have htotal : E.variation h f (E.continuousCoreToDomain v) - E.affineVariationSum h f u φ z n =
      c * ∑ w, V w := by
    rw [E.variation_eq_sum_words h n f (E.continuousCoreToDomain v)]
    unfold affineVariationSum
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    simp only [V, vpull, f', wList, pulls, D, point, U, linearCoreTuple, map_sub, map_sum, map_smul,
      smul_eq_mul, E.continuousCoreToDomain_wordPullbackCore]
  have hbound : |c * ∑ w, V w| ≤ (b : ℝ) * B := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [abs_mul, abs_of_nonneg hc₀]
    refine (Finset.sum_le_sum (fun w _ ↦ herror w)).trans ?_
    rw [← Finset.mul_sum]
    have h := sum_abs_mul_mass_rpow_le hpq a d (fun _ ↦ (1 : ℝ)) ha hd
    simp only [abs_one, one_mul, Real.one_rpow, hs₁, hs₂] at h
    exact mul_le_mul_of_nonneg_left h b.coe_nonneg
  have hbε : (b : ℝ) * B < ε := by
    change ε / (B + 1) * B < ε
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ (by positivity : 0 < B + 1)).mpr (by linarith)
  rw [dist_comm, Real.dist_eq, htotal]
  exact hbound.trans_lt hbε

end CarpetEnergy.SelfSimilarPEnergy
