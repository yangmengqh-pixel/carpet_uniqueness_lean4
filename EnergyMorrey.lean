import EnergyAdjacentCellMeans
import CarpetAddressMeasure

/-!
# Morrey bounds when the renormalization factor exceeds one

Consecutive word averages are controlled by the spectral gap. When
`ρ > 1` their pointwise differences are summable down every address,
which bounds the oscillation of a continuous domain function.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem exists_wordMean_child_gap :
    ∃ C > (0 : ℝ), ∀ (f : E.domain) (w : List (Fin 8)) (i : Fin 8),
      |E.wordMean (w ++ [i]) f - E.wordMean w f| ≤ C * E.rootSeminorm (E.pullbackWord w f) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨D, hD, hgap⟩ := E.exists_spectral_gap
  let C := D ^ p⁻¹
  have hC : 0 < C := Real.rpow_pos_of_pos hD _
  refine ⟨8 * C, by positivity, fun f w i ↦ ?_⟩
  let g := E.pullbackWord w f
  let a := E.wordMean w f
  let v := (g : CarpetLp p) - constantLp p a
  let A := range (cellMap i)
  let T : CarpetLp p →L[ℝ] ℝ := lpSetIntegral A
  have hT : |T v| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le A v
  have hconst : T (constantLp p a) = (8 : ℝ)⁻¹ * a := by
    change (∫ x in A, (constantLp p a) x ∂carpetMeasure) = _
    have heq : ((constantLp p a : CarpetLp p) : CarpetPoints → ℝ) =ᵐ[carpetMeasure.restrict A] fun _ ↦ a :=
      (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a).filter_mono (ae_mono Measure.restrict_le_self)
    rw [integral_congr_ae heq, integral_const, Measure.real,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
    have he : carpetMeasure A = (8 : ℝ≥0∞)⁻¹ := by
      simpa only [wordMap, comp_id, List.length_singleton, pow_one] using carpetMeasure_range_wordMap [i]
    rw [he, ENNReal.toReal_inv]
    norm_num
  have hmean : T (g : CarpetLp p) = (8 : ℝ)⁻¹ * E.wordMean (w ++ [i]) f := by
    have h := E.setIntegral_wordMap_eq_wordMean [i] g
    change (∫ x in A, (g : CarpetLp p) x ∂carpetMeasure) =
      (8 : ℝ)⁻¹ * E.wordMean (w ++ [i]) f
    simpa only [List.length_singleton, pow_one, wordMap, comp_id, wordMean,
      E.pullbackWord_append] using h
  have he : T v = (8 : ℝ)⁻¹ * (E.wordMean (w ++ [i]) f - a) := by
    dsimp only [v]
    rw [map_sub, hmean, hconst, mul_sub]
  have hnorm : ‖v‖ ≤ C * E.rootSeminorm g := by
    rw [E.rootSeminorm_apply, ← Real.mul_rpow hD.le (NNReal.coe_nonneg (E.energy g))]
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) (hgap g)
      (inv_nonneg.mpr hp.le)
    rw [Real.rpow_rpow_inv (norm_nonneg _) hp.ne'] at h
    exact h
  change |E.wordMean (w ++ [i]) f - a| ≤ _
  rw [he, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (8 : ℝ)⁻¹)] at hT
  have hh := hT.trans hnorm
  linarith

private theorem addressPrefix_ofFn_succ (n : ℕ) (s : Addresses) :
    List.ofFn (addressPrefix (n + 1) s) = List.ofFn (addressPrefix n s) ++ [s n] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

/-- The global oscillation bound for continuous domain functions in the
case `ρ > 1`. -/
theorem exists_sup_sub_mean_le_rootSeminorm (hρ : 1 < E.scalingFactor) :
    ∃ C > (0 : ℝ), ∀ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain) x,
      |f x - E.wordMean [] ⟨continuousLp p f, hf⟩| ≤ C * E.rootSeminorm ⟨continuousLp p f, hf⟩ := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨D, hD, hchild⟩ := E.exists_wordMean_child_gap
  let q := E.scalingFactor⁻¹ ^ p⁻¹
  have hq₀ : 0 ≤ q := Real.rpow_nonneg (inv_nonneg.mpr (zero_le_one.trans hρ.le)) _
  have hq₁ : q < 1 := Real.rpow_lt_one (inv_nonneg.mpr (zero_le_one.trans hρ.le))
    (inv_lt_one_of_one_lt₀ hρ) (inv_pos.mpr hp)
  refine ⟨D * (1 - q)⁻¹, mul_pos hD (inv_pos.mpr (sub_pos.mpr hq₁)), fun f hf x ↦ ?_⟩
  let u : E.domain := ⟨continuousLp p f, hf⟩
  obtain ⟨s, rfl⟩ := surjective_coding x
  let w (n : ℕ) := List.ofFn (addressPrefix n s)
  let m (n : ℕ) := E.wordMean (w n) u
  have hR (n : ℕ) : E.rootSeminorm (E.pullbackWord (w n) u) ≤ q ^ n * E.rootSeminorm u := by
    have he := E.pullbackWord_energy_le (w n) u
    have hlen : (w n).length = n := List.length_ofFn
    rw [hlen] at he
    rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
    apply (Real.rpow_le_rpow (NNReal.coe_nonneg _) he (inv_nonneg.mpr hp.le)).trans_eq
    have hρ₀ := zero_le_one.trans hρ.le
    rw [← inv_pow, Real.mul_rpow (pow_nonneg (inv_nonneg.mpr hρ₀) _) (NNReal.coe_nonneg (E.energy u)),
      ← Real.rpow_natCast_mul (inv_nonneg.mpr hρ₀), mul_comm (n : ℝ),
      Real.rpow_mul_natCast (inv_nonneg.mpr hρ₀)]
  have hstep (n : ℕ) : |m (n + 1) - m n| ≤ D * (q ^ n * E.rootSeminorm u) := by
    have he : w (n + 1) = w n ++ [s n] := addressPrefix_ofFn_succ n s
    change |E.wordMean (w (n + 1)) u - E.wordMean (w n) u| ≤ _
    rw [he]
    exact (hchild u (w n) (s n)).trans (mul_le_mul_of_nonneg_left (hR n) hD.le)
  have hfinite (n : ℕ) : |m n - m 0| ≤ D * (1 - q)⁻¹ * E.rootSeminorm u := by
    have hg : (∑ k ∈ Finset.range n, q ^ k) ≤ (1 - q)⁻¹ := by
      have hs := hasSum_geometric_of_lt_one hq₀ hq₁
      exact hs.tsum_eq ▸ hs.summable.sum_le_tsum _ (fun k _ ↦ pow_nonneg hq₀ k)
    rw [← Finset.sum_range_sub m n]
    calc
      _ ≤ ∑ k ∈ Finset.range n, |m (k + 1) - m k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, D * (q ^ k * E.rootSeminorm u) :=
        Finset.sum_le_sum (fun k _ ↦ hstep k)
      _ = D * (∑ k ∈ Finset.range n, q ^ k) * E.rootSeminorm u := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hD.le) (apply_nonneg _ _)
  have hlim : Tendsto m atTop (𝓝 (f (coding s))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    rw [tendsto_order]
    refine ⟨fun a ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _), fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hdist⟩ :=
      Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous)
        (ε / 2) (half_pos hε)
    filter_upwards [tendsto_wordMap_radius.eventually_lt_const hδ] with n hn
    rw [Real.norm_eq_abs]
    change |E.wordMean (w n) u - f (coding s)| < ε
    rw [E.wordMean_continuousLp (w n) f hf]
    apply lt_of_le_of_lt _ (half_lt_self hε)
    apply abs_wordMean_sub_le
    intro t
    have h := wordMap_dist_le n (addressPrefix n s) (mem_range_self t) (coding_mem_range_prefix n s)
    exact (show |f (wordMap (w n) t) - f (coding s)| < ε / 2 from
      Real.dist_eq _ _ ▸ hdist (h.trans_lt hn)).le
  have hz : m 0 = E.wordMean [] u := by
    change E.wordMean (List.ofFn (addressPrefix 0 s)) u = _
    rw [List.ofFn_zero]
  rw [← hz]
  exact le_of_tendsto_of_tendsto ((hlim.sub_const (m 0)).abs) tendsto_const_nhds
    (Eventually.of_forall hfinite)

/-- For `ρ > 1`, continuous domain functions have a uniform norm estimate by the graph norm. -/
theorem exists_uniform_norm_le_graphSeminorm (hρ : 1 < E.scalingFactor) :
    ∃ C > (0 : ℝ), ∀ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain),
      ‖f‖ ≤ C * E.graphSeminorm ⟨continuousLp p f, hf⟩ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨D, hD, h⟩ := E.exists_sup_sub_mean_le_rootSeminorm hρ
  refine ⟨D + 1, by positivity, fun f hf ↦ ?_⟩
  let g : E.domain := ⟨continuousLp p f, hf⟩
  let m := E.wordMean [] g
  have hm : |m| ≤ ‖(g : CarpetLp p)‖ := by
    have hi := norm_setIntegral_le univ (g : CarpetLp p)
    rw [Measure.restrict_univ] at hi
    exact (Real.norm_eq_abs _ ▸ hi)
  apply (ContinuousMap.norm_le f (mul_nonneg (by positivity) (apply_nonneg _ _))).mpr
  intro x
  rw [Real.norm_eq_abs, ← sub_add_cancel (f x) m]
  calc
    _ ≤ |f x - m| + |m| := abs_add_le _ _
    _ ≤ D * E.rootSeminorm g + ‖(g : CarpetLp p)‖ := add_le_add (h f hf x) hm
    _ ≤ D * E.graphSeminorm g + E.graphSeminorm g :=
      add_le_add (mul_le_mul_of_nonneg_left (E.rootSeminorm_le_graphSeminorm g) hD.le)
        (E.norm_coe_le_graphSeminorm g)
    _ = _ := by ring

/-- Every finite-energy function has a continuous version if `ρ > 1`. -/
theorem exists_continuous_version_of_scalingFactor_gt_one (hρ : 1 < E.scalingFactor) (f : E.domain) :
    ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (f : CarpetLp p) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨C, hC, hb⟩ := E.exists_uniform_norm_le_graphSeminorm hρ
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose u hu hnear using fun n ↦ E.regular_graph f (ε n) (hε n)
  let g (n : ℕ) : E.domain := ⟨continuousLp p (u n), hu n⟩
  have ht : Tendsto (fun n ↦ E.toGraph (g n)) atTop (𝓝 (E.toGraph f)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ ↦ norm_nonneg _) (fun n ↦ (hnear n).le)
  have hd (m n : ℕ) : ‖u m - u n‖ ≤ C * ‖E.toGraph (g m) - E.toGraph (g n)‖ := by
    have he : continuousLp p (u m - u n) = ((g m - g n : E.domain) : CarpetLp p) :=
      (continuousLpLinear p).map_sub _ _
    have hm : continuousLp p (u m - u n) ∈ E.domain := he.symm ▸ (g m - g n).property
    have hdf : (⟨continuousLp p (u m - u n), hm⟩ : E.domain) = g m - g n := Subtype.ext he
    change ‖u m - u n‖ ≤ C * E.graphSeminorm (g m - g n)
    simpa only [hdf] using hb (u m - u n) hm
  have hc : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro η hη
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ht.cauchySeq (η / C) (div_pos hη hC)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [dist_eq_norm]
    apply (hd m n).trans_lt
    have h := hN m hm n hn
    rw [dist_eq_norm] at h
    exact (mul_lt_mul_of_pos_left h hC).trans_eq (by field_simp)
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  let L := ContinuousMap.toLp (E := ℝ) (ENNReal.ofReal p) carpetMeasure ℝ
  have hL (w : C(CarpetPoints, ℝ)) : L w = continuousLp p w := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp carpetMeasure w).trans (continuousLp_ae_eq p w).symm
  have h₁ : Tendsto (fun n ↦ continuousLp p (u n)) atTop (𝓝 (continuousLp p v)) := by
    have ht' := (L.continuous.tendsto v).comp hv
    have hEq : (L : C(CarpetPoints, ℝ) → CarpetLp p) ∘ u = fun n ↦ continuousLp p (u n) :=
      funext fun n ↦ hL (u n)
    rwa [hEq, hL v] at ht' 
  have h₂ : Tendsto (fun n ↦ continuousLp p (u n)) atTop (𝓝 (f : CarpetLp p)) :=
    (E.graphInclusion.continuous.tendsto _).comp ht
  exact ⟨v, tendsto_nhds_unique h₁ h₂⟩

/-- The cell oscillation estimate used in the Morrey case of Section 5.
It follows from the word pullback of the global oscillation bound. -/
theorem exists_cell_oscillation_bound (hρ : 1 < E.scalingFactor) :
    ∃ C > (0 : ℝ), ∀ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain)
      (w : List (Fin 8)) (x y : CarpetPoints),
      |f (wordMap w x) - f (wordMap w y)| ^ p ≤
        C * (E.scalingFactor ^ w.length)⁻¹ *
          (E.energyMeasure ⟨continuousLp p f, hf⟩ (range (wordMap w))).toReal := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨D, hD, h⟩ := E.exists_sup_sub_mean_le_rootSeminorm hρ
  refine ⟨(2 * D) ^ p, Real.rpow_pos_of_pos (by positivity) _, fun f hf w x y ↦ ?_⟩
  let g := f.comp ⟨wordMap w, continuous_wordMap w⟩
  let u : E.domain := ⟨continuousLp p f, hf⟩
  let v := E.pullbackWord w u
  have he : continuousLp p g = (v : CarpetLp p) := continuousLp_interpolate_word_eq f hf g w (fun _ ↦ rfl)
  have hg : continuousLp p g ∈ E.domain := he.symm ▸ v.property
  have he' : (⟨continuousLp p g, hg⟩ : E.domain) = v := Subtype.ext he
  let m := E.wordMean [] v
  have hx : |g x - m| ≤ D * E.rootSeminorm v := by simpa only [he'] using h g hg x
  have hy : |g y - m| ≤ D * E.rootSeminorm v := by simpa only [he'] using h g hg y
  have hab : |g x - g y| ≤ (2 * D) * E.rootSeminorm v := by
    calc
      _ = |(g x - m) - (g y - m)| := by ring_nf
      _ ≤ |g x - m| + |g y - m| := abs_sub _ _
      _ ≤ D * E.rootSeminorm v + D * E.rootSeminorm v := add_le_add hx hy
      _ = _ := by ring
  have hpow := Real.rpow_le_rpow (abs_nonneg _) hab hp.le
  rw [Real.mul_rpow (by positivity) (apply_nonneg _ _), E.rootSeminorm_apply,
    Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'] at hpow
  have hμ := congrArg ENNReal.toReal (E.energyMeasure_range_word u w)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (zero_le_one.trans hρ.le),
    ENNReal.coe_toReal] at hμ
  change |g x - g y| ^ p ≤ (2 * D) ^ p * (E.scalingFactor ^ w.length)⁻¹ *
    (E.energyMeasure u (range (wordMap w))).toReal
  rw [hμ]
  have hρn : E.scalingFactor ^ w.length ≠ 0 := pow_ne_zero _ (zero_lt_one.trans hρ).ne'
  rw [mul_assoc, ← mul_assoc (E.scalingFactor ^ w.length)⁻¹,
    inv_mul_cancel₀ hρn, one_mul]
  exact hpow

end CarpetEnergy.SelfSimilarPEnergy
