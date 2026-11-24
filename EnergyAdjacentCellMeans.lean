import EnergyGraphPullback
import EnergyAdjacentCells

/-!
# Adjacent-cell means on the full domain

Graph-continuous word pullbacks transport the mean inequalities from
continuous domain functions to all energy-domain functions.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem continuous_graphEnergy :
    Continuous (fun z : E.GraphDomain ↦ (E.energy (E.graphToDomain z) : ℝ)) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let L : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := E.rootSeminorm.comp L
  have hS : Continuous S :=
    Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm
      (fun z ↦ E.rootSeminorm_le_graphSeminorm (E.graphToDomain z))
  have he (z : E.GraphDomain) : (E.energy (E.graphToDomain z) : ℝ) = S z ^ p := by
    change _ = E.rootSeminorm (E.graphToDomain z) ^ p
    rw [E.rootSeminorm_apply]
    exact (Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne').symm
  simp only [he]
  exact hS.rpow_const (fun _ ↦ Or.inr hp.le)

theorem continuous_graphWordMean (w : List (Fin 8)) :
    Continuous (fun z : E.GraphDomain ↦ E.wordMean w (E.graphToDomain z)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  let A := (lpSetIntegral (p := p) univ).comp (E.graphInclusion.comp (E.graphPullbackWord w))
  have hA (z : E.GraphDomain) : A z = E.wordMean w (E.graphToDomain z) := by
    change (∫ x in univ, (E.pullbackWord w (E.graphToDomain z) : CarpetLp p) x ∂carpetMeasure) = _
    rw [Measure.restrict_univ]
    rfl
  rw [show (fun z ↦ E.wordMean w (E.graphToDomain z)) = A from (funext hA).symm]
  exact A.continuous

theorem wordMean_continuousLp (w : List (Fin 8)) (f : C(CarpetPoints, ℝ))
    (hf : continuousLp p f ∈ E.domain) :
    E.wordMean w ⟨continuousLp p f, hf⟩ = ∫ x, f (wordMap w x) ∂carpetMeasure := by
  unfold wordMean
  exact integral_congr_ae ((E.pullbackWord_isLpPullback w ⟨continuousLp p f, hf⟩).trans
    ((quasiMeasurePreserving_wordMap w).ae_eq_comp (continuousLp_ae_eq p f)))

/-- The adjacent-cell inequality (4.9) for every domain function. -/
theorem exists_wordMean_gap_of_side_adjacent :
    ∃ C > (0 : ℝ), ∀ (f : E.domain) (w v : List (Fin 8)) (j : Fin 2),
      w.length = v.length → gridCoordinate v j = gridCoordinate w j + 1 →
      gridCoordinate v j.rev = gridCoordinate w j.rev →
      |E.wordMean w f - E.wordMean v f| ^ p ≤
        C * ((E.energy (E.pullbackWord w f) : ℝ) + (E.energy (E.pullbackWord v f) : ℝ)) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨C, hC, hgap⟩ := E.exists_mean_gap_of_adjacent_words
  refine ⟨C, hC, fun f w v j hwv hj hk ↦ ?_⟩
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose u hu hnear using fun n ↦ E.regular_graph f (ε n) (hε n)
  let g (n : ℕ) : E.domain := ⟨continuousLp p (u n), hu n⟩
  have hlim : Tendsto (fun n ↦ E.toGraph (g n)) atTop (𝓝 (E.toGraph f)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ ↦ norm_nonneg _) (fun n ↦ (hnear n).le)
  have hM (a : List (Fin 8)) :
      Tendsto (fun n ↦ E.wordMean a (g n)) atTop (𝓝 (E.wordMean a f)) :=
    ((E.continuous_graphWordMean a).tendsto _).comp hlim
  have hE (a : List (Fin 8)) : Tendsto (fun n ↦ (E.energy (E.pullbackWord a (g n)) : ℝ)) atTop
      (𝓝 (E.energy (E.pullbackWord a f) : ℝ)) :=
    ((E.continuous_graphEnergy.comp (E.graphPullbackWord a).continuous).tendsto _).comp hlim
  apply le_of_tendsto_of_tendsto (((hM w).sub (hM v)).abs.rpow_const (Or.inr hp.le))
    (((hE w).add (hE v)).const_mul C)
  filter_upwards with n
  have hc := hgap (u n) (hu n) w v j hwv hj hk
  rw [← E.wordMean_continuousLp w (u n) (hu n), ← E.wordMean_continuousLp v (u n) (hu n)] at hc
  exact hc

end CarpetEnergy.SelfSimilarPEnergy
