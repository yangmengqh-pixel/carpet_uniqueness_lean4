import EnergyNormalizedHarmonic
import EnergyComponentInterpolation
import CarpetGoodCells

/-!
# Reduction of the zero-one law to harmonic compactness

The compact selection gives a sequence with positive central mass,
bounded neighborhood ratios, and vanishing complementary mass after
normalization. A strong continuous limit lies in the complementary
component kernel and has unit energy.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem normalized_mass_le_of_ratio {μ : Measure CarpetPoints}
    (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (B : Set CarpetPoints) (w : List (Fin 8))
    (hinv : ∀ᵐ x ∂μ, wordMap w x ∈ B ↔ x ∈ B)
    (f : E.domain) (hw : 0 < E.energyMeasure f (range (wordMap w)))
    (ε : ℝ≥0∞)
    (hsmall : E.energyMeasure f (range (wordMap w) ∩ B) ≤
      ε * E.energyMeasure f (range (wordMap w))) :
    E.energyMeasure (E.normalizedWordPullback w f) B ≤ ε := by
  let u := E.pullbackWord w f
  let e : ℝ≥0 := E.energy u
  let s := ENNReal.ofReal E.scalingFactor ^ w.length
  have hu : 0 < e := E.pullback_energy_pos_of_mass w hw
  have hs : s ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1).ne'
  have hs' : s ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hm := E.energyMeasure_inter_image_word_of_invariant hdom B w hinv f univ
  rw [image_univ, inter_univ, inter_comm B] at hm
  rw [hm, E.energyMeasure_range_word] at hsmall
  change s * E.energyMeasure u B ≤ ε * (s * (e : ℝ≥0∞)) at hsmall
  have hle : E.energyMeasure u B ≤ ε * (e : ℝ≥0∞) := by
    have hc : s⁻¹ * s = 1 := ENNReal.inv_mul_cancel hs hs'
    calc
      _ = s⁻¹ * (s * E.energyMeasure u B) := by rw [← mul_assoc, hc, one_mul]
      _ ≤ s⁻¹ * (ε * (s * (e : ℝ≥0∞))) := mul_le_mul' le_rfl hsmall
      _ = (s⁻¹ * s) * (ε * (e : ℝ≥0∞)) := by ac_rfl
      _ = _ := by rw [hc, one_mul]
  have he : ENNReal.ofReal ((e : ℝ)⁻¹) * (e : ℝ≥0∞) = 1 := by
    rw [← (show ENNReal.ofReal (e : ℝ) = (e : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal), ← ENNReal.ofReal_mul (inv_nonneg.mpr e.coe_nonneg),
      inv_mul_cancel₀ (by exact_mod_cast hu.ne'), ENNReal.ofReal_one]
  rw [normalizedWordPullback, E.energyMeasure_smul, E.energyMeasure_add_constant,
    E.unitEnergyScale_rpow hu, smul_apply, smul_eq_mul]
  change ENNReal.ofReal ((e : ℝ)⁻¹) * E.energyMeasure u B ≤ _
  calc
    _ ≤ ENNReal.ofReal ((e : ℝ)⁻¹) * (ε * (e : ℝ≥0∞)) := mul_le_mul' le_rfl hle
    _ = ε * (ENNReal.ofReal ((e : ℝ)⁻¹) * (e : ℝ≥0∞)) := by ac_rfl
    _ = _ := by rw [he, mul_one]

/-- Theorem 6.1 follows from the specialized graph compactness of harmonic blowups. -/
theorem zeroOne_of_interiorHarmonicCompactness
    (hcompact : E.HasInteriorHarmonicCompactness)
    (μ : Measure CarpetPoints) (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (hmin : ∀ ν : Measure CarpetPoints, (∀ f, E.energyMeasure f ≪ ν) → μ ≪ ν) :
    HasZeroOneLaw μ (Sum.elim cellMap carpetSymmetry) := by
  intro A hA hAinv
  by_cases hμA : μ A = 0
  · exact Or.inl hμA
  apply Or.inr
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hcell (i : Fin 8) : ∀ᵐ x ∂μ, cellMap i x ∈ A ↔ x ∈ A := hAinv (Sum.inl i)
  have hsy (σ : SquareSymmetry) : ∀ᵐ x ∂μ, carpetSymmetry σ x ∈ A ↔ x ∈ A :=
    hAinv (Sum.inr σ)
  have hcell' (i : Fin 8) : ∀ᵐ x ∂μ, cellMap i x ∈ Aᶜ ↔ x ∈ Aᶜ :=
    (hcell i).mono fun _ h ↦ not_congr h
  have hsy' (σ : SquareSymmetry) : ∀ᵐ x ∂μ, carpetSymmetry σ x ∈ Aᶜ ↔ x ∈ Aᶜ :=
    (hsy σ).mono fun _ h ↦ not_congr h
  obtain ⟨h, hH, hΓ⟩ := E.exists_interiorHarmonic_pos_mass hdom hmin A hA
    (pos_iff_ne_zero.mpr hμA) hcell
  have hh : 0 < E.energy h := by
    have h := hΓ.trans_le (measure_mono (subset_univ _))
    rwa [E.energyMeasure_univ, ENNReal.coe_pos] at h
  let f := E.unitEnergyScale h • h
  have hF : E.IsInteriorHarmonic f := hH.smul E _
  let ν := E.energyMeasure f
  have hν : ν univ = 1 := by
    change E.energyMeasure f univ = 1
    rw [E.energyMeasure_univ, E.energy_unitEnergyScale_smul hh, ENNReal.coe_one]
  have hνA : 0 < ν A := by
    change 0 < E.energyMeasure (E.unitEnergyScale h • h) A
    rw [E.energyMeasure_smul, smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (abs_pos.mpr (E.unitEnergyScale_pos hh).ne') _)).ne' hΓ.ne'
  obtain ⟨α, hα, hsel⟩ := exists_good_interior_cells ν hν
    (E.energyMeasure_carpetOuterBoundary_eq_zero f)
    (E.energyMeasure_carpetCellBoundary_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero f) A hA hνA 3
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hex (k : ℕ) : ∃ n ≥ k, ∃ w : Fin n → Fin 8,
      0 < ν (range (wordMap (List.ofFn w))) ∧
      α * ν (wordCellUnion (cellNeighborhood w 3)) ≤ ν (range (wordMap (List.ofFn w))) ∧
      wordCellUnion (cellNeighborhood w 3) ⊆ carpetOuterBoundaryᶜ ∧
      ν (range (wordMap (List.ofFn w)) ∩ Aᶜ) ≤ ENNReal.ofReal (ε k) * ν (range (wordMap (List.ofFn w))) := by
    have he := (eventually_ge_atTop k).and (hsel (ε k) (hε k))
    obtain ⟨n, hn, w, h⟩ := he.exists
    exact ⟨n, hn, w, h⟩
  choose n hn w hmass hratio hloc hsmall using hex
  obtain ⟨j, g, u, hj, hu, hlim⟩ :=
    hcompact f hF n w hn hmass ⟨α, hα, hratio⟩ hloc
  let v (k : ℕ) := E.normalizedWordPullback (List.ofFn (w (j k))) f
  have hv (k : ℕ) : E.energy (v k) = 1 :=
    E.energy_normalizedWordPullback _ _ (E.pullback_energy_pos_of_mass _ (hmass (j k)))
  have hE : (E.energy g : ℝ) = 1 := by
    have hh := ((E.continuous_graphEnergy.tendsto (E.toGraph g)).comp hlim)
    have hEq : (fun k ↦ (E.energy (v k) : ℝ)) = fun _ ↦ 1 := funext fun k ↦ by rw [hv]; rfl
    change Tendsto (fun k ↦ (E.energy (v k) : ℝ)) atTop (𝓝 (E.energy g : ℝ)) at hh
    rw [hEq] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  obtain ⟨d, hdc, hdd⟩ := E.exists_energyDense_continuous_sequence
  let ν' := E.energyReferenceMeasure d
  have hνμ : ν' ≪ μ := E.energyReferenceMeasure_absolutelyContinuous d μ hdom
  have hμν : μ ≪ ν' := hmin ν' (E.energyMeasure_absolutelyContinuous_reference d hdd)
  have hi (w : List (Fin 8)) : ∀ᵐ x ∂μ, wordMap w x ∈ Aᶜ ↔ x ∈ Aᶜ :=
    (E.ae_mem_word_of_ae_mem_cell d hdc hdd
      (fun i ↦ (hcell' i).filter_mono hνμ.ae_le) w).filter_mono hμν.ae_le
  have hcMass (k : ℕ) : E.energyMeasure (v k) Aᶜ ≤ ENNReal.ofReal (ε (j k)) :=
    E.normalized_mass_le_of_ratio hdom Aᶜ _ (hi _) f (hmass (j k)) _ (hsmall (j k))
  let Q := E.componentOfInvariantSet hdom Aᶜ hA.compl hcell' hsy'
  let L : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := Q.rootSeminorm.comp L
  have hS : Continuous S := by
    apply Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm
    intro z
    change Q.rootSeminorm (E.graphToDomain z) ≤ E.graphSeminorm (E.graphToDomain z)
    apply le_trans _ (E.rootSeminorm_le_graphSeminorm _)
    rw [Q.rootSeminorm_apply, E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr (Q.mass_le_energy _))
      (inv_nonneg.mpr hp.le)
  have hupper (k : ℕ) : S (E.toGraph (v k)) ≤ (ε (j k)) ^ p⁻¹ := by
    change Q.rootSeminorm (v k) ≤ _
    rw [Q.rootSeminorm_apply]
    have hQ := E.componentOfInvariantSet_mass hdom Aᶜ hA.compl hcell' hsy' (v k)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hQ.trans_le (hcMass k))
    rw [ENNReal.coe_toReal, ENNReal.toReal_ofReal (hε _).le] at hh
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) hh (inv_nonneg.mpr hp.le)
  have hEps : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun k ↦ (ε (j k)) ^ p⁻¹) atTop (𝓝 0) := by
    have hh := (hEps.comp hj.tendsto_atTop).rpow_const
      (Or.inr (inv_nonneg.mpr hp.le))
    simpa only [Function.comp_apply, Real.zero_rpow (inv_ne_zero hp.ne')] using hh
  have hqle := le_of_tendsto_of_tendsto ((hS.tendsto _).comp hlim) ht (Eventually.of_forall hupper)
  have hq : Q.rootSeminorm g = 0 := hqle.antisymm (apply_nonneg _ _)
  have hMem : g ∈ Q.kernel := (Q.mem_kernel_iff g).mpr ((Q.mass_eq_zero_iff_root_eq_zero g).mpr hq)
  have hu' : continuousLp p u ∈ E.domain := hu.symm ▸ g.property
  have hgu : (⟨continuousLp p u, hu'⟩ : E.domain) = g := Subtype.ext hu
  have huQ : u ∈ Q.continuousKernel := ⟨hu', hgu.symm ▸ hMem⟩
  have hQzero : ∀ f, Q.mass f = 0 := by
    rcases Q.kernel_dichotomy with hconst | hzero
    · obtain ⟨c, hc⟩ := hconst u huQ
      have hconst' : (g : CarpetLp p) = constantLp p c := by
        apply Lp.ext
        rw [← hu]
        have hcu : (u : CarpetPoints → ℝ) =ᵐ[carpetMeasure] fun _ ↦ c :=
          Eventually.of_forall hc
        exact (continuousLp_ae_eq p u).trans (hcu.trans
          (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c).symm)
      have he := (E.zero_iff_constant g).2 ⟨c, hconst'⟩
      rw [he, NNReal.coe_zero] at hE
      exact (zero_ne_one hE).elim
    · exact hzero
  apply (E.null_iff_forall_energyMeasure_null hdom hmin hA.compl).mpr
  intro v'
  rw [← E.componentOfInvariantSet_mass hdom Aᶜ hA.compl hcell' hsy', hQzero v', ENNReal.coe_zero]

end CarpetEnergy.SelfSimilarPEnergy
