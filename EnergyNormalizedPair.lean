import EnergyPairDensityBounds

/-!
# Simultaneous normalized harmonic pullbacks

Each component's separately normalized pullback is compact under the
individual neighborhood ratios. Bounded scalar weights convert the
two limits to the normalization by total pair energy.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

noncomputable def pairWordScale (w : List (Fin 8)) (f g : E.domain) : ℝ :=
  (((E.energy (E.pullbackWord w f) : ℝ) + (E.energy (E.pullbackWord w g) : ℝ)) ^ p⁻¹)⁻¹

noncomputable def centeredWordPullback (w : List (Fin 8)) (f : E.domain) : E.domain :=
  E.pullbackWord w f + ⟨constantLp p (-E.wordMean w f), E.constant_mem _⟩

/-- The two centered word pullbacks scaled by one common factor. -/
noncomputable def normalizedPairWordPullback (w : List (Fin 8)) (f g : E.domain) : E.domain × E.domain :=
  (E.pairWordScale w f g • E.centeredWordPullback w f,
    E.pairWordScale w f g • E.centeredWordPullback w g)

theorem IsInteriorHarmonic.add_constant {f : E.domain} (hf : E.IsInteriorHarmonic f) (c : ℝ) :
    E.IsInteriorHarmonic (f + ⟨constantLp p c, E.constant_mem c⟩) := by
  intro u hu hz
  let C : E.domain := ⟨constantLp p c, E.constant_mem c⟩
  let U : E.domain := ⟨continuousLp p u, hu⟩
  change E.energy (f + C) ≤ E.energy (f + C + U)
  rw [add_right_comm f C U, E.add_constant, E.add_constant]
  exact hf u hu hz

theorem isClosed_interiorHarmonic :
    IsClosed {z : E.GraphDomain | E.IsInteriorHarmonic (E.graphToDomain z)} := by
  let T := {v : C(CarpetPoints, ℝ) // continuousLp p v ∈ E.domain ∧
    ∀ x ∈ carpetOuterBoundary, v x = 0}
  have hEq : {z : E.GraphDomain | E.IsInteriorHarmonic (E.graphToDomain z)} =
      ⋂ v : T, {z | (E.energy (E.graphToDomain z) : ℝ) ≤
        (E.energy (E.graphToDomain (z + E.toGraph ⟨continuousLp p v.val, v.property.1⟩)) : ℝ)} := by
    ext z
    rw [mem_iInter]
    constructor
    · intro hz v
      exact_mod_cast hz v.val v.property.1 v.property.2
    · intro hz v hv hv₀
      exact_mod_cast hz ⟨v, hv, hv₀⟩
  rw [hEq]
  exact isClosed_iInter fun _ ↦ isClosed_le E.continuous_graphEnergy
    (E.continuous_graphEnergy.comp (continuous_id.add continuous_const))

theorem normalizedPairWordPullback_isInteriorHarmonic (w : List (Fin 8)) (f g : E.domain)
    (hf : E.IsInteriorHarmonic f) (hg : E.IsInteriorHarmonic g) :
    E.IsInteriorHarmonic (E.normalizedPairWordPullback w f g).1 ∧
      E.IsInteriorHarmonic (E.normalizedPairWordPullback w f g).2 :=
  ⟨(((hf.pullbackWord E w).add_constant E _).smul E _),
    (((hg.pullbackWord E w).add_constant E _).smul E _)⟩

theorem energy_normalizedPairWordPullback_add (w : List (Fin 8)) (f g : E.domain)
    (h : 0 < (E.energy (E.pullbackWord w f) : ℝ) + (E.energy (E.pullbackWord w g) : ℝ)) :
    (E.energy (E.normalizedPairWordPullback w f g).1 : ℝ) +
      (E.energy (E.normalizedPairWordPullback w f g).2 : ℝ) = 1 := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let t := (E.energy (E.pullbackWord w f) : ℝ) + (E.energy (E.pullbackWord w g) : ℝ)
  have hpow : |E.pairWordScale w f g| ^ p = t⁻¹ := by
    change |(t ^ p⁻¹)⁻¹| ^ p = _
    rw [abs_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg h.le _)),
      Real.inv_rpow (Real.rpow_nonneg h.le _), Real.rpow_inv_rpow h.le hp.ne']
  simp only [normalizedPairWordPullback, E.smul_energy, centeredWordPullback, E.add_constant, hpow]
  rw [← mul_add]
  exact inv_mul_cancel₀ h.ne'

private noncomputable def pairWordWeight (w : List (Fin 8)) (f g : E.domain) : ℝ :=
  (E.energy (E.pullbackWord w f) : ℝ) ^ p⁻¹ * E.pairWordScale w f g

private theorem pairWordWeight_mem_Icc (w : List (Fin 8)) (f g : E.domain) :
    E.pairWordWeight w f g ∈ Icc (0 : ℝ) 1 := by
  let a := (E.energy (E.pullbackWord w f) : ℝ)
  let b := (E.energy (E.pullbackWord w g) : ℝ)
  have ha : 0 ≤ a := NNReal.coe_nonneg _
  have hb : 0 ≤ b := NNReal.coe_nonneg _
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  change a ^ p⁻¹ * ((a + b) ^ p⁻¹)⁻¹ ∈ Icc _ _
  refine ⟨mul_nonneg (Real.rpow_nonneg ha _) (inv_nonneg.mpr (Real.rpow_nonneg (add_nonneg ha hb) _)), ?_⟩
  rcases eq_or_lt_of_le (add_nonneg ha hb) with ht | ht
  · rw [← ht, Real.zero_rpow (inv_ne_zero hp.ne'), inv_zero, mul_zero]
    exact zero_le_one
  · rw [← div_eq_mul_inv]
    exact (div_le_one (Real.rpow_pos_of_pos ht _)).mpr
      (Real.rpow_le_rpow ha (le_add_of_nonneg_right hb) (inv_nonneg.mpr hp.le))

private theorem first_normalizedPairWordPullback_eq (w : List (Fin 8)) (f g : E.domain)
    (hf : 0 < E.energy (E.pullbackWord w f)) :
    (E.normalizedPairWordPullback w f g).1 =
      E.pairWordWeight w f g • E.normalizedWordPullback w f := by
  change E.pairWordScale w f g • E.centeredWordPullback w f = _
  rw [normalizedWordPullback, smul_smul, pairWordWeight, unitEnergyScale]
  congr 1
  rw [mul_right_comm, mul_inv_cancel₀ (Real.rpow_pos_of_pos
    (show 0 < (E.energy (E.pullbackWord w f) : ℝ) by exact_mod_cast hf) _).ne', one_mul]

private theorem second_normalizedPairWordPullback_eq (w : List (Fin 8)) (f g : E.domain)
    (hg : 0 < E.energy (E.pullbackWord w g)) :
    (E.normalizedPairWordPullback w f g).2 =
      E.pairWordWeight w g f • E.normalizedWordPullback w g := by
  have h : E.pairWordScale w f g = E.pairWordScale w g f := by simp only [pairWordScale, add_comm]
  change E.pairWordScale w f g • E.centeredWordPullback w g = _
  rw [h]
  exact E.first_normalizedPairWordPullback_eq w g f hg

/-- Joint normalized harmonic compactness follows from the two separate
applications of Proposition 4.2 and compactness of the normalization weights. -/
theorem exists_normalizedPairWordPullback_subseq
    (hcompact : E.HasInteriorHarmonicCompactness) (f g : E.domain)
    (hf : E.IsInteriorHarmonic f) (hg : E.IsInteriorHarmonic g)
    (n : ℕ → ℕ) (w : ∀ k, Fin (n k) → Fin 8) (hn : ∀ k, k ≤ n k)
    (hmassF : ∀ k, 0 < E.energyMeasure f (range (wordMap (List.ofFn (w k)))))
    (hmassG : ∀ k, 0 < E.energyMeasure g (range (wordMap (List.ofFn (w k)))))
    (hratioF : ∃ a : ℝ≥0∞, 0 < a ∧ ∀ k, a * E.energyMeasure f (wordCellUnion (cellNeighborhood (w k) 3)) ≤
      E.energyMeasure f (range (wordMap (List.ofFn (w k)))))
    (hratioG : ∃ a : ℝ≥0∞, 0 < a ∧ ∀ k, a * E.energyMeasure g (wordCellUnion (cellNeighborhood (w k) 3)) ≤
      E.energyMeasure g (range (wordMap (List.ofFn (w k)))))
    (hloc : ∀ k, wordCellUnion (cellNeighborhood (w k) 3) ⊆ carpetOuterBoundaryᶜ) :
    ∃ (j : ℕ → ℕ) (v₁ v₂ : E.domain) (u₁ u₂ : C(CarpetPoints, ℝ)), StrictMono j ∧
      continuousLp p u₁ = (v₁ : CarpetLp p) ∧ continuousLp p u₂ = (v₂ : CarpetLp p) ∧
      E.IsInteriorHarmonic v₁ ∧ E.IsInteriorHarmonic v₂ ∧
      (E.energy v₁ : ℝ) + (E.energy v₂ : ℝ) = 1 ∧
      Tendsto (fun k ↦ E.toGraph (E.normalizedPairWordPullback (List.ofFn (w (j k))) f g).1)
        atTop (𝓝 (E.toGraph v₁)) ∧
      Tendsto (fun k ↦ E.toGraph (E.normalizedPairWordPullback (List.ofFn (w (j k))) f g).2)
        atTop (𝓝 (E.toGraph v₂)) := by
  obtain ⟨i, v₁, u₁, hi, hu₁, hv₁⟩ := hcompact f hf n w hn hmassF hratioF hloc
  obtain ⟨a, ha, hra⟩ := hratioG
  obtain ⟨j, v₂, u₂, hj, hu₂, hv₂⟩ := hcompact g hg (n ∘ i) (fun k ↦ w (i k))
    (fun k ↦ (hi.le_apply : k ≤ i k).trans (hn (i k))) (fun k ↦ hmassG (i k))
    ⟨a, ha, fun k ↦ hra (i k)⟩ (fun k ↦ hloc (i k))
  let W (k : ℕ) := List.ofFn (w (i (j k)))
  let r (k : ℕ) := (E.pairWordWeight (W k) f g, E.pairWordWeight (W k) g f)
  have hC : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨b, _, l, hl, hr⟩ := hC.tendsto_subseq (x := r) (fun k ↦
    ⟨E.pairWordWeight_mem_Icc (W k) f g, E.pairWordWeight_mem_Icc (W k) g f⟩)
  let σ := i ∘ j ∘ l
  let V₁ : E.domain := b.1 • v₁
  let V₂ : E.domain := b.2 • v₂
  have hV₁ : Tendsto (fun k ↦ E.toGraph (E.normalizedPairWordPullback (List.ofFn (w (σ k))) f g).1)
      atTop (𝓝 (E.toGraph V₁)) := by
    have h := (continuous_fst.tendsto b).comp hr
    have ht := h.smul ((hv₁.comp hj.tendsto_atTop).comp hl.tendsto_atTop)
    apply ht.congr'
    filter_upwards with k
    rw [E.first_normalizedPairWordPullback_eq _ _ _ (E.pullback_energy_pos_of_mass _ (hmassF (σ k)))]
    rfl
  have hV₂ : Tendsto (fun k ↦ E.toGraph (E.normalizedPairWordPullback (List.ofFn (w (σ k))) f g).2)
      atTop (𝓝 (E.toGraph V₂)) := by
    have h := (continuous_snd.tendsto b).comp hr
    have ht := h.smul (hv₂.comp hl.tendsto_atTop)
    apply ht.congr'
    filter_upwards with k
    rw [E.second_normalizedPairWordPullback_eq _ _ _ (E.pullback_energy_pos_of_mass _ (hmassG (σ k)))]
    rfl
  have hE : (E.energy V₁ : ℝ) + (E.energy V₂ : ℝ) = 1 := by
    apply tendsto_nhds_unique (((E.continuous_graphEnergy.tendsto _).comp hV₁).add
      ((E.continuous_graphEnergy.tendsto _).comp hV₂))
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)) using 1
    funext k
    exact E.energy_normalizedPairWordPullback_add _ _ _ (add_pos_of_pos_of_nonneg
      (by exact_mod_cast E.pullback_energy_pos_of_mass _ (hmassF (σ k))) (NNReal.coe_nonneg _))
  refine ⟨σ, V₁, V₂, b.1 • u₁, b.2 • u₂, hi.comp (hj.comp hl), ?_, ?_, ?_, ?_, hE, hV₁, hV₂⟩
  · change SelfSimilarComponent.continuousLpLinear p (b.1 • u₁) = _
    rw [map_smul]
    change b.1 • continuousLp p u₁ = _
    rw [hu₁]
    rfl
  · change SelfSimilarComponent.continuousLpLinear p (b.2 • u₂) = _
    rw [map_smul]
    change b.2 • continuousLp p u₂ = _
    rw [hu₂]
    rfl
  · exact E.isClosed_interiorHarmonic.mem_of_tendsto hV₁ (Eventually.of_forall fun k ↦
      (E.normalizedPairWordPullback_isInteriorHarmonic (List.ofFn (w (σ k))) f g hf hg).1)
  · exact E.isClosed_interiorHarmonic.mem_of_tendsto hV₂ (Eventually.of_forall fun k ↦
      (E.normalizedPairWordPullback_isInteriorHarmonic (List.ofFn (w (σ k))) f g hf hg).2)

end CarpetEnergy.SelfSimilarPEnergy
