import EnergyIndependenceApproximation

/-!
# Pulling back pairwise dependence to a word cell

On a word cell the energy measure and the pair reference measure have
the same scaling factor. Their Radon–Nikodym ratio is therefore unchanged
under the cell map. The harmonic core reduction can use this identity to
work with a pair harmonic on the whole interior.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem rnDeriv_restrict_both (ν μ : Measure CarpetPoints)
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (h : ν ≪ μ)
    {S : Set CarpetPoints} (hS : MeasurableSet S) :
    ν.rnDeriv μ =ᵐ[μ.restrict S] (ν.restrict S).rnDeriv (μ.restrict S) := by
  let : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  apply Measure.eq_rnDeriv (Measure.measurable_rnDeriv _ _) Measure.MutuallySingular.zero_left
  rw [zero_add, ← restrict_withDensity hS, Measure.withDensity_rnDeriv_eq ν μ h]

/-- Cell covariance of the normalized pair densities used in Section 5. -/
theorem ae_rnDeriv_word_pair (w : List (Fin 8)) (f g : E.domain) (a b : ℚ) :
    let f' := E.pullbackWord w f
    let g' := E.pullbackWord w g
    ∀ᵐ x ∂(E.energyMeasure f' + E.energyMeasure g'),
      (E.energyMeasure (a • f + b • g)).rnDeriv (E.energyMeasure f + E.energyMeasure g) (wordMap w x) =
        (E.energyMeasure (a • f' + b • g')).rnDeriv (E.energyMeasure f' + E.energyMeasure g') x := by
  let f' := E.pullbackWord w f
  let g' := E.pullbackWord w g
  let μ := E.energyMeasure f + E.energyMeasure g
  let ν := E.energyMeasure (a • f + b • g)
  let μ' := E.energyMeasure f' + E.energyMeasure g'
  let ν' := E.energyMeasure (a • f' + b • g')
  let S := range (wordMap w)
  let r : ℝ≥0 := Real.toNNReal (E.scalingFactor ^ w.length)
  let e := measurableEmbedding_wordMap w
  have hρ := E.isScalingFactor_scalingFactor.1
  have hr : r ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (pow_pos hρ _))
  have hreal : (r : ℝ≥0∞) = ENNReal.ofReal E.scalingFactor ^ w.length := by
    rw [← ENNReal.ofReal_pow hρ.le]
    rfl
  have hν : ν.restrict S = r • ν'.map (wordMap w) := by
    change (E.energyMeasure (a • f + b • g)).restrict S = _
    rw [E.energyMeasure_restrict_word, ← hreal]
    rw [E.pullbackWord_add, ← Rat.cast_smul_eq_qsmul ℝ a f,
      ← Rat.cast_smul_eq_qsmul ℝ b g, E.pullbackWord_smul, E.pullbackWord_smul,
      Rat.cast_smul_eq_qsmul, Rat.cast_smul_eq_qsmul]
    rfl
  have hμ : μ.restrict S = r • μ'.map (wordMap w) := by
    change (E.energyMeasure f + E.energyMeasure g).restrict S = _
    rw [Measure.restrict_add, E.energyMeasure_restrict_word, E.energyMeasure_restrict_word, ← hreal]
    change r • (E.energyMeasure f').map _ + r • (E.energyMeasure g').map _ =
      r • (E.energyMeasure f' + E.energyMeasure g').map _
    rw [Measure.map_add _ _ e.measurable, smul_add]
  have h₁ := rnDeriv_restrict_both ν μ (E.energyMeasure_add_rat_smul_absolutelyContinuous f g a b)
    e.measurableSet_range
  rw [hν, hμ, Measure.ae_smul_measure_eq hr _] at h₁
  let : IsFiniteMeasure μ' := inferInstanceAs (IsFiniteMeasure (E.energyMeasure f' + E.energyMeasure g'))
  let : IsFiniteMeasure ν' := inferInstanceAs (IsFiniteMeasure (E.energyMeasure (a • f' + b • g')))
  let : (ν'.map (wordMap w)).HaveLebesgueDecomposition (μ'.map (wordMap w)) :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  have h₂ := Measure.rnDeriv_smul_same (ν'.map (wordMap w)) (μ'.map (wordMap w)) hr
  have h₃ := e.rnDeriv_map ν' μ'
  have hab : (fun x ↦ ν.rnDeriv μ (wordMap w x)) =ᵐ[μ']
      fun x ↦ (ν'.map (wordMap w)).rnDeriv (μ'.map (wordMap w)) (wordMap w x) :=
    e.ae_map_iff.mp (h₁.trans h₂)
  exact hab.trans h₃


theorem ae_pairDependence_on_word (w : List (Fin 8)) (f g : E.domain)
    (h : ∀ᵐ x ∂(E.energyMeasure (E.pullbackWord w f) + E.energyMeasure (E.pullbackWord w g)),
      ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
        E.energyDensityRoot
          (E.energyMeasure (E.pullbackWord w f) + E.energyMeasure (E.pullbackWord w g))
          (a • E.pullbackWord w f + b • E.pullbackWord w g) x ≤ ε * (‖a‖ + ‖b‖)) :
    ∀ᵐ x ∂(E.energyMeasure f + E.energyMeasure g).restrict (range (wordMap w)),
      ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
        E.energyDensityRoot (E.energyMeasure f + E.energyMeasure g) (a • f + b • g) x ≤
          ε * (‖a‖ + ‖b‖) := by
  let f' := E.pullbackWord w f
  let g' := E.pullbackWord w g
  let μ := E.energyMeasure f + E.energyMeasure g
  let μ' := E.energyMeasure f' + E.energyMeasure g'
  let c := ENNReal.ofReal E.scalingFactor ^ w.length
  let e := measurableEmbedding_wordMap w
  have hμ : μ.restrict (range (wordMap w)) = c • μ'.map (wordMap w) := by
    change (E.energyMeasure f + E.energyMeasure g).restrict _ = _
    rw [Measure.restrict_add, E.energyMeasure_restrict_word, E.energyMeasure_restrict_word]
    change c • (E.energyMeasure f').map _ + c • (E.energyMeasure g').map _ =
      c • (E.energyMeasure f' + E.energyMeasure g').map _
    rw [Measure.map_add _ _ e.measurable, smul_add]
  have hc : c ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1).ne'
  rw [hμ, Measure.ae_ennreal_smul_measure_eq hc, e.ae_map_iff]
  have hRN : ∀ᵐ x ∂μ', ∀ a b : ℚ,
      (E.energyMeasure (a • f + b • g)).rnDeriv μ (wordMap w x) =
        (E.energyMeasure (a • f' + b • g')).rnDeriv μ' x :=
    ae_all_iff.mpr fun a ↦ ae_all_iff.mpr fun b ↦ E.ae_rnDeriv_word_pair w f g a b
  filter_upwards [hRN, h] with x hx hh
  intro ε hε
  obtain ⟨a, b, hpos, hle⟩ := hh ε hε
  refine ⟨a, b, hpos, ?_⟩
  change ((E.energyMeasure (a • f + b • g)).rnDeriv μ (wordMap w x)).toReal ^ p⁻¹ ≤ _
  rw [hx a b]
  exact hle

private theorem IsInteriorHarmonic.of_piecewise_at_le {f : E.domain} {n N : ℕ} (hn : n ≤ N)
    (h : ∀ w : Fin n → Fin 8, E.IsInteriorHarmonic (E.pullbackWord (List.ofFn w) f))
    (w : Fin N → Fin 8) : E.IsInteriorHarmonic (E.pullbackWord (List.ofFn w) f) := by
  let W := List.ofFn w
  let u := W.take n
  let v := W.drop n
  have hu : u.length = n := by simp [u, W, Nat.min_eq_left hn]
  obtain ⟨a, ha⟩ : ∃ a : Fin n → Fin 8, List.ofFn a = u := by
    exact ⟨fun i ↦ u.get (Fin.cast hu.symm i),
      (List.ofFn_congr hu u.get).symm.trans (List.ofFn_get u)⟩
  have hW : List.ofFn a ++ v = W := by rw [ha]; exact List.take_append_drop n W
  change E.IsInteriorHarmonic (E.pullbackWord W f)
  rw [← hW, E.pullbackWord_append]
  exact (h a).pullbackWord E v

/-- Pairwise dependence on interior-harmonic functions implies dependence
on the full domain. This combines both parts of Proposition 5.4. -/
theorem hasPairwiseEnergyDependence_of_interiorHarmonic
    (h : ∀ f g : E.domain, E.IsInteriorHarmonic f → E.IsInteriorHarmonic g →
      ∀ᵐ x ∂(E.energyMeasure f + E.energyMeasure g),
        ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
          E.energyDensityRoot (E.energyMeasure f + E.energyMeasure g) (a • f + b • g) x ≤
            ε * (‖a‖ + ‖b‖))
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (hdom : ∀ f, E.energyMeasure f ≪ μ) :
    E.HasPairwiseEnergyDependence μ := by
  apply E.hasPairwiseEnergyDependence_of_piecewiseHarmonic μ hdom
  intro f g hf hg
  obtain ⟨n, hf⟩ := hf
  obtain ⟨m, hg⟩ := hg
  let N := max n m
  apply E.ae_pairDependence_of_pairMeasure f g _ μ hdom
  let P (x : CarpetPoints) := ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
    E.energyDensityRoot (E.energyMeasure f + E.energyMeasure g) (a • f + b • g) x ≤
      ε * (‖a‖ + ‖b‖)
  have hw (w : Fin N → Fin 8) :
      ∀ᵐ x ∂(E.energyMeasure f + E.energyMeasure g), x ∈ range (wordMap (List.ofFn w)) → P x := by
    have hF := IsInteriorHarmonic.of_piecewise_at_le E (le_max_left n m) hf w
    have hG := IsInteriorHarmonic.of_piecewise_at_le E (le_max_right n m) hg w
    exact (ae_restrict_iff' (measurableEmbedding_wordMap (List.ofFn w)).measurableSet_range).mp
      (E.ae_pairDependence_on_word _ f g (h _ _ hF hG))
  filter_upwards [ae_all_iff.mpr hw] with x hx
  obtain ⟨w, hmem⟩ := exists_wordMap_range N x
  exact hx w hmem

end CarpetEnergy.SelfSimilarPEnergy
