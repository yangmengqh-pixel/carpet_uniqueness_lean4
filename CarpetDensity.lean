import CarpetFolding
import EnergyDominance
import InvariantDensity

/-!
# Common densities and carpet maps

The cell and symmetry identities identify two versions of a common density.
For cells, the restriction identity uses null overlaps, and folding supplies
the extensions of the continuous functions in the reference sequence.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The first-level restriction formula for energy measures with null cell intersections. -/
theorem energyMeasure_restrict_cell_of_null_intersections
    (h : ∀ (f : E.domain) ⦃i j : Fin 8⦄, i ≠ j →
      E.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (f : E.domain) (i : Fin 8) :
    (E.energyMeasure f).restrict (range (cellMap i)) =
      ENNReal.ofReal E.scalingFactor • (E.energyMeasure (E.pullback i f)).map (cellMap i) := by
  conv_lhs => rw [E.energyMeasure_eq_sum_cells]
  apply restrict_eq_smul_map_of_null_overlaps cellMap measurableEmbedding_cellMap
  intro j hj
  have hp : ENNReal.ofReal E.scalingFactor ≠ 0 :=
    (ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1).ne'
  have hac : (E.energyMeasure (E.pullback j f)).map (cellMap j) ≪ E.energyMeasure f := by
    conv_rhs => rw [E.energyMeasure_eq_sum_cells]
    exact Measure.absolutelyContinuous_sum_right j (Measure.absolutelyContinuous_smul hp)
  have hpre : cellMap j ⁻¹' (range (cellMap j) ∩ range (cellMap i)) =
      cellMap j ⁻¹' range (cellMap i) := by rw [preimage_inter, preimage_range, univ_inter]
  rw [← hpre, ← (measurableEmbedding_cellMap j).map_apply]
  exact hac (h f hj)

/-- The image formula of Lemma 7.2 for all finite words, given null first-level overlaps. -/
theorem energyMeasure_image_word_of_null_intersections
    (h : ∀ (f : E.domain) ⦃i j : Fin 8⦄, i ≠ j →
      E.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (f : E.domain) (w : List (Fin 8)) (A : Set CarpetPoints) :
    E.energyMeasure f (wordMap w '' A) =
      ENNReal.ofReal E.scalingFactor ^ w.length * E.energyMeasure (E.pullbackWord w f) A := by
  have hcell (g : E.domain) (i : Fin 8) (B : Set CarpetPoints) :
      E.energyMeasure g (cellMap i '' B) =
        ENNReal.ofReal E.scalingFactor * E.energyMeasure (E.pullback i g) B := by
    rw [← Measure.restrict_eq_self _ (image_subset_range _ _),
      E.energyMeasure_restrict_cell_of_null_intersections h,
      smul_apply, smul_eq_mul, (measurableEmbedding_cellMap i).map_apply,
      preimage_image_eq _ (injective_cellMap i)]
  induction w generalizing f with
  | nil => simp only [wordMap, image_id, List.length_nil, pow_zero, one_mul, pullbackWord]
  | cons i w ih =>
    simp only [wordMap, image_comp, List.length_cons, pullbackWord]
    rw [hcell, ih, pow_succ', mul_assoc]

/-- Restricting to a finite-word cell gives the scaled pushforward of the pullback measure. -/
theorem energyMeasure_restrict_word_of_null_intersections
    (h : ∀ (f : E.domain) ⦃i j : Fin 8⦄, i ≠ j →
      E.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (f : E.domain) (w : List (Fin 8)) :
    (E.energyMeasure f).restrict (range (wordMap w)) =
      (ENNReal.ofReal E.scalingFactor ^ w.length) •
        (E.energyMeasure (E.pullbackWord w f)).map (wordMap w) := by
  apply Measure.ext
  intro B hB
  rw [Measure.restrict_apply hB, smul_apply, smul_eq_mul, (measurableEmbedding_wordMap w).map_apply,
    ← E.energyMeasure_image_word_of_null_intersections h,
    image_preimage_eq_inter_range]

private theorem inclusion_pullbackSymmetry {D : SelfSimilarPEnergy p}
    (hED : E.domain ≤ D.domain) (σ : SquareSymmetry) (f : E.domain) :
    Submodule.inclusion hED (E.pullbackSymmetry σ f) =
      D.pullbackSymmetry σ (Submodule.inclusion hED f) :=
  Subtype.ext rfl

private theorem exists_pullbackWord_eq_of_continuous (w : List (Fin 8)) (f : E.domain)
    (h : ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (f : CarpetLp p)) :
    ∃ g : E.domain, E.pullbackWord w g = f := by
  obtain ⟨u, hu⟩ := h
  have hm : continuousLp p u ∈ E.domain := hu.symm ▸ f.property
  obtain ⟨v, hv, heq⟩ := E.exists_continuous_extension_word w u hm
  let g : E.domain := ⟨continuousLp p v, hv⟩
  refine ⟨g, Subtype.ext ?_⟩
  apply Lp.ext
  have h₁ := E.pullbackWord_isLpPullback w g
  have h₂ := (quasiMeasurePreserving_wordMap w).ae_eq_comp (continuousLp_ae_eq p v)
  rw [← hu]
  exact h₁.trans (h₂.trans (heq ▸ (continuousLp_ae_eq p u).symm))

/-- Word maps preserve null preimages of a reference measure built from a
continuous energy-dense sequence, as in (6.2). -/
theorem quasiMeasurePreserving_wordMap_energyReference
    (d : ℕ → E.domain)
    (hd : ∀ n, ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (d n : CarpetLp p))
    (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0))
    (w : List (Fin 8)) :
    QuasiMeasurePreserving (wordMap w) (E.energyReferenceMeasure d) (E.energyReferenceMeasure d) := by
  have hac (v : List (Fin 8)) (f : E.domain) :
      (E.energyMeasure (E.pullbackWord v f)).map (wordMap v) ≪ E.energyMeasure f := by
    induction v generalizing f with
    | nil =>
      simp only [pullbackWord, wordMap, Measure.map_id]
      exact Measure.AbsolutelyContinuous.rfl
    | cons i v ih =>
      have hi := measurableEmbedding_cellMap i
      have hcell : (E.energyMeasure (E.pullback i f)).map (cellMap i) ≪ E.energyMeasure f := by
        conv_rhs => rw [E.energyMeasure_eq_sum_cells f]
        exact Measure.absolutelyContinuous_sum_right i (Measure.absolutelyContinuous_smul
          (ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1).ne')
      rw [pullbackWord, wordMap, ← Measure.map_map hi.measurable
        (measurableEmbedding_wordMap v).measurable]
      exact (hi.absolutelyContinuous_map (ih (E.pullback i f))).trans hcell
  have hw := (measurableEmbedding_wordMap w).measurable
  refine ⟨hw.aemeasurable, Measure.AbsolutelyContinuous.mk fun A hA hnull ↦ ?_⟩
  rw [Measure.map_apply hw hA, energyReferenceMeasure, Measure.sum_apply _ (hw hA)]
  apply tsum_eq_zero_iff.mpr
  intro n
  obtain ⟨f, hf⟩ := E.exists_pullbackWord_eq_of_continuous w (d n) (hd n)
  have hz := ((hac w f).trans (E.energyMeasure_absolutelyContinuous_reference d hdense f)) hnull
  rw [Measure.map_apply hw hA, hf] at hz
  rw [smul_apply, smul_eq_mul, hz, mul_zero]

/-- A common density is invariant under every finite-word map. -/
theorem ae_eq_comp_wordMap_of_common_density
    (D : SelfSimilarPEnergy p) (hED : E.domain ≤ D.domain)
    (hscale : E.scalingFactor = D.scalingFactor)
    (hE : ∀ (f : E.domain) ⦃i j : Fin 8⦄, i ≠ j →
      E.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (hD : ∀ (f : D.domain) ⦃i j : Fin 8⦄, i ≠ j →
      D.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (d : ℕ → E.domain)
    (hd : ∀ n, ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (d n : CarpetLp p))
    {a : CarpetPoints → ℝ} (ha : Measurable a) (hna : ∀ x, 0 ≤ a x)
    (density : ∀ f : E.domain, D.energyMeasure (Submodule.inclusion hED f) =
      (E.energyMeasure f).withDensity fun x ↦ ENNReal.ofReal (a x))
    (w : List (Fin 8)) :
    a ∘ wordMap w =ᵐ[E.energyReferenceMeasure d] a := by
  exact ae_eq_comp_of_restrict_map_sum (measurableEmbedding_wordMap w) (E.pullbackWord w)
    E.energyMeasure (fun f ↦ D.energyMeasure (Submodule.inclusion hED f))
    (fun _ ↦ inferInstance) d (E.energyReferenceWeight d)
    (fun n ↦ E.exists_pullbackWord_eq_of_continuous w (d n) (hd n))
    (s := ENNReal.ofReal E.scalingFactor ^ w.length)
    (pow_ne_zero _ (ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ha hna density
    (fun f ↦ E.energyMeasure_restrict_word_of_null_intersections hE f w)
    (fun f ↦ by
      rw [E.pullbackWord_inclusion hED, hscale]
      exact D.energyMeasure_restrict_word_of_null_intersections hD _ w)

/-- A common density is invariant under a first-level map when both energy
measures have null cell intersections and the reference sequence is continuous. -/
theorem ae_eq_comp_cellMap_of_common_density
    (D : SelfSimilarPEnergy p) (hED : E.domain ≤ D.domain)
    (hscale : E.scalingFactor = D.scalingFactor)
    (hE : ∀ (f : E.domain) ⦃i j : Fin 8⦄, i ≠ j →
      E.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (hD : ∀ (f : D.domain) ⦃i j : Fin 8⦄, i ≠ j →
      D.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (d : ℕ → E.domain)
    (hd : ∀ n, ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (d n : CarpetLp p))
    {a : CarpetPoints → ℝ} (ha : Measurable a) (hna : ∀ x, 0 ≤ a x)
    (density : ∀ f : E.domain, D.energyMeasure (Submodule.inclusion hED f) =
      (E.energyMeasure f).withDensity fun x ↦ ENNReal.ofReal (a x))
    (i : Fin 8) :
    a ∘ cellMap i =ᵐ[E.energyReferenceMeasure d] a :=
  E.ae_eq_comp_wordMap_of_common_density D hED hscale hE hD d hd ha hna density [i]

private theorem pullbackSymmetry_leftInverse (σ : SquareSymmetry) (f : E.domain) :
    E.pullbackSymmetry σ (E.pullbackSymmetry (inverseSymmetry σ) f) = f := by
  apply Subtype.ext
  apply Lp.ext
  have h₁ := symmetryPullback_isLpPullback σ
    (E.pullbackSymmetry (inverseSymmetry σ) f : CarpetLp p)
  have h₂ := (measurePreserving_carpetSymmetry σ).quasiMeasurePreserving.ae_eq_comp
    (symmetryPullback_isLpPullback (inverseSymmetry σ) (f : CarpetLp p))
  exact h₁.trans (h₂.trans (Filter.Eventually.of_forall fun x ↦
    congrArg (f : CarpetLp p) (carpetSymmetry_leftInverse σ x)))

/-- A common density is invariant under each square symmetry. -/
theorem ae_eq_comp_carpetSymmetry_of_common_density
    (D : SelfSimilarPEnergy p) (hED : E.domain ≤ D.domain) (d : ℕ → E.domain)
    {a : CarpetPoints → ℝ} (ha : Measurable a) (hna : ∀ x, 0 ≤ a x)
    (density : ∀ f : E.domain, D.energyMeasure (Submodule.inclusion hED f) =
      (E.energyMeasure f).withDensity fun x ↦ ENNReal.ofReal (a x))
    (σ : SquareSymmetry) :
    a ∘ carpetSymmetry σ =ᵐ[E.energyReferenceMeasure d] a := by
  have hemb : MeasurableEmbedding (carpetSymmetry σ) :=
    ((continuous_carpetSymmetry σ).isClosedEmbedding
      (bijective_carpetSymmetry σ).1).measurableEmbedding
  have hrange : range (carpetSymmetry σ) = univ :=
    range_eq_univ.mpr (bijective_carpetSymmetry σ).2
  refine ae_eq_comp_of_restrict_map_sum hemb (E.pullbackSymmetry σ)
    E.energyMeasure (fun f ↦ D.energyMeasure (Submodule.inclusion hED f))
    (fun _ ↦ inferInstance) d (E.energyReferenceWeight d)
    (fun n ↦ ⟨E.pullbackSymmetry (inverseSymmetry σ) (d n),
      E.pullbackSymmetry_leftInverse σ (d n)⟩)
    (s := 1) one_ne_zero ENNReal.one_ne_top ha hna density ?_ ?_
  · intro f
    rw [hrange, Measure.restrict_univ, one_smul, E.map_energyMeasure_symmetry]
  · intro f
    rw [hrange, Measure.restrict_univ, one_smul, E.inclusion_pullbackSymmetry hED,
      D.map_energyMeasure_symmetry]

/-- The last step of the uniqueness argument from a bounded common density and
the zero-one law for the cell maps and the square symmetries. -/
theorem proportional_of_common_density
    (D : SelfSimilarPEnergy p) (hED : E.domain ≤ D.domain)
    (hscale : E.scalingFactor = D.scalingFactor)
    (hE : ∀ (f : E.domain) ⦃i j : Fin 8⦄, i ≠ j →
      E.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (hD : ∀ (f : D.domain) ⦃i j : Fin 8⦄, i ≠ j →
      D.energyMeasure f (range (cellMap i) ∩ range (cellMap j)) = 0)
    (d : ℕ → E.domain)
    (hcontinuous : ∀ n, ∃ u : C(CarpetPoints, ℝ), continuousLp p u = (d n : CarpetLp p))
    (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - d (j n))) atTop (𝓝 0))
    (hzeroOne : HasZeroOneLaw (E.energyReferenceMeasure d) (Sum.elim cellMap carpetSymmetry))
    {a : CarpetPoints → ℝ} (ha : Measurable a) (hna : ∀ x, 0 ≤ a x)
    {lower upper : ℝ} (hpos : 0 < lower) (hle : lower ≤ upper)
    (bounds : ∀ᵐ x ∂E.energyReferenceMeasure d, lower ≤ a x ∧ a x ≤ upper)
    (density : ∀ f : E.domain, D.energyMeasure (Submodule.inclusion hED f) =
      (E.energyMeasure f).withDensity fun x ↦ ENNReal.ofReal (a x)) :
    ∃ c ∈ Icc lower upper, 0 < c ∧ ∀ f : E.domain,
      D.energyMeasure (Submodule.inclusion hED f) = ENNReal.ofReal c • E.energyMeasure f ∧
      (D.energy (Submodule.inclusion hED f) : ℝ) = c * (E.energy f : ℝ) := by
  have invariant (i : Sum (Fin 8) SquareSymmetry) :
      a ∘ Sum.elim cellMap carpetSymmetry i =ᵐ[E.energyReferenceMeasure d] a := by
    rcases i with i | σ
    · exact E.ae_eq_comp_cellMap_of_common_density
        D hED hscale hE hD d hcontinuous ha hna density i
    · exact E.ae_eq_comp_carpetSymmetry_of_common_density D hED d ha hna density σ
  obtain ⟨c, hc, hcpos, h⟩ := proportional_of_invariant_density
    hzeroOne ha invariant hpos hle bounds
    (E.energyMeasure_absolutelyContinuous_reference d hdense) density
  refine ⟨c, hc, hcpos, fun f ↦ ⟨(h f).1, ?_⟩⟩
  simpa only [D.energyMeasure_univ, E.energyMeasure_univ, ENNReal.coe_toReal] using (h f).2

end CarpetEnergy.SelfSimilarPEnergy
