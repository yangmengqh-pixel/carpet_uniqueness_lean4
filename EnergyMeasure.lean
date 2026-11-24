import PEnergy
import CylinderMeasure

/-!
# Energy measures of a self-similar p-energy

The mass of a cylinder is the energy of the pullback along that word multiplied
by the corresponding power of the scaling factor.
-/

open Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Pullback by the first-level cell, with its membership in the energy domain. -/
noncomputable def pullback (i : Fin 8) (f : E.domain) : E.domain :=
  ⟨cellPullback i f, by
    obtain ⟨ρ, _, hρ⟩ := E.selfSimilar
    obtain ⟨g, hg, _⟩ := hρ f
    rw [(cellPullback_isLpPullback i (f : CarpetLp p)).unique (hg i)]
    exact (g i).property⟩

/-- The scalar in the self-similarity equation (SSEe). -/
def IsScalingFactor (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : E.domain, (E.energy f : ℝ) =
    ρ * ∑ i : Fin 8, (E.energy (E.pullback i f) : ℝ)

theorem exists_scalingFactor : ∃ ρ, E.IsScalingFactor ρ := by
  obtain ⟨ρ, hpos, hρ⟩ := E.selfSimilar
  refine ⟨ρ, hpos, fun f ↦ ?_⟩
  obtain ⟨g, hg, heq⟩ := hρ f
  have hfun (i : Fin 8) : E.pullback i f = g i := by
    exact Subtype.ext ((cellPullback_isLpPullback i (f : CarpetLp p)).unique (hg i))
  simpa only [hfun] using heq

private theorem coding_constant_address (i : Fin 8) :
    (coding (fun _ ↦ i) : Plane) = cellCenter i := by
  have h : prepend i (fun _ ↦ i) = (fun _ ↦ i : Addresses) := by
    funext n
    cases n <;> rfl
  have hfix := congrArg (fun x : CarpetPoints ↦ (x : Plane)) (coding_prepend i (fun _ ↦ i))
  rw [h] at hfix
  ext j
  have hj := congrArg (fun x : Plane ↦ x j) hfix
  change (coding (fun _ ↦ i) : Plane) j = cellSimilarity i (coding (fun _ ↦ i)) j at hj
  rw [cellSimilarity_coord] at hj
  linarith

/-- Regularity and the kernel condition force the energy to be nonzero. -/
theorem exists_energy_ne_zero : ∃ f : E.domain, E.energy f ≠ 0 := by
  let u : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ (x : Plane) 0,
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_subtypeVal⟩
  let x₀ := coding (fun _ ↦ (0 : Fin 8))
  let x₁ := coding (fun _ ↦ (4 : Fin 8))
  have hu₀ : u x₀ = 0 := by
    change (coding (fun _ ↦ (0 : Fin 8)) : Plane) 0 = 0
    rw [coding_constant_address]
    rfl
  have hu₁ : u x₁ = 1 := by
    change (coding (fun _ ↦ (4 : Fin 8)) : Plane) 0 = 1
    rw [coding_constant_address]
    rfl
  obtain ⟨v, hv, hvu⟩ := E.regular_sup u (1 / 3) (by norm_num)
  refine ⟨⟨continuousLp p v, hv⟩, fun h ↦ ?_⟩
  obtain ⟨a, ha⟩ := (E.zero_iff_constant ⟨continuousLp p v, hv⟩).1 h
  change continuousLp p v = constantLp p a at ha
  have hconst : (v : CarpetPoints → ℝ) = fun _ ↦ a := by
    apply Measure.eq_of_ae_eq (μ := carpetMeasure) _ v.continuous continuous_const
    apply (continuousLp_ae_eq p v).symm.trans
    rw [ha]
    exact Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a
  have hv₀ := (v - u).norm_coe_le_norm x₀
  have hv₁ := (v - u).norm_coe_le_norm x₁
  change ‖v x₀ - u x₀‖ ≤ _ at hv₀
  change ‖v x₁ - u x₁‖ ≤ _ at hv₁
  rw [Real.norm_eq_abs, congrFun hconst x₀, hu₀, sub_zero] at hv₀
  rw [Real.norm_eq_abs, congrFun hconst x₁, hu₁] at hv₁
  linarith [le_abs_self a, neg_le_abs (a - 1)]

theorem existsUnique_scalingFactor : ∃! ρ, E.IsScalingFactor ρ := by
  obtain ⟨ρ, hρ⟩ := E.exists_scalingFactor
  refine ⟨ρ, hρ, fun s hs ↦ ?_⟩
  obtain ⟨f, hf⟩ := E.exists_energy_ne_zero
  have hsum : (∑ i : Fin 8, (E.energy (E.pullback i f) : ℝ)) ≠ 0 := by
    intro h
    apply hf
    have hz : (E.energy f : ℝ) = 0 := by rw [hρ.2 f, h, mul_zero]
    exact_mod_cast hz
  exact mul_right_cancel₀ hsum ((hs.2 f).symm.trans (hρ.2 f))

/-- The unique positive scaling factor of the energy in (SSEe). -/
noncomputable def scalingFactor : ℝ :=
  E.existsUnique_scalingFactor.exists.choose

theorem isScalingFactor_scalingFactor : E.IsScalingFactor E.scalingFactor :=
  E.existsUnique_scalingFactor.exists.choose_spec

/-- Iterated pullback in the order of the manuscript's word composition. -/
noncomputable def pullbackWord : List (Fin 8) → E.domain → E.domain
  | [], f => f
  | i :: w, f => pullbackWord w (E.pullback i f)

theorem pullbackWord_append (w v : List (Fin 8)) (f : E.domain) :
    E.pullbackWord (w ++ v) f = E.pullbackWord v (E.pullbackWord w f) := by
  induction w generalizing f with
  | nil => rfl
  | cons i w ih => exact ih (E.pullback i f)

theorem quasiMeasurePreserving_wordMap (w : List (Fin 8)) :
    QuasiMeasurePreserving (wordMap w) carpetMeasure carpetMeasure := by
  induction w with
  | nil => exact QuasiMeasurePreserving.id carpetMeasure
  | cons i w ih =>
    have hi : QuasiMeasurePreserving (cellMap i) carpetMeasure carpetMeasure :=
      ⟨(measurableEmbedding_cellMap i).measurable.aemeasurable, map_cellMap_absolutelyContinuous i⟩
    exact hi.comp ih

theorem pullbackWord_isLpPullback (w : List (Fin 8)) (f : E.domain) :
    IsLpPullback (p := p) (wordMap w) f (E.pullbackWord w f) := by
  induction w generalizing f with
  | nil => exact Filter.EventuallyEq.rfl
  | cons i w ih =>
    have h₁ := ih (E.pullback i f)
    have h₂ := cellPullback_isLpPullback i (f : CarpetLp p)
    exact h₁.trans ((quasiMeasurePreserving_wordMap w).ae_eq_comp h₂)

private theorem ofFn_snoc {n : ℕ} (w : Fin n → Fin 8) (i : Fin 8) :
    List.ofFn (Fin.snoc w i) = List.ofFn w ++ [i] := by
  rw [List.ofFn_succ', Fin.snoc_last]
  simp only [Fin.snoc_castSucc, List.concat_eq_append]

private theorem sum_energy_pullback (f : E.domain) :
    E.scalingFactor.toNNReal * ∑ i : Fin 8, E.energy (E.pullback i f) = E.energy f := by
  have h := E.isScalingFactor_scalingFactor
  apply NNReal.eq
  push_cast
  rw [Real.coe_toNNReal _ h.1.le]
  exact (h.2 f).symm

/-- The masses prescribed by self-similarity, before pushing forward to the carpet. -/
noncomputable def cylinderMasses (f : E.domain) : CylinderMasses where
  mass n w := E.scalingFactor.toNNReal ^ n * E.energy (E.pullbackWord (List.ofFn w) f)
  sum_snoc n w := by
    simp only [ofFn_snoc, E.pullbackWord_append, pullbackWord, pow_succ]
    rw [← Finset.mul_sum, mul_assoc, E.sum_energy_pullback]

/-- The finite symbolic energy measure of a domain function. -/
noncomputable def symbolicEnergyMeasure (f : E.domain) : Measure Addresses :=
  (E.cylinderMasses f).measure

instance (f : E.domain) : IsFiniteMeasure (E.symbolicEnergyMeasure f) :=
  inferInstanceAs (IsFiniteMeasure (E.cylinderMasses f).measure)

theorem symbolicEnergyMeasure_cylinder (f : E.domain) {n : ℕ} (w : Fin n → Fin 8) :
    E.symbolicEnergyMeasure f (addressCylinder w) =
      (ENNReal.ofReal E.scalingFactor) ^ n * (E.energy (E.pullbackWord (List.ofFn w) f) : ℝ≥0∞) := by
  rw [symbolicEnergyMeasure, CylinderMasses.measure_cylinder]
  change ((E.scalingFactor.toNNReal ^ n *
    E.energy (E.pullbackWord (List.ofFn w) f) : ℝ≥0) : ℝ≥0∞) = _
  rw [ENNReal.coe_mul, ENNReal.coe_pow]
  rfl

theorem symbolicEnergyMeasure_univ (f : E.domain) :
    E.symbolicEnergyMeasure f univ = (E.energy f : ℝ≥0∞) := by
  rw [symbolicEnergyMeasure, CylinderMasses.measure_univ]
  simp [cylinderMasses, pullbackWord]

/-- The energy measure on the carpet, obtained by pushing forward along the address map. -/
noncomputable def energyMeasure (f : E.domain) : Measure CarpetPoints :=
  (E.symbolicEnergyMeasure f).map coding

instance (f : E.domain) : IsFiniteMeasure (E.energyMeasure f) :=
  inferInstanceAs (IsFiniteMeasure ((E.symbolicEnergyMeasure f).map coding))

theorem energyMeasure_univ (f : E.domain) :
    E.energyMeasure f univ = (E.energy f : ℝ≥0∞) := by
  rw [energyMeasure, Measure.map_apply continuous_coding.measurable MeasurableSet.univ,
    preimage_univ, E.symbolicEnergyMeasure_univ]

theorem symbolicEnergyMeasure_eq_sum_prepend (f : E.domain) :
    E.symbolicEnergyMeasure f = Measure.sum (fun i : Fin 8 ↦
      (ENNReal.ofReal E.scalingFactor •
        E.symbolicEnergyMeasure (E.pullback i f)).map (prepend i)) := by
  apply (E.cylinderMasses f).measure_eq_sum_prepend
  intro i n w
  rw [smul_apply, smul_eq_mul, E.symbolicEnergyMeasure_cylinder]
  change _ = ((E.scalingFactor.toNNReal ^ (n + 1) *
    E.energy (E.pullbackWord (List.ofFn (Fin.cons i w)) f) : ℝ≥0) : ℝ≥0∞)
  rw [ENNReal.coe_mul, ENNReal.coe_pow, List.ofFn_cons, pullbackWord, pow_succ', mul_assoc]
  rfl

/-- The self-similar measure identity (3.2) at the first level. -/
theorem energyMeasure_eq_sum_cells (f : E.domain) :
    E.energyMeasure f = Measure.sum (fun i : Fin 8 ↦
      ENNReal.ofReal E.scalingFactor • (E.energyMeasure (E.pullback i f)).map (cellMap i)) := by
  conv_lhs => rw [energyMeasure, E.symbolicEnergyMeasure_eq_sum_prepend]
  rw [Measure.map_sum continuous_coding.measurable.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_map continuous_coding.measurable (CylinderMasses.measurable_prepend i),
    Measure.map_smul _ (continuous_coding.measurable.comp
      (CylinderMasses.measurable_prepend i)).aemeasurable, energyMeasure,
    Measure.map_map (measurableEmbedding_cellMap i).measurable continuous_coding.measurable]
  exact congrArg (fun g : Addresses → CarpetPoints ↦
    ENNReal.ofReal E.scalingFactor • (E.symbolicEnergyMeasure (E.pullback i f)).map g)
    (funext (coding_prepend i))

/-- The energy measure decomposition (3.2) over all words of a given length. -/
theorem energyMeasure_eq_sum_words (n : ℕ) (f : E.domain) :
    E.energyMeasure f = Measure.sum (fun w : Fin n → Fin 8 ↦
      (ENNReal.ofReal E.scalingFactor) ^ n •
        (E.energyMeasure (E.pullbackWord (List.ofFn w) f)).map (wordMap (List.ofFn w))) := by
  classical
  induction n generalizing f with
  | zero =>
    ext A hA
    rw [Measure.sum_apply _ hA, tsum_fintype, Fintype.sum_unique]
    simp [List.ofFn_zero, pullbackWord, wordMap]
  | succ n ih =>
    ext A hA
    conv_lhs => rw [E.energyMeasure_eq_sum_cells, Measure.sum_apply _ hA, tsum_fintype]
    rw [Measure.sum_apply _ hA, tsum_fintype, ← (Fin.consEquiv (fun _ ↦ Fin 8)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    have hi := (measurableEmbedding_cellMap i).measurable
    rw [smul_apply, smul_eq_mul, Measure.map_apply hi hA, ih (E.pullback i f),
      Measure.sum_apply _ (hi hA), tsum_fintype, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Fin.consEquiv_apply, List.ofFn_cons, pullbackWord, wordMap, smul_apply, smul_eq_mul]
    rw [← Measure.map_apply hi hA,
      Measure.map_map hi (measurableEmbedding_wordMap (List.ofFn w)).measurable,
      pow_succ', mul_assoc]

theorem pullbackWord_inclusion {D : SelfSimilarPEnergy p} (hdom : E.domain ≤ D.domain)
    (w : List (Fin 8)) (f : E.domain) :
    Submodule.inclusion hdom (E.pullbackWord w f) =
      D.pullbackWord w (Submodule.inclusion hdom f) := by
  induction w generalizing f with
  | nil => rfl
  | cons i w ih =>
    rw [pullbackWord, pullbackWord, ih]
    exact congrArg (D.pullbackWord w) (Subtype.ext rfl)

/-- If the scaling factors agree, an energy comparison on an included domain
passes to the associated energy measures. This is the measure-comparison step
in Lemma 7.1. -/
theorem energyMeasure_le_of_energy_le (D : SelfSimilarPEnergy p)
    (hdom : E.domain ≤ D.domain) (hscale : E.scalingFactor = D.scalingFactor)
    (c : ℝ≥0) (henergy : ∀ f : E.domain,
      E.energy f ≤ c * D.energy (Submodule.inclusion hdom f)) (f : E.domain) :
    E.energyMeasure f ≤ (c : ℝ≥0∞) • D.energyMeasure (Submodule.inclusion hdom f) := by
  rw [energyMeasure, energyMeasure, ← Measure.map_smul _ continuous_coding.measurable.aemeasurable]
  apply Measure.map_mono _ continuous_coding.measurable
  apply CylinderMasses.measure_le_smul_of_mass_le
  intro n w
  change E.scalingFactor.toNNReal ^ n * E.energy (E.pullbackWord (List.ofFn w) f) ≤
    c * (D.scalingFactor.toNNReal ^ n *
      D.energy (D.pullbackWord (List.ofFn w) (Submodule.inclusion hdom f)))
  rw [hscale, mul_left_comm c, ← E.pullbackWord_inclusion hdom]
  exact mul_le_mul_of_nonneg_left (henergy _) bot_le

end CarpetEnergy.SelfSimilarPEnergy
