import EnergyComponent
import AddressMeasureComparison

/-!
# A component dominating the energy

An invariant restriction of an energy measure has prescribed masses on
address cylinders. A lower comparison on those cylinders extends to the
whole address space. Applying it to the complement of the invariant set
proves that the complement has zero energy measure.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem symbolicEnergyMeasure_inter_cylinder_cons (f : E.domain)
    {B : Set Addresses} (hB : MeasurableSet B) (i : Fin 8) {n : ℕ} (w : Fin n → Fin 8) :
    E.symbolicEnergyMeasure f (B ∩ addressCylinder (Fin.cons i w)) =
      ENNReal.ofReal E.scalingFactor *
        E.symbolicEnergyMeasure (E.pullback i f) (prepend i ⁻¹' B ∩ addressCylinder w) := by
  let A := B ∩ addressCylinder (Fin.cons i w)
  have hA : MeasurableSet A := hB.inter (measurableSet_addressCylinder _)
  change (E.symbolicEnergyMeasure f) A = _
  rw [E.symbolicEnergyMeasure_eq_sum_prepend, Measure.sum_apply _ hA, tsum_fintype]
  rw [Finset.sum_eq_single i]
  · rw [Measure.map_apply (CylinderMasses.measurable_prepend i) hA, smul_apply, smul_eq_mul]
    change ENNReal.ofReal E.scalingFactor *
      E.symbolicEnergyMeasure (E.pullback i f) (prepend i ⁻¹' (B ∩ addressCylinder (Fin.cons i w))) = _
    rw [preimage_inter, CylinderMasses.prepend_preimage_cylinder, ite_eq_left rfl]
  · intro j _ hj
    rw [Measure.map_apply (CylinderMasses.measurable_prepend j) hA]
    change (_ • E.symbolicEnergyMeasure (E.pullback j f))
      (prepend j ⁻¹' (B ∩ addressCylinder (Fin.cons i w))) = 0
    rw [preimage_inter, CylinderMasses.prepend_preimage_cylinder, ite_eq_right hj, inter_empty, measure_empty]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The restriction of the address energy measure to the coded inverse
image of an invariant set has the component's masses on all cylinders. -/
theorem symbolicEnergyMeasure_restrict_invariant_cylinder
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    {A : Set CarpetPoints} (hA : MeasurableSet A)
    (hcell : ∀ i, ∀ᵐ x ∂μ, cellMap i x ∈ A ↔ x ∈ A)
    (f : E.domain) {n : ℕ} (w : Fin n → Fin 8) :
    ((E.symbolicEnergyMeasure f).restrict (coding ⁻¹' A)) (addressCylinder w) =
      (ENNReal.ofReal E.scalingFactor) ^ n * E.energyMeasure (E.pullbackWord (List.ofFn w) f) A := by
  induction n generalizing f with
  | zero =>
    obtain rfl : w = Fin.elim0 := Subsingleton.elim _ _
    rw [addressCylinder_zero, Measure.restrict_apply_univ, pow_zero, one_mul, List.ofFn_zero,
      pullbackWord, energyMeasure, Measure.map_apply continuous_coding.measurable hA]
  | succ n ih =>
    let i := w 0
    let v := Fin.tail w
    have hv : Fin.cons i v = w := Fin.cons_self_tail _
    have hC (z : Fin n → Fin 8) :
        (E.symbolicEnergyMeasure (E.pullback i f)) (prepend i ⁻¹' (coding ⁻¹' A) ∩ addressCylinder z) =
          ((E.symbolicEnergyMeasure (E.pullback i f)).restrict (coding ⁻¹' A)) (addressCylinder z) := by
      rw [Measure.restrict_apply (measurableSet_addressCylinder z), inter_comm (addressCylinder z)]
      apply measure_congr
      apply Filter.EventuallyEqSet.inter _ Filter.EventuallyEqSet.rfl
      have ha : ∀ᵐ x ∂E.energyMeasure (E.pullback i f), cellMap i x ∈ A ↔ x ∈ A :=
        (hcell i).filter_mono (Measure.AbsolutelyContinuous.ae_le (hdom _))
      have hm : MeasurableSet {x | cellMap i x ∈ A ↔ x ∈ A} := by
        have he : {x | cellMap i x ∈ A ↔ x ∈ A} =
            (cellMap i ⁻¹' A) ∩ A ∪ (cellMap i ⁻¹' A)ᶜ ∩ Aᶜ := by
          ext x
          simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage, mem_compl_iff]
          tauto
        rw [he]
        exact ((hA.preimage (continuous_cellMap i).measurable).inter hA).union
          (((hA.preimage (continuous_cellMap i).measurable).compl).inter hA.compl)
      have hc : ∀ᵐ s ∂E.symbolicEnergyMeasure (E.pullback i f),
          cellMap i (coding s) ∈ A ↔ coding s ∈ A :=
        (ae_map_iff continuous_coding.measurable.aemeasurable hm).mp ha
      exact hc.mono fun s hs ↦ by
        change coding (prepend i s) ∈ A ↔ coding s ∈ A
        rw [coding_prepend]
        exact hs
    rw [← hv, Measure.restrict_apply (measurableSet_addressCylinder (Fin.cons i v)),
      inter_comm (addressCylinder _), E.symbolicEnergyMeasure_inter_cylinder_cons f
        (hA.preimage continuous_coding.measurable), hC, ih (E.pullback i f) v,
      List.ofFn_cons, pullbackWord, pow_succ', mul_assoc]

/-- A strictly positive lower bound by the full energy forces the
complement of the invariant set to have zero energy measure. -/
theorem energyMeasure_compl_eq_zero_of_invariant_dominates
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    {A : Set CarpetPoints} (hA : MeasurableSet A)
    (hcell : ∀ i, ∀ᵐ x ∂μ, cellMap i x ∈ A ↔ x ∈ A)
    {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ f, (c : ℝ≥0∞) * (E.energy f : ℝ≥0∞) ≤ E.energyMeasure f A)
    (f : E.domain) :
    E.energyMeasure f Aᶜ = 0 := by
  let ν := E.symbolicEnergyMeasure f
  let B := coding ⁻¹' A
  have hB : MeasurableSet B := hA.preimage continuous_coding.measurable
  have hle : ν ≤ ((c⁻¹ : ℝ≥0) : ℝ≥0∞) • ν.restrict B := by
    apply measure_le_smul_of_addressCylinder_le
    intro n w
    rw [show ν (addressCylinder w) = _ from E.symbolicEnergyMeasure_cylinder f w,
      show (ν.restrict B) (addressCylinder w) = _ from
        E.symbolicEnergyMeasure_restrict_invariant_cylinder hdom hA hcell f w]
    let s := (ENNReal.ofReal E.scalingFactor) ^ n
    let g := E.pullbackWord (List.ofFn w) f
    have hcancel : ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * (c : ℝ≥0∞) = 1 := by
      rw [ENNReal.coe_inv hc.ne', ENNReal.inv_mul_cancel (by exact_mod_cast hc.ne') ENNReal.coe_ne_top]
    change s * (E.energy g : ℝ≥0∞) ≤ ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * (s * E.energyMeasure g A)
    calc
      _ = (((c⁻¹ : ℝ≥0) : ℝ≥0∞) * (c : ℝ≥0∞)) * (s * (E.energy g : ℝ≥0∞)) := by
        rw [hcancel, one_mul]
      _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * (s * ((c : ℝ≥0∞) * (E.energy g : ℝ≥0∞))) := by ac_rfl
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl (h g))
  have hz := hle Bᶜ
  rw [smul_apply, smul_eq_mul, Measure.restrict_apply hB.compl, compl_inter_self, measure_empty, mul_zero] at hz
  rw [energyMeasure, Measure.map_apply continuous_coding.measurable hA.compl, preimage_compl]
  exact nonpos_iff_eq_zero.mp hz

/-- Minimal energy dominance equates a null set with a set of zero mass
for every energy measure. -/
theorem null_iff_forall_energyMeasure_null
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (hmin : ∀ ν : Measure CarpetPoints, (∀ f, E.energyMeasure f ≪ ν) → μ ≪ ν)
    {A : Set CarpetPoints} (hA : MeasurableSet A) :
    μ A = 0 ↔ ∀ f, E.energyMeasure f A = 0 := by
  refine ⟨fun h f ↦ hdom f h, fun h ↦ ?_⟩
  have hrestrict (f : E.domain) : E.energyMeasure f ≪ μ.restrict Aᶜ := by
    apply Measure.AbsolutelyContinuous.mk
    intro B hB hz
    rw [Measure.restrict_apply hB] at hz
    have h₁ : E.energyMeasure f (B ∩ Aᶜ) = 0 := hdom f hz
    have h₂ : E.energyMeasure f (B \ Aᶜ) = 0 := measure_mono_null (by
      intro x hx; exact not_not.mp hx.2) (h f)
    have hm := measure_inter_add_sdiff (μ := E.energyMeasure f) B hA.compl
    simpa only [h₁, h₂, add_zero] using hm.symm
  apply (hmin _ hrestrict)
  rw [Measure.restrict_apply hA, inter_compl_self, measure_empty]

/-- Lemma 6.8, stated in terms of the invariant restriction of the energy
measures and minimal energy dominance. -/
theorem invariant_full_measure_iff_energy_dominates
    {μ : Measure CarpetPoints} (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (hmin : ∀ ν : Measure CarpetPoints, (∀ f, E.energyMeasure f ≪ ν) → μ ≪ ν)
    {A : Set CarpetPoints} (hA : MeasurableSet A)
    (hcell : ∀ i, ∀ᵐ x ∂μ, cellMap i x ∈ A ↔ x ∈ A) :
    μ Aᶜ = 0 ↔ ∃ c : ℝ≥0, 0 < c ∧
        ∀ f, (c : ℝ≥0∞) * (E.energy f : ℝ≥0∞) ≤ E.energyMeasure f A := by
  constructor
  · intro h
    refine ⟨1, one_pos, fun f ↦ ?_⟩
    have hz := hdom f h
    have hsum := measure_add_measure_compl (μ := E.energyMeasure f) hA
    rw [hz, add_zero, E.energyMeasure_univ] at hsum
    rw [ENNReal.coe_one, one_mul, hsum]
  · rintro ⟨c, hc, h⟩
    exact (E.null_iff_forall_energyMeasure_null hdom hmin hA.compl).2
      (E.energyMeasure_compl_eq_zero_of_invariant_dominates hdom hA hcell hc h)

end CarpetEnergy.SelfSimilarPEnergy
