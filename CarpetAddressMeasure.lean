import AddressMeasureComparison
import CarpetMeasure

/-!
# Measuring symbolic cylinders against carpet sets

The pushforward relation identifies a cylinder with its corresponding cell
modulo null sets. This gives the cell fraction used in the blowup argument.
-/

open Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

private theorem uniform_digit_singleton (i : Fin 8) :
    uniformOn (univ : Set (Fin 8)) {i} = (8 : ℝ≥0∞)⁻¹ := by
  have h := uniformOn_apply_finset (s := (Finset.univ : Finset (Fin 8))) (t := {i})
  rw [Finset.coe_univ, Finset.coe_singleton, Finset.univ_inter, Finset.card_singleton,
    Finset.card_univ, Fintype.card_fin, Nat.cast_one, div_eq_mul_inv, one_mul] at h
  exact h

theorem addressMeasure_cylinder {n : ℕ} (w : Fin n → Fin 8) :
    addressMeasure (addressCylinder w) = ((8 : ℝ≥0∞)⁻¹) ^ n := by
  let t (k : ℕ) : Set (Fin 8) := if h : k < n then {w ⟨k, h⟩} else univ
  have hc : addressCylinder w = Set.pi (↑(Finset.range n) : Set ℕ) t := by
    ext s
    change addressPrefix n s = w ↔ s ∈ Set.pi (↑(Finset.range n) : Set ℕ) t
    rw [Set.mem_pi]
    constructor
    · intro h k hk
      have hkn := Finset.mem_range.mp hk
      simp only [t, dite_eq_left hkn, mem_singleton_iff]
      exact congrFun h ⟨k, hkn⟩
    · intro h
      funext k
      have hk := h k.val (Finset.mem_range.mpr k.isLt)
      simpa only [t, dite_eq_left k.isLt, mem_singleton_iff, addressPrefix] using hk
  rw [hc]
  change (Measure.infinitePi fun _ : ℕ ↦ uniformOn (univ : Set (Fin 8))) _ = _
  rw [Measure.infinitePi_pi _ (fun _ _ ↦ MeasurableSet.of_discrete)]
  calc
    _ = ∏ _ ∈ Finset.range n, (8 : ℝ≥0∞)⁻¹ := by
      apply Finset.prod_congr rfl
      intro i hi
      have hin := Finset.mem_range.mp hi
      have ht : t i = {w ⟨i, hin⟩} := dite_eq_left hin
      rw [ht, uniform_digit_singleton]
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

theorem coding_mem_range_prefix (n : ℕ) (s : Addresses) :
    coding s ∈ range (wordMap (List.ofFn (addressPrefix n s))) := by
  induction n generalizing s with
  | zero => exact ⟨coding s, rfl⟩
  | succ n ih =>
    let t : Addresses := fun j ↦ s (j + 1)
    have hs : prepend (s 0) t = s := by funext k; cases k <;> rfl
    have htuple : addressPrefix (n + 1) s = Fin.cons (s 0) (addressPrefix n t) := by
      funext j
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · rw [Fin.cons_zero]
        rfl
      · rw [Fin.cons_succ]
        rfl
    obtain ⟨y, hy⟩ := ih t
    refine ⟨y, ?_⟩
    rw [htuple, List.ofFn_cons]
    change cellMap (s 0) (wordMap (List.ofFn (addressPrefix n t)) y) = coding s
    rw [hy, ← coding_prepend, hs]

/-- A cylinder and the inverse image of its carpet cell agree modulo address-measure zero. -/
theorem addressCylinder_ae_eq_preimage_range_wordMap {n : ℕ} (w : Fin n → Fin 8) :
    addressCylinder w =ᵐ[addressMeasure] coding ⁻¹' range (wordMap (List.ofFn w)) := by
  have hsub : addressCylinder w ⊆ coding ⁻¹' range (wordMap (List.ofFn w)) := by
    intro s hs
    change addressPrefix n s = w at hs
    exact hs ▸ coding_mem_range_prefix n s
  have hmass : addressMeasure (addressCylinder w) =
      addressMeasure (coding ⁻¹' range (wordMap (List.ofFn w))) := by
    rw [addressMeasure_cylinder, ← Measure.map_apply continuous_coding.measurable
      (measurableEmbedding_wordMap (List.ofFn w)).measurableSet_range]
    change ((8 : ℝ≥0∞)⁻¹) ^ n = carpetMeasure (range (wordMap (List.ofFn w)))
    rw [carpetMeasure_range_wordMap, List.length_ofFn]
  exact ae_eq_of_subset_of_measure_ge hsub hmass.ge (measurableSet_addressCylinder w).nullMeasurableSet
    (measure_ne_top _ _)

/-- The normalized carpet probability scales on images under every word map. -/
theorem carpetMeasure_image_wordMap (w : List (Fin 8)) {A : Set CarpetPoints}
    (hA : MeasurableSet A) :
    carpetMeasure (wordMap w '' A) = ((8 : ℝ≥0∞)⁻¹) ^ w.length * carpetMeasure A := by
  induction w with
  | nil => simp only [wordMap, image_id, List.length_nil, pow_zero, one_mul]
  | cons i w ih =>
    simp only [wordMap, image_comp, List.length_cons]
    rw [carpetMeasure_image_cellMap i ((measurableEmbedding_wordMap w).measurableSet_image.mpr hA),
      ih, pow_succ', mul_assoc]

/-- The joint mass of a cylinder and a coded carpet set equals the cylinder
mass times the relative carpet mass of the set in that cell. -/
theorem addressMeasure_inter_preimage_coding_cylinder {n : ℕ} (w : Fin n → Fin 8)
    {A : Set CarpetPoints} (hA : MeasurableSet A) :
    addressMeasure (coding ⁻¹' A ∩ addressCylinder w) =
      addressMeasure (addressCylinder w) * carpetMeasure (wordMap (List.ofFn w) ⁻¹' A) := by
  let F := wordMap (List.ofFn w)
  have hF := measurableEmbedding_wordMap (List.ofFn w)
  calc
    _ = addressMeasure (coding ⁻¹' (A ∩ range F)) := by
      rw [preimage_inter]
      exact measure_congr (Filter.EventuallyEqSet.rfl.inter (addressCylinder_ae_eq_preimage_range_wordMap w))
    _ = carpetMeasure (A ∩ range F) :=
      (Measure.map_apply continuous_coding.measurable (hA.inter hF.measurableSet_range)).symm
    _ = carpetMeasure (F '' (F ⁻¹' A)) := congrArg carpetMeasure image_preimage_eq_inter_range.symm
    _ = _ := by
      rw [carpetMeasure_image_wordMap _ (hF.measurable hA), List.length_ofFn, addressMeasure_cylinder]

end CarpetEnergy
