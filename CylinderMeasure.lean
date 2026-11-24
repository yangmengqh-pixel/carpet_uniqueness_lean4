import CarpetCoding
import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Measures with consistent masses on address cylinders

Finite words are indexed by tuples of length `n`. Compatible nonnegative
masses on those tuples specify a finite measure by Kolmogorov extension.
-/

open Function MeasureTheory Preorder Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

/-- The first `n` symbols of an address. -/
def addressPrefix (n : ℕ) (s : Addresses) (i : Fin n) : Fin 8 := s i

/-- The addresses whose initial tuple is the given word. -/
def addressCylinder {n : ℕ} (w : Fin n → Fin 8) : Set Addresses :=
  addressPrefix n ⁻¹' {w}

theorem measurable_addressPrefix (n : ℕ) : Measurable (addressPrefix n) :=
  Measurable.of_eval fun i ↦ measurable_pi_apply i.val

theorem measurableSet_addressCylinder {n : ℕ} (w : Fin n → Fin 8) :
    MeasurableSet (addressCylinder w) := measurable_addressPrefix n (measurableSet_singleton w)

theorem addressCylinder_zero (w : Fin 0 → Fin 8) : addressCylinder w = univ := by
  ext s
  exact ⟨fun _ ↦ mem_univ _, fun _ ↦ Subsingleton.elim _ _⟩

/-- A consistent family of finite masses on the address cylinders. -/
structure CylinderMasses where
  mass (n : ℕ) : (Fin n → Fin 8) → ℝ≥0
  sum_snoc (n : ℕ) (w : Fin n → Fin 8) :
    (∑ i : Fin 8, mass (n + 1) (Fin.snoc w i)) = mass n w

namespace CylinderMasses

private abbrev AddressAlphabet : ℕ → Type := fun _ ↦ Fin 8

private def intervalTuple (n : ℕ) : (Fin n.succ → Fin 8) ≃ (↑(Finset.Iic n) → Fin 8) where
  toFun w i := w ⟨i.val, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.property)⟩
  invFun w i := w ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def finiteMarginal (W : CylinderMasses) (n : ℕ) :
    Measure (↑(Finset.Iic n) → Fin 8) :=
  Measure.sum (fun w : Fin n.succ → Fin 8 ↦
    (W.mass n.succ w : ℝ≥0∞) • Measure.dirac (intervalTuple n w))

private instance (W : CylinderMasses) (n : ℕ) : IsFiniteMeasure (W.finiteMarginal n) := by
  constructor
  rw [finiteMarginal, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  simp only [smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  exact ENNReal.sum_lt_top.mpr fun _ _ ↦ ENNReal.coe_lt_top

private theorem finiteMarginal_singleton (W : CylinderMasses) (n : ℕ) (w : Fin n.succ → Fin 8) :
    W.finiteMarginal n {intervalTuple n w} = (W.mass n.succ w : ℝ≥0∞) := by
  rw [finiteMarginal, Measure.sum_apply _ (measurableSet_singleton _), tsum_fintype,
    Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    have hne : intervalTuple n v ∉ {intervalTuple n w} := fun h ↦
      hv ((intervalTuple n).injective (mem_singleton_iff.mp h))
    rw [smul_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
      indicator_of_notMem hne, smul_zero]
  · simp

private theorem restrict_snoc_intervalTuple (n : ℕ) (w : Fin n.succ → Fin 8) (i : Fin 8) :
    frestrictLe₂ (π := AddressAlphabet) n.le_succ (intervalTuple (n + 1) (Fin.snoc w i)) = intervalTuple n w := by
  funext j
  let k : Fin n.succ := ⟨j.val, Nat.lt_succ_of_le (Finset.mem_Iic.mp j.property)⟩
  change Fin.snoc (α := fun _ : Fin (n + 2) ↦ Fin 8) w i k.castSucc = w k
  rw [Fin.snoc_castSucc]

private theorem map_finiteMarginal_succ (W : CylinderMasses) (n : ℕ) :
    (W.finiteMarginal (n + 1)).map (frestrictLe₂ (π := AddressAlphabet) n.le_succ) = W.finiteMarginal n := by
  classical
  ext A hA
  rw [Measure.map_apply (measurable_frestrictLe₂ (X := AddressAlphabet) _) hA]
  rw [finiteMarginal, finiteMarginal, Measure.sum_apply _ (measurable_frestrictLe₂ (X := AddressAlphabet) _ hA),
    Measure.sum_apply _ hA, tsum_fintype, tsum_fintype]
  let e : ((Fin n.succ → Fin 8) × Fin 8) ≃ (Fin (n + 2) → Fin 8) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ ↦ Fin 8))
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro w _
  have h (i : Fin 8) :
      (Measure.dirac (intervalTuple (n + 1) (e (w, i))))
          (frestrictLe₂ (π := AddressAlphabet) n.le_succ ⁻¹' A) = (Measure.dirac (intervalTuple n w)) A := by
    change (Measure.dirac (intervalTuple (n + 1) (Fin.snoc w i))) _ = _
    rw [← Measure.map_apply (measurable_frestrictLe₂ (X := AddressAlphabet) _) hA, Measure.map_dirac,
      restrict_snoc_intervalTuple]
  simp only [h]
  rw [← Finset.sum_mul, ← ENNReal.ofNNReal_finsetSum]
  change ((∑ i : Fin 8, W.mass (n + 2) (Fin.snoc w i) : ℝ≥0) : ℝ≥0∞) * _ = _
  rw [W.sum_snoc]

private theorem map_finiteMarginal (W : CylinderMasses) (a b : ℕ) (hab : a ≤ b) :
    (W.finiteMarginal b).map (frestrictLe₂ (π := AddressAlphabet) hab) = W.finiteMarginal a := by
  induction b, hab using Nat.le_induction with
  | base =>
    change (W.finiteMarginal a).map id = _
    exact Measure.map_id
  | succ b hab ih =>
    rw [← frestrictLe₂_comp_frestrictLe₂ (π := AddressAlphabet) hab b.le_succ,
      ← Measure.map_map (measurable_frestrictLe₂ (X := AddressAlphabet) _) (measurable_frestrictLe₂ (X := AddressAlphabet) _),
      W.map_finiteMarginal_succ, ih]

private noncomputable def family (W : CylinderMasses) (s : Finset ℕ) :
    Measure (↑s → Fin 8) :=
  inducedFamily (X := AddressAlphabet) W.finiteMarginal s

private instance (W : CylinderMasses) (s : Finset ℕ) : IsFiniteMeasure (W.family s) :=
  inferInstanceAs (IsFiniteMeasure (inducedFamily (X := AddressAlphabet) W.finiteMarginal s))

private theorem projective_family (W : CylinderMasses) : IsProjectiveMeasureFamily (α := AddressAlphabet) W.family :=
  isProjectiveMeasureFamily_inducedFamily (X := AddressAlphabet) W.finiteMarginal W.map_finiteMarginal

/-- The finite measure on addresses obtained by Kolmogorov extension. -/
noncomputable def measure (W : CylinderMasses) : Measure Addresses :=
  projectiveLimit (α := AddressAlphabet) W.family W.projective_family

instance (W : CylinderMasses) : IsFiniteMeasure W.measure :=
  inferInstanceAs (IsFiniteMeasure (projectiveLimit (α := AddressAlphabet) W.family W.projective_family))

private theorem map_frestrictLe_measure (W : CylinderMasses) (n : ℕ) :
    W.measure.map (frestrictLe (π := AddressAlphabet) n) = W.finiteMarginal n := by
  have h := isProjectiveLimit_projectiveLimit (α := AddressAlphabet) W.projective_family (Finset.Iic n)
  exact h.trans (inducedFamily_Iic (X := AddressAlphabet) W.finiteMarginal n)

private theorem preimage_intervalTuple_singleton (n : ℕ) (w : Fin n.succ → Fin 8) :
    frestrictLe (π := AddressAlphabet) n ⁻¹' {intervalTuple n w} = addressCylinder w := by
  ext s
  change frestrictLe n s = intervalTuple n w ↔ addressPrefix n.succ s = w
  change intervalTuple n (addressPrefix n.succ s) = intervalTuple n w ↔ _
  exact (intervalTuple n).injective.eq_iff

theorem measure_cylinder_succ (W : CylinderMasses) (n : ℕ) (w : Fin n.succ → Fin 8) :
    W.measure (addressCylinder w) = (W.mass n.succ w : ℝ≥0∞) := by
  rw [← preimage_intervalTuple_singleton, ← Measure.map_apply (measurable_frestrictLe (X := AddressAlphabet) _)
    (measurableSet_singleton _), W.map_frestrictLe_measure, W.finiteMarginal_singleton]

theorem measure_univ (W : CylinderMasses) :
    W.measure univ = (W.mass 0 Fin.elim0 : ℝ≥0∞) := by
  rw [← preimage_univ (f := frestrictLe (π := AddressAlphabet) 0),
    ← Measure.map_apply (measurable_frestrictLe (X := AddressAlphabet) 0) MeasurableSet.univ, W.map_frestrictLe_measure,
    finiteMarginal, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  simp only [smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  rw [← (Fin.snocEquiv (fun _ : Fin 1 ↦ Fin 8)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.snocEquiv_apply, Fintype.sum_unique, ← ENNReal.ofNNReal_finsetSum]
  exact congrArg ((↑) : ℝ≥0 → ℝ≥0∞) (W.sum_snoc 0 Fin.elim0)

theorem measure_cylinder (W : CylinderMasses) {n : ℕ} (w : Fin n → Fin 8) :
    W.measure (addressCylinder w) = (W.mass n w : ℝ≥0∞) := by
  cases n with
  | zero =>
    obtain rfl : w = Fin.elim0 := Subsingleton.elim _ _
    rw [addressCylinder_zero, W.measure_univ]
  | succ n => exact W.measure_cylinder_succ n w

/-- Agreement on all initial cylinders determines the measure. -/
theorem eq_measure_of_cylinders (W : CylinderMasses) (ν : Measure Addresses)
    (hν : ∀ (n : ℕ) (w : Fin n → Fin 8), ν (addressCylinder w) = (W.mass n w : ℝ≥0∞)) :
    ν = W.measure := by
  apply IsProjectiveLimit.unique (α := AddressAlphabet) (P := W.family) _
    (isProjectiveLimit_projectiveLimit (α := AddressAlphabet) W.projective_family)
  apply (isProjectiveLimit_nat_iff (X := AddressAlphabet) W.projective_family ν).2
  intro n
  rw [show W.family (Finset.Iic n) = W.finiteMarginal n from inducedFamily_Iic (X := AddressAlphabet) _ _]
  apply Measure.ext_of_singleton
  intro a
  obtain ⟨w, rfl⟩ := (intervalTuple n).surjective a
  rw [Measure.map_apply (measurable_frestrictLe (X := AddressAlphabet) _) (measurableSet_singleton _),
    preimage_intervalTuple_singleton, hν, W.finiteMarginal_singleton]

theorem measurable_prepend (i : Fin 8) : Measurable (prepend i) := by
  apply Measurable.of_eval
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

private theorem prefix_prepend (n : ℕ) (i : Fin 8) (s : Addresses) :
    addressPrefix (n + 1) (prepend i s) = Fin.cons i (addressPrefix n s) := by
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp only [Fin.cons_zero]
    rfl
  · simp only [Fin.cons_succ]
    rfl

/-- Prepending a digit removes it from a matching cylinder and misses every other cylinder. -/
theorem prepend_preimage_cylinder {n : ℕ} (i j : Fin 8) (w : Fin n → Fin 8) :
    prepend i ⁻¹' addressCylinder (Fin.cons j w) =
      if i = j then addressCylinder w else ∅ := by
  ext s
  change addressPrefix (n + 1) (prepend i s) = Fin.cons j w ↔ s ∈ _
  rw [prefix_prepend, Fin.cons_inj]
  by_cases h : i = j
  · simp only [h, true_and, ite_true]
    rfl
  · simp only [h, false_and, ite_false, mem_empty_iff_false]

/-- The measure breaks up over first symbols. The input measures specify
the masses obtained by dropping the first symbol from each cylinder. -/
theorem measure_eq_sum_prepend (W : CylinderMasses) (ν : Fin 8 → Measure Addresses)
    (hν : ∀ (i : Fin 8) (n : ℕ) (w : Fin n → Fin 8),
      ν i (addressCylinder w) = (W.mass (n + 1) (Fin.cons i w) : ℝ≥0∞)) :
    W.measure = Measure.sum (fun i ↦ (ν i).map (prepend i)) := by
  symm
  apply W.eq_measure_of_cylinders
  intro n w
  rw [Measure.sum_apply _ (measurableSet_addressCylinder w), tsum_fintype]
  simp only [Measure.map_apply (measurable_prepend _) (measurableSet_addressCylinder w)]
  cases n with
  | zero =>
    have hsum := W.sum_snoc 0 w
    have hcons (i : Fin 8) :
        Fin.cons i w = Fin.snoc (α := fun _ : Fin 1 ↦ Fin 8) w i := by
      funext j
      rw [Fin.eq_zero j]
      simp [Fin.snoc]
    have hmass (i : Fin 8) : ν i univ = (W.mass 1 (Fin.snoc w i) : ℝ≥0∞) := by
      rw [← addressCylinder_zero w, hν, hcons]
    simp only [addressCylinder_zero, preimage_univ, hmass, ← ENNReal.ofNNReal_finsetSum, hsum]
  | succ n =>
    rw [← Fin.cons_self_tail w]
    simp only [prepend_preimage_cylinder]
    rw [Finset.sum_eq_single (w 0)]
    · rw [ite_eq_left (show w 0 = w 0 from rfl)]
      exact hν (w 0) n (Fin.tail w)
    · intro i _ hi
      rw [ite_eq_right hi, measure_empty]
    · simp

private def scale (W : CylinderMasses) (c : ℝ≥0) : CylinderMasses where
  mass n w := c * W.mass n w
  sum_snoc n w := by rw [← Finset.mul_sum, W.sum_snoc]

private theorem measure_scale (W : CylinderMasses) (c : ℝ≥0) :
    (W.scale c).measure = (c : ℝ≥0∞) • W.measure := by
  symm
  apply (W.scale c).eq_measure_of_cylinders
  intro n w
  rw [smul_apply, smul_eq_mul, W.measure_cylinder]
  change _ = ((c * W.mass n w : ℝ≥0) : ℝ≥0∞)
  rw [ENNReal.coe_mul]

private theorem measure_le (W V : CylinderMasses)
    (h : ∀ (n : ℕ) (w : Fin n → Fin 8), W.mass n w ≤ V.mass n w) :
    W.measure ≤ V.measure := by
  let D : CylinderMasses :=
    { mass := fun n w ↦ V.mass n w - W.mass n w
      sum_snoc := fun n w ↦ by
        rw [Finset.sum_tsub_distrib _ (fun i _ ↦ h _ _), V.sum_snoc, W.sum_snoc] }
  have hmeasure : W.measure + D.measure = V.measure := by
    apply V.eq_measure_of_cylinders
    intro n w
    rw [add_apply, W.measure_cylinder, D.measure_cylinder, ← ENNReal.coe_add]
    exact congrArg ((↑) : ℝ≥0 → ℝ≥0∞) (add_tsub_cancel_of_le (h n w))
  rw [← hmeasure]
  exact le_add_of_nonneg_right bot_le

/-- A uniform comparison of cylinder masses gives the same comparison of measures. -/
theorem measure_le_smul_of_mass_le (W V : CylinderMasses) (c : ℝ≥0)
    (h : ∀ (n : ℕ) (w : Fin n → Fin 8), W.mass n w ≤ c * V.mass n w) :
    W.measure ≤ (c : ℝ≥0∞) • V.measure := by
  rw [← V.measure_scale c]
  exact W.measure_le (V.scale c) h

end CylinderMasses

end CarpetEnergy
