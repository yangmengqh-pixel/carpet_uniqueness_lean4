import CylinderMeasure

/-!
# Comparing finite measures on the address space

The tables of cylinder masses of finite measures are consistent. This
allows the cylinder comparison theorem to be applied to arbitrary finite
measures, in particular to restrictions of the address probability.
-/

open Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

private theorem addressCylinder_eq_iUnion_snoc {n : ℕ} (w : Fin n → Fin 8) :
    addressCylinder w = ⋃ i : Fin 8, addressCylinder (Fin.snoc w i) := by
  ext s
  constructor
  · intro h
    apply mem_iUnion.mpr
    refine ⟨s n, ?_⟩
    change addressPrefix (n + 1) s = Fin.snoc w (s n)
    change addressPrefix n s = w at h
    funext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · rw [Fin.snoc_last]
      rfl
    · rw [Fin.snoc_castSucc]
      exact congrFun h i
  · intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    change addressPrefix n s = w
    change addressPrefix (n + 1) s = Fin.snoc w i at hi
    funext j
    exact (congrFun hi j.castSucc).trans (Fin.snoc_castSucc _ _ _)

private theorem pairwiseDisjoint_addressCylinder_snoc {n : ℕ} (w : Fin n → Fin 8) :
    Pairwise (Disjoint on fun i : Fin 8 ↦ addressCylinder (Fin.snoc w i)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro s hi hj
  change addressPrefix (n + 1) s = Fin.snoc w i at hi
  change addressPrefix (n + 1) s = Fin.snoc w j at hj
  have h := congrFun (hi.symm.trans hj) (Fin.last n)
  rw [Fin.snoc_last, Fin.snoc_last] at h
  exact hij h

namespace CylinderMasses

/-- The consistent cylinder masses obtained from a finite measure on addresses. -/
noncomputable def ofFiniteMeasure (μ : Measure Addresses) [IsFiniteMeasure μ] :
    CylinderMasses where
  mass _ w := (μ (addressCylinder w)).toNNReal
  sum_snoc n w := by
    apply ENNReal.coe_injective
    rw [ENNReal.ofNNReal_finsetSum, ENNReal.coe_toNNReal (measure_ne_top _ _),
      addressCylinder_eq_iUnion_snoc w, measure_iUnion (pairwiseDisjoint_addressCylinder_snoc w)
        (fun i ↦ measurableSet_addressCylinder (Fin.snoc w i)), tsum_fintype]
    exact Finset.sum_congr rfl fun _ _ ↦ ENNReal.coe_toNNReal (measure_ne_top _ _)

theorem measure_ofFiniteMeasure (μ : Measure Addresses) [IsFiniteMeasure μ] :
    (ofFiniteMeasure μ).measure = μ :=
  ((ofFiniteMeasure μ).eq_measure_of_cylinders μ
    (fun _ _ ↦ (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm)).symm

end CylinderMasses

/-- A uniform upper comparison on all address cylinders extends to all measurable sets. -/
theorem measure_le_smul_of_addressCylinder_le (μ ν : Measure Addresses)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ≥0)
    (h : ∀ (n : ℕ) (w : Fin n → Fin 8), μ (addressCylinder w) ≤ (c : ℝ≥0∞) * ν (addressCylinder w)) :
    μ ≤ (c : ℝ≥0∞) • ν := by
  have hmass (n : ℕ) (w : Fin n → Fin 8) :
      (CylinderMasses.ofFiniteMeasure μ).mass n w ≤ c * (CylinderMasses.ofFiniteMeasure ν).mass n w := by
    apply ENNReal.coe_le_coe.mp
    change ((μ (addressCylinder w)).toNNReal : ℝ≥0∞) ≤
      ((c * (ν (addressCylinder w)).toNNReal : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_toNNReal (measure_ne_top _ _), ENNReal.coe_mul,
      ENNReal.coe_toNNReal (measure_ne_top _ _)]
    exact h n w
  have hle := (CylinderMasses.ofFiniteMeasure μ).measure_le_smul_of_mass_le
    (CylinderMasses.ofFiniteMeasure ν) c hmass
  simpa only [CylinderMasses.measure_ofFiniteMeasure] using hle

/-- Every set of positive finite measure occupies more than a given
fraction below one of some address cylinder. -/
theorem exists_addressCylinder_large_fraction (μ : Measure Addresses) [IsFiniteMeasure μ]
    {A : Set Addresses} (hμA : μ A ≠ 0) {c : ℝ≥0} (hc : c < 1) :
    ∃ (n : ℕ) (w : Fin n → Fin 8),
      (c : ℝ≥0∞) * μ (addressCylinder w) < μ (A ∩ addressCylinder w) := by
  by_contra! h
  have hle : μ.restrict A ≤ (c : ℝ≥0∞) • μ := by
    apply measure_le_smul_of_addressCylinder_le
    intro n w
    rw [Measure.restrict_apply (measurableSet_addressCylinder w), inter_comm]
    exact h n w
  have hA' := hle A
  rw [Measure.restrict_apply_self, smul_apply, smul_eq_mul] at hA'
  have hlt : (c : ℝ≥0∞) * μ A < μ A := by
    calc
      _ < (1 : ℝ≥0∞) * μ A := ENNReal.mul_lt_mul_left hμA (measure_ne_top _ _) (by exact_mod_cast hc)
      _ = _ := one_mul _
  exact hlt.not_ge hA'

end CarpetEnergy
