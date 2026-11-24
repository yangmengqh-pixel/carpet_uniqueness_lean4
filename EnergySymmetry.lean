import EnergyMeasure

/-!
# Covariance of energy measures under the square symmetries

A symmetry permutes the alphabet of the coding. Its pullback on the energy
domain induces the corresponding permutation of the symbolic energy measure.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CarpetEnergy

private def permuteAddress (e : Equiv.Perm (Fin 8)) (s : Addresses) : Addresses :=
  fun n ↦ e (s n)

private theorem measurable_permuteAddress (e : Equiv.Perm (Fin 8)) :
    Measurable (permuteAddress e) :=
  Measurable.of_eval fun n ↦ (measurable_of_finite e).comp (measurable_pi_apply n)

private theorem coding_permuteAddress (σ : SquareSymmetry) (e : Equiv.Perm (Fin 8))
    (h : ∀ i, carpetSymmetry σ ∘ cellMap i = cellMap (e i) ∘ carpetSymmetry σ)
    (s : Addresses) :
    coding (permuteAddress e s) = carpetSymmetry σ (coding s) := by
  have hdist (n : ℕ) (s : Addresses) :
      dist (coding (permuteAddress e s)) (carpetSymmetry σ (coding s)) ≤
        (1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints) := by
    induction n generalizing s with
    | zero =>
      rw [pow_zero, one_mul]
      exact dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
    | succ n ih =>
      let t : Addresses := fun k ↦ s (k + 1)
      have hs : prepend (s 0) t = s := by funext k; cases k <;> rfl
      have hperm : prepend (e (s 0)) (permuteAddress e t) = permuteAddress e s := by
        funext k
        cases k <;> rfl
      have h₁ := coding_prepend (e (s 0)) (permuteAddress e t)
      rw [hperm] at h₁
      have h₂ : carpetSymmetry σ (coding s) = cellMap (e (s 0)) (carpetSymmetry σ (coding t)) := by
        calc
          _ = carpetSymmetry σ (coding (prepend (s 0) t)) := by rw [hs]
          _ = carpetSymmetry σ (cellMap (s 0) (coding t)) := by rw [coding_prepend]
          _ = _ := congrFun (h (s 0)) (coding t)
      rw [h₁, h₂]
      change dist (cellSimilarity (e (s 0)) (coding (permuteAddress e t)))
        (cellSimilarity (e (s 0)) (carpetSymmetry σ (coding t))) ≤ _
      rw [dist_cellSimilarity, pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih t) (by norm_num)
  apply dist_le_zero.mp
  have hlim : Tendsto
      (fun n : ℕ ↦ (1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num)
        (by norm_num)).mul_const (diam (univ : Set CarpetPoints))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Eventually.of_forall (fun n ↦ hdist n s))

theorem wordMap_symmetry (σ : SquareSymmetry) (e : Equiv.Perm (Fin 8))
    (h : ∀ i, carpetSymmetry σ ∘ cellMap i = cellMap (e i) ∘ carpetSymmetry σ)
    (w : List (Fin 8)) (x : CarpetPoints) :
    carpetSymmetry σ (wordMap w x) = wordMap (w.map e) (carpetSymmetry σ x) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [wordMap, List.map_cons, comp_apply]
    exact (congrFun (h i) (wordMap w x)).trans (congrArg (cellMap (e i)) ih)

private theorem permuteAddress_preimage_cylinder (e : Equiv.Perm (Fin 8))
    {n : ℕ} (w : Fin n → Fin 8) :
    permuteAddress e ⁻¹' addressCylinder w = addressCylinder (e.symm ∘ w) := by
  ext s
  change (fun i : Fin n ↦ e (s i)) = w ↔ addressPrefix n s = e.symm ∘ w
  rw [funext_iff, funext_iff]
  exact forall_congr' fun i ↦ e.eq_symm_apply.symm

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Pullback by a symmetry as a function in the energy domain. -/
noncomputable def pullbackSymmetry (σ : SquareSymmetry) (f : E.domain) : E.domain :=
  ⟨symmetryPullback σ f, by
    obtain ⟨g, hg, _⟩ := E.symmetry σ f
    rw [(symmetryPullback_isLpPullback σ (f : CarpetLp p)).unique hg]
    exact g.property⟩

theorem energy_pullbackSymmetry (σ : SquareSymmetry) (f : E.domain) :
    E.energy (E.pullbackSymmetry σ f) = E.energy f := by
  obtain ⟨g, hg, he⟩ := E.symmetry σ f
  have h : E.pullbackSymmetry σ f = g :=
    Subtype.ext ((symmetryPullback_isLpPullback σ (f : CarpetLp p)).unique hg)
  rw [h, he]

theorem pullbackWord_pullbackSymmetry (σ : SquareSymmetry) (e : Equiv.Perm (Fin 8))
    (h : ∀ i, carpetSymmetry σ ∘ cellMap i = cellMap (e i) ∘ carpetSymmetry σ)
    (w : List (Fin 8)) (f : E.domain) :
    E.pullbackWord w (E.pullbackSymmetry σ f) =
      E.pullbackSymmetry σ (E.pullbackWord (w.map e) f) := by
  apply Subtype.ext
  apply Lp.ext
  have hleft := E.pullbackWord_isLpPullback w (E.pullbackSymmetry σ f)
  have hleft' := (quasiMeasurePreserving_wordMap w).ae_eq_comp
    (symmetryPullback_isLpPullback σ (f : CarpetLp p))
  have hright := symmetryPullback_isLpPullback σ
    (E.pullbackWord (w.map e) f : CarpetLp p)
  have hright' := (measurePreserving_carpetSymmetry σ).quasiMeasurePreserving.ae_eq_comp
    (E.pullbackWord_isLpPullback (w.map e) f)
  refine hleft.trans (hleft'.trans (Filter.EventuallyEq.trans ?_ (hright.trans hright').symm))
  exact Eventually.of_forall fun x ↦ congrArg (f : CarpetLp p) (wordMap_symmetry σ e h w x)

private theorem map_symbolicEnergyMeasure_symmetry (σ : SquareSymmetry) (e : Equiv.Perm (Fin 8))
    (h : ∀ i, carpetSymmetry σ ∘ cellMap i = cellMap (e i) ∘ carpetSymmetry σ)
    (f : E.domain) :
    (E.symbolicEnergyMeasure (E.pullbackSymmetry σ f)).map (permuteAddress e) =
      E.symbolicEnergyMeasure f := by
  apply (E.cylinderMasses f).eq_measure_of_cylinders
  intro n w
  rw [Measure.map_apply (measurable_permuteAddress e) (measurableSet_addressCylinder _),
    permuteAddress_preimage_cylinder, E.symbolicEnergyMeasure_cylinder,
    E.pullbackWord_pullbackSymmetry σ e h, E.energy_pullbackSymmetry]
  have hw : (List.ofFn (e.symm ∘ w)).map e = List.ofFn w := by
    rw [← List.ofFn_comp']
    congr
    funext i
    exact e.apply_symm_apply (w i)
  rw [hw]
  exact (E.symbolicEnergyMeasure_cylinder f w).symm.trans
    ((E.cylinderMasses f).measure_cylinder w)

/-- Mapping the measure of the pulled-back function by the symmetry gives the original measure. -/
theorem map_energyMeasure_symmetry (σ : SquareSymmetry) (f : E.domain) :
    (E.energyMeasure (E.pullbackSymmetry σ f)).map (carpetSymmetry σ) = E.energyMeasure f := by
  obtain ⟨e, he⟩ := exists_carpetSymmetry_cellPerm σ
  have hcomp : carpetSymmetry σ ∘ coding = coding ∘ permuteAddress e :=
    funext fun s ↦ (coding_permuteAddress σ e he s).symm
  rw [energyMeasure, energyMeasure,
    Measure.map_map (continuous_carpetSymmetry σ).measurable continuous_coding.measurable, hcomp,
    ← Measure.map_map continuous_coding.measurable (measurable_permuteAddress e),
    E.map_symbolicEnergyMeasure_symmetry σ e he]

/-- The symmetry covariance identity (3.3). -/
theorem energyMeasure_pullbackSymmetry (σ : SquareSymmetry) (f : E.domain) :
    E.energyMeasure (E.pullbackSymmetry σ f) =
      (E.energyMeasure f).map (carpetSymmetry (inverseSymmetry σ)) := by
  rw [← E.map_energyMeasure_symmetry σ f,
    Measure.map_map (continuous_carpetSymmetry (inverseSymmetry σ)).measurable
      (continuous_carpetSymmetry σ).measurable,
    (carpetSymmetry_leftInverse σ).comp_eq_id, Measure.map_id]

end SelfSimilarPEnergy
end CarpetEnergy
