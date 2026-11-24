import EnergyMeasure
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Setwise seminorms of energy measures

The proof uses Minkowski's inequality on finite partitions of the address
space and extends the inequality to Borel sets by measure approximation.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem pullbackWord_add (w : List (Fin 8)) (f g : E.domain) :
    E.pullbackWord w (f + g) = E.pullbackWord w f + E.pullbackWord w g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [E.pullbackWord_isLpPullback w (f + g), E.pullbackWord_isLpPullback w f,
    E.pullbackWord_isLpPullback w g,
    (quasiMeasurePreserving_wordMap w).ae_eq_comp (Lp.coeFn_add (f : CarpetLp p) g),
    Lp.coeFn_add (E.pullbackWord w f : CarpetLp p) (E.pullbackWord w g : CarpetLp p)] with
    x hsum hf hg hsum' hsum''
  exact hsum.trans (hsum'.trans ((congrArg₂ (· + ·) hf.symm hg.symm).trans hsum''.symm))

theorem pullbackWord_smul (w : List (Fin 8)) (a : ℝ) (f : E.domain) :
    E.pullbackWord w (a • f) = a • E.pullbackWord w f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [E.pullbackWord_isLpPullback w (a • f), E.pullbackWord_isLpPullback w f,
    (quasiMeasurePreserving_wordMap w).ae_eq_comp (Lp.coeFn_smul a (f : CarpetLp p)),
    Lp.coeFn_smul a (E.pullbackWord w f : CarpetLp p)] with x h hf h' h''
  exact h.trans (h'.trans ((congrArg (fun v : ℝ ↦ a • v) hf.symm).trans h''.symm))

theorem symbolicEnergyMeasure_smul (a : ℝ) (f : E.domain) :
    E.symbolicEnergyMeasure (a • f) =
      ENNReal.ofReal (|a| ^ p) • E.symbolicEnergyMeasure f := by
  symm
  apply (E.cylinderMasses (a • f)).eq_measure_of_cylinders
  intro n w
  rw [← (E.cylinderMasses (a • f)).measure_cylinder w]
  change _ = E.symbolicEnergyMeasure (a • f) (addressCylinder w)
  rw [smul_apply, smul_eq_mul, E.symbolicEnergyMeasure_cylinder,
    E.symbolicEnergyMeasure_cylinder, E.pullbackWord_smul]
  have h : ((E.energy (a • E.pullbackWord (List.ofFn w) f)) : ℝ≥0∞) =
      ENNReal.ofReal (|a| ^ p) * (E.energy (E.pullbackWord (List.ofFn w) f) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, E.smul_energy,
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _), ENNReal.ofReal_coe_nnreal]
  rw [h, mul_left_comm]

theorem energyMeasure_smul (a : ℝ) (f : E.domain) :
    E.energyMeasure (a • f) = ENNReal.ofReal (|a| ^ p) • E.energyMeasure f := by
  rw [energyMeasure, E.symbolicEnergyMeasure_smul, Measure.map_smul _ (continuous_coding.measurable.aemeasurable)]
  rfl

theorem energyMeasure_zero : E.energyMeasure 0 = 0 := by
  have h := E.energyMeasure_smul 0 (0 : E.domain)
  rwa [zero_smul, abs_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt_p).ne',
    ENNReal.ofReal_zero, zero_smul] at h

private theorem exists_prefix_preimage {A : Set Addresses}
    (hA : A ∈ measurableCylinders (fun _ : ℕ ↦ Fin 8)) :
    ∃ (n : ℕ) (S : Set (Fin n → Fin 8)), A = addressPrefix n ⁻¹' S := by
  obtain ⟨J, T, _, rfl⟩ := (mem_measurableCylinders A).mp hA
  let n := J.sup id + 1
  let restrict : (Fin n → Fin 8) → (↑J → Fin 8) := fun w j ↦
    w ⟨j.val, Nat.lt_succ_of_le (Finset.le_sup (f := id) j.property)⟩
  exact ⟨n, restrict ⁻¹' T, rfl⟩

private theorem symbolicEnergyMeasure_prefix (f : E.domain) {n : ℕ}
    (S : Finset (Fin n → Fin 8)) :
    (E.symbolicEnergyMeasure f).real (addressPrefix n ⁻¹' (S : Set (Fin n → Fin 8))) =
      ∑ w ∈ S, E.scalingFactor ^ n * (E.energy (E.pullbackWord (List.ofFn w) f) : ℝ) := by
  classical
  have hset : addressPrefix n ⁻¹' (S : Set (Fin n → Fin 8)) =
      ⋃ w ∈ S, addressCylinder w := by
    ext s
    simp only [mem_preimage, Finset.mem_coe, mem_iUnion, addressCylinder, mem_singleton_iff]
    exact ⟨fun h ↦ ⟨addressPrefix n s, h, rfl⟩, fun ⟨w, hw, h⟩ ↦ h.symm ▸ hw⟩
  have hdisj : (S : Set (Fin n → Fin 8)).PairwiseDisjoint addressCylinder := by
    intro w _ v _ hwv
    change Disjoint (addressCylinder w) (addressCylinder v)
    rw [Set.disjoint_left]
    intro s hs ht
    exact hwv (hs.symm.trans ht)
  rw [Measure.real, hset, measure_biUnion_finset hdisj
    (fun w _ ↦ measurableSet_addressCylinder w)]
  rw [ENNReal.toReal_sum (fun w _ ↦ measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro w _
  rw [E.symbolicEnergyMeasure_cylinder, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal E.isScalingFactor_scalingFactor.1.le, ENNReal.coe_toReal]

private theorem symbolicEnergyMeasure_prefix_root_add_le (f g : E.domain) {n : ℕ}
    (S : Finset (Fin n → Fin 8)) :
    ((E.symbolicEnergyMeasure (f + g)).real (addressPrefix n ⁻¹' (S : Set _))) ^ p⁻¹ ≤
      ((E.symbolicEnergyMeasure f).real (addressPrefix n ⁻¹' (S : Set _))) ^ p⁻¹ +
      ((E.symbolicEnergyMeasure g).real (addressPrefix n ⁻¹' (S : Set _))) ^ p⁻¹ := by
  classical
  let a (u : E.domain) (w : Fin n → Fin 8) :=
    (E.scalingFactor ^ n) ^ p⁻¹ * E.rootSeminorm (E.pullbackWord (List.ofFn w) u)
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hρ : 0 ≤ E.scalingFactor ^ n := pow_nonneg E.isScalingFactor_scalingFactor.1.le _
  have ha (u : E.domain) (w : Fin n → Fin 8) : 0 ≤ a u w :=
    mul_nonneg (Real.rpow_nonneg hρ _) (apply_nonneg E.rootSeminorm _)
  have hap (u : E.domain) (w : Fin n → Fin 8) :
      (a u w) ^ p = E.scalingFactor ^ n * (E.energy (E.pullbackWord (List.ofFn w) u) : ℝ) := by
    dsimp only [a]
    have hE : 0 ≤ (E.energy (E.pullbackWord (List.ofFn w) u) : ℝ) := (E.energy _).property
    rw [Real.mul_rpow (Real.rpow_nonneg hρ _) (apply_nonneg E.rootSeminorm _),
      E.rootSeminorm_apply, Real.rpow_inv_rpow hρ hp.ne', Real.rpow_inv_rpow hE hp.ne']
  have hadd (w : Fin n → Fin 8) : a (f + g) w ≤ a f w + a g w := by
    dsimp only [a]
    rw [E.pullbackWord_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (map_add_le_add E.rootSeminorm _ _) (Real.rpow_nonneg hρ _)
  simp only [E.symbolicEnergyMeasure_prefix, ← hap]
  apply le_trans ?_ (by
    simpa only [one_div] using
      Real.Lp_add_le_of_nonneg S (f := a f) (g := a g) E.one_lt_p.le
        (fun w _ ↦ ha f w) (fun w _ ↦ ha g w))
  apply Real.rpow_le_rpow (Finset.sum_nonneg fun w _ ↦ Real.rpow_nonneg (ha (f + g) w) _)
    (Finset.sum_le_sum fun w _ ↦ Real.rpow_le_rpow (ha (f + g) w) (hadd w) hp.le)
    (inv_nonneg.mpr hp.le)

private theorem continuous_measure_real_of_le {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≤ ν) :
    Continuous (fun s : MeasuredSets ν ↦ μ.real (s : Set α)) := by
  let forget (s : MeasuredSets ν) : MeasuredSets μ := ⟨s, s.property⟩
  have hf : LipschitzWith 1 forget := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [MeasuredSets.dist_def, NNReal.coe_one, one_mul]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_iff'.1 h _)
  exact MeasuredSets.lipschitzWith_measureReal.continuous.comp hf.continuous

private theorem measure_real_root_add_le_of_prefix
    (μ₁ μ₂ μ₃ : Measure Addresses) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    {q : ℝ} (hq : 0 ≤ q)
    (hprefix : ∀ (n : ℕ) (S : Finset (Fin n → Fin 8)),
      (μ₁.real (addressPrefix n ⁻¹' (S : Set _))) ^ q ≤
      (μ₂.real (addressPrefix n ⁻¹' (S : Set _))) ^ q +
        (μ₃.real (addressPrefix n ⁻¹' (S : Set _))) ^ q)
    {A : Set Addresses} (hA : MeasurableSet A) :
    (μ₁.real A) ^ q ≤ (μ₂.real A) ^ q + (μ₃.real A) ^ q := by
  classical
  let ν : Measure Addresses := μ₁ + μ₂ + μ₃
  have : IsFiniteMeasure ν := by dsimp only [ν]; infer_instance
  have h₁ : μ₁ ≤ ν :=
    (le_add_of_nonneg_right (show 0 ≤ μ₂ from bot_le)).trans
      (le_add_of_nonneg_right (show 0 ≤ μ₃ from bot_le))
  have h₂ : μ₂ ≤ ν :=
    (le_add_of_nonneg_left (show 0 ≤ μ₁ from bot_le)).trans
      (le_add_of_nonneg_right (show 0 ≤ μ₃ from bot_le))
  have h₃ : μ₃ ≤ ν := le_add_of_nonneg_left (show 0 ≤ μ₁ + μ₂ from bot_le)
  let C := measurableCylinders (fun _ : ℕ ↦ Fin 8)
  have hcover : ∃ D : Set (Set Addresses), D.Countable ∧ D ⊆ C ∧ ν (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, countable_singleton _, ?_, by simp⟩
    exact singleton_subset_iff.mpr (univ_mem_measurableCylinders _)
  have hd : Dense ((SetLike.coe : MeasuredSets ν → Set Addresses) ⁻¹' C) :=
    dense_of_generateFrom_isSetRing isSetRing_measurableCylinders hcover
      generateFrom_measurableCylinders.symm
  let m (μ : Measure Addresses) (s : MeasuredSets ν) := (μ.real (s : Set Addresses)) ^ q
  have hc (μ : Measure Addresses) [IsFiniteMeasure μ] (hμ : μ ≤ ν) : Continuous (m μ) :=
    (Real.continuous_rpow_const hq).comp (continuous_measure_real_of_le hμ)
  have hclosed : IsClosed {s : MeasuredSets ν | m μ₁ s ≤ m μ₂ s + m μ₃ s} :=
    isClosed_le (hc _ h₁) ((hc _ h₂).add (hc _ h₃))
  have hbase : ((SetLike.coe : MeasuredSets ν → Set Addresses) ⁻¹' C) ⊆
      {s : MeasuredSets ν | m μ₁ s ≤ m μ₂ s + m μ₃ s} := by
    intro s hs
    obtain ⟨n, S, hS⟩ := exists_prefix_preimage hs
    have hS' : (s : Set Addresses) = addressPrefix n ⁻¹' (S.toFinset : Set (Fin n → Fin 8)) := by
      simpa only [Set.coe_toFinset] using hS
    change (μ₁.real (s : Set Addresses)) ^ q ≤
      (μ₂.real (s : Set Addresses)) ^ q + (μ₃.real (s : Set Addresses)) ^ q
    rw [hS']
    exact hprefix n S.toFinset
  have hcl := closure_minimal hbase hclosed
  exact hcl (by rw [hd.closure_eq]; exact mem_univ (⟨A, hA⟩ : MeasuredSets ν))

private theorem energyMeasure_root_add_le (f g : E.domain)
    {A : Set CarpetPoints} (hA : MeasurableSet A) :
    ((E.energyMeasure (f + g)).real A) ^ p⁻¹ ≤
      ((E.energyMeasure f).real A) ^ p⁻¹ + ((E.energyMeasure g).real A) ^ p⁻¹ := by
  simp only [Measure.real, energyMeasure, Measure.map_apply continuous_coding.measurable hA]
  exact measure_real_root_add_le_of_prefix
    (E.symbolicEnergyMeasure (f + g)) (E.symbolicEnergyMeasure f) (E.symbolicEnergyMeasure g)
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt_p).le)
    (fun _ ↦ E.symbolicEnergyMeasure_prefix_root_add_le f g) (continuous_coding.measurable hA)

private theorem energyMeasure_root_smul (A : Set CarpetPoints) (a : ℝ) (f : E.domain) :
    ((E.energyMeasure (a • f)).real A) ^ p⁻¹ =
      ‖a‖ * ((E.energyMeasure f).real A) ^ p⁻¹ := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  simp only [Measure.real, E.energyMeasure_smul, smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg a) _)]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) _) ENNReal.toReal_nonneg,
    Real.rpow_rpow_inv (abs_nonneg a) hp.ne', Real.norm_eq_abs]

/-- The seminorm given by the p-th root of the mass on a Borel set, as in Lemma 3.3(a). -/
noncomputable def energyMeasureSeminorm (A : Set CarpetPoints) (hA : MeasurableSet A) :
    Seminorm ℝ E.domain where
  toFun f := ((E.energyMeasure f).real A) ^ p⁻¹
  map_zero' := by
    rw [E.energyMeasure_zero]
    simp [Measure.real, Real.zero_rpow (inv_ne_zero (zero_lt_one.trans E.one_lt_p).ne')]
  add_le' f g := E.energyMeasure_root_add_le f g hA
  neg' f := by
    rw [← neg_one_smul ℝ f, E.energyMeasure_root_smul, norm_neg, norm_one, one_mul]
  smul' := E.energyMeasure_root_smul A

theorem energyMeasureSeminorm_apply (A : Set CarpetPoints) (hA : MeasurableSet A) (f : E.domain) :
    E.energyMeasureSeminorm A hA f = ((E.energyMeasure f).real A) ^ p⁻¹ := rfl

theorem energyMeasureSeminorm_le_rootSeminorm
    (A : Set CarpetPoints) (hA : MeasurableSet A) (f : E.domain) :
    E.energyMeasureSeminorm A hA f ≤ E.rootSeminorm f := by
  rw [E.energyMeasureSeminorm_apply, E.rootSeminorm_apply, Measure.real]
  have hmass : E.energyMeasure f A ≤ (E.energy f : ℝ≥0∞) := by
    rw [← E.energyMeasure_univ]
    exact measure_mono (subset_univ _)
  apply Real.rpow_le_rpow ENNReal.toReal_nonneg _
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt_p).le)
  exact ENNReal.toReal_mono ENNReal.coe_ne_top hmass

end CarpetEnergy.SelfSimilarPEnergy
