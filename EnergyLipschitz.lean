import EnergyLocality

/-!
# Lipschitz composition

Piecewise affine scalar maps are finite sums of shifted truncations. Each
truncation retains the original energy measure on its own open strip, so
estimating the energy of the sum costs only the largest absolute slope.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem energyMeasure_apply_le_iff {A : Set CarpetPoints}
    (hA : MeasurableSet A) (f g : E.domain) :
    E.energyMeasure f A ≤ E.energyMeasure g A ↔
      E.energyMeasureSeminorm A hA f ≤ E.energyMeasureSeminorm A hA g := by
  let μ := E.energyMeasure f
  let ν := E.energyMeasure g
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  rw [E.energyMeasureSeminorm_apply, E.energyMeasureSeminorm_apply, Measure.real, Measure.real,
    Real.rpow_le_rpow_iff ENNReal.toReal_nonneg ENNReal.toReal_nonneg (inv_pos.mpr hp)]
  refine ⟨ENNReal.toReal_mono (measure_ne_top ν A), fun h ↦ ?_⟩
  calc
    μ A = ENNReal.ofReal (μ A).toReal := (ENNReal.ofReal_toReal (measure_ne_top μ A)).symm
    _ ≤ ENNReal.ofReal (ν A).toReal := ENNReal.ofReal_le_ofReal h
    _ = ν A := ENNReal.ofReal_toReal (measure_ne_top ν A)

private theorem setwiseSeminorm_eq_zero_of_mass_eq_zero {A : Set CarpetPoints}
    (hA : MeasurableSet A) (g : E.domain) (h : E.energyMeasure g A = 0) :
    E.energyMeasureSeminorm A hA g = 0 := by
  rw [E.energyMeasureSeminorm_apply, Measure.real, h, ENNReal.toReal_zero,
    Real.zero_rpow (inv_ne_zero (zero_lt_one.trans E.one_lt_p).ne')]

private theorem seminorm_sum_le {ι : Type*} (S : Seminorm ℝ E.domain)
    (g : ι → E.domain) (s : Finset ι) : S (∑ i ∈ s, g i) ≤ ∑ i ∈ s, S (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero, le_rfl]
  | insert i s hi hs =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (map_add_le_add S _ _).trans (add_le_add_right hs _)

private theorem energyMeasure_sum_univ_le {ι : Type*} [Fintype ι]
    (A : ι → Set CarpetPoints) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Disjoint on A)) (g : ι → E.domain)
    (hsupp : ∀ i, E.energyMeasure (g i) (A i)ᶜ = 0) :
    E.energyMeasure (∑ i, g i) univ ≤ ∑ i, E.energyMeasure (g i) (A i) := by
  classical
  let B : Set CarpetPoints := ⋃ i, A i
  have hB : MeasurableSet B := MeasurableSet.iUnion hA
  let S := E.energyMeasureSeminorm Bᶜ hB.compl
  have hzero (i : ι) : S (g i) = 0 := by
    apply E.setwiseSeminorm_eq_zero_of_mass_eq_zero hB.compl
    exact measure_mono_null (compl_subset_compl.mpr (subset_iUnion A i)) (hsupp i)
  have hBc : E.energyMeasure (∑ i, g i) Bᶜ = 0 := by
    apply le_antisymm _ zero_le
    have hle : S (∑ i, g i) ≤ S 0 := by
      simpa only [hzero, Finset.sum_const_zero, map_zero] using
        (E.seminorm_sum_le S g Finset.univ)
    simpa only [E.energyMeasure_zero, zero_apply] using
      (E.energyMeasure_apply_le_iff hB.compl _ _).mpr hle
  have hpiece (i : ι) : E.energyMeasure (∑ j, g j) (A i) ≤ E.energyMeasure (g i) (A i) := by
    rw [E.energyMeasure_apply_le_iff (hA i)]
    let Q := E.energyMeasureSeminorm (A i) (hA i)
    calc
      Q (∑ j, g j) ≤ ∑ j, Q (g j) := E.seminorm_sum_le Q g Finset.univ
      _ = Q (g i) := by
        apply Finset.sum_eq_single i
        · intro j _ hj
          apply E.setwiseSeminorm_eq_zero_of_mass_eq_zero (hA i)
          exact measure_mono_null (fun _ hx ↦ disjoint_left.mp (hdisj hj.symm) hx) (hsupp j)
        · exact fun hi ↦ (hi (Finset.mem_univ i)).elim
  calc
    E.energyMeasure (∑ i, g i) univ = E.energyMeasure (∑ i, g i) B := by
      rw [← union_compl_self B, measure_union disjoint_compl_right hB.compl, hBc, add_zero]
    _ = ∑ i, E.energyMeasure (∑ j, g j) (A i) := by
      change E.energyMeasure (∑ i, g i) (⋃ i, A i) = _
      rw [measure_iUnion hdisj hA, tsum_fintype]
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ hpiece i

private theorem rootSeminorm_sum_shiftedTruncation_le {ι : Type*} [Fintype ι]
    (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain)
    (a b c : ι → ℝ) (hb : ∀ i, 0 < b i) {L : ℝ} (hL : 0 ≤ L)
    (hc : ∀ i, |c i| ≤ L) (hdisj : Pairwise (Disjoint on fun i ↦ Ioo (a i) (a i + b i))) :
    E.rootSeminorm (∑ i, c i • E.shiftedTruncation (a i) (b i) ⟨continuousLp p u, hu⟩) ≤
      L * E.rootSeminorm ⟨continuousLp p u, hu⟩ := by
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let A (i : ι) := u ⁻¹' Ioo (a i) (a i + b i)
  have hA (i : ι) : MeasurableSet (A i) := measurableSet_Ioo.preimage u.continuous.measurable
  have hd : Pairwise (Disjoint on A) := fun _ _ hij ↦ (hdisj hij).preimage u
  let g (i : ι) := c i • E.shiftedTruncation (a i) (b i) f
  have hg (i : ι) : E.energyMeasure (g i) =
      ENNReal.ofReal (|c i| ^ p) • (E.energyMeasure f).restrict (A i) := by
    exact (E.energyMeasure_smul (c i) (E.shiftedTruncation (a i) (b i) f)).trans
      (congrArg (ENNReal.ofReal (|c i| ^ p) • ·)
        (E.energyMeasure_shiftedTruncation_eq_restrict u hu (a i) (hb i)))
  have hmass : E.energyMeasure (∑ i, g i) univ ≤
      ENNReal.ofReal (L ^ p) * E.energyMeasure f univ := by
    calc
      _ ≤ ∑ i, E.energyMeasure (g i) (A i) :=
        E.energyMeasure_sum_univ_le A hA hd g fun i ↦ by
          rw [hg, smul_apply, smul_eq_mul, Measure.restrict_apply (hA i).compl,
            compl_inter_self, measure_empty, mul_zero]
      _ ≤ ∑ i, ENNReal.ofReal (L ^ p) * E.energyMeasure f (A i) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hg, smul_apply, smul_eq_mul, Measure.restrict_eq_self _ Subset.rfl]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (abs_nonneg _) (hc i) (zero_lt_one.trans E.one_lt_p).le)) le_rfl
      _ = ENNReal.ofReal (L ^ p) * E.energyMeasure f (⋃ i, A i) := by
        rw [measure_iUnion hd hA, tsum_fintype, Finset.mul_sum]
      _ ≤ _ := mul_le_mul' le_rfl (measure_mono (subset_univ _))
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hmass
  rw [E.energyMeasure_univ, E.energyMeasure_univ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hL _), ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
  change E.rootSeminorm (∑ i, g i) ≤ L * E.rootSeminorm f
  rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
  calc
    _ ≤ (L ^ p * (E.energy f : ℝ)) ^ p⁻¹ :=
      Real.rpow_le_rpow (E.energy (∑ i, g i)).property hreal (inv_nonneg.mpr hp.le)
    _ = (L ^ p) ^ p⁻¹ * (E.energy f : ℝ) ^ p⁻¹ :=
      Real.mul_rpow (Real.rpow_nonneg hL _) (E.energy f).property
    _ = _ := congrArg (· * (E.energy f : ℝ) ^ p⁻¹) (Real.rpow_rpow_inv hL hp.ne')

private def gridPoint (a b : ℝ) (i : ℕ) : ℝ := a + (i : ℝ) * b

private theorem gridPoint_succ (a b : ℝ) (i : ℕ) :
    gridPoint a b (i + 1) = gridPoint a b i + b := by
  simp only [gridPoint, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc]

private noncomputable def gridSlope (φ : ℝ → ℝ) (a b : ℝ) (i : ℕ) : ℝ :=
  (φ (gridPoint a b (i + 1)) - φ (gridPoint a b i)) / b

private noncomputable def gridInterpolation (φ : ℝ → ℝ) (a b : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  φ a + ∑ i ∈ Finset.range N, gridSlope φ a b i * min (max (t - gridPoint a b i) 0) b

private theorem abs_gridSlope_le {L : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith L φ)
    (a : ℝ) {b : ℝ} (hb : 0 < b) (i : ℕ) : |gridSlope φ a b i| ≤ (L : ℝ) := by
  rw [gridSlope, abs_div, abs_of_pos hb, div_le_iff₀ hb]
  have h := hφ.dist_le_mul (gridPoint a b (i + 1)) (gridPoint a b i)
  simpa only [Real.dist_eq, gridPoint_succ a b i, add_sub_cancel_left, abs_of_pos hb] using h

private theorem gridInterpolation_succ (φ : ℝ → ℝ) (a b : ℝ) (N : ℕ) (t : ℝ) :
    gridInterpolation φ a b (N + 1) t = gridInterpolation φ a b N t +
      gridSlope φ a b N * min (max (t - gridPoint a b N) 0) b := by
  simp only [gridInterpolation, Finset.sum_range_succ, add_assoc]

private theorem gridInterpolation_of_ge (φ : ℝ → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (N : ℕ) {t : ℝ} (ht : gridPoint a b N ≤ t) :
    gridInterpolation φ a b N t = φ (gridPoint a b N) := by
  induction N with
  | zero => simp only [gridInterpolation, Finset.range_zero, Finset.sum_empty, add_zero,
      gridPoint, Nat.cast_zero, zero_mul]
  | succ N ih =>
    have ht' : b ≤ t - gridPoint a b N := by
      rw [gridPoint_succ] at ht
      linarith only [ht]
    have hN : gridPoint a b N ≤ t := by linarith only [ht', hb]
    rw [gridInterpolation_succ, ih hN,
      min_eq_right (ht'.trans (le_max_left _ _)), gridSlope, div_mul_cancel₀ _ hb.ne']
    ring

private theorem abs_gridInterpolation_sub_le {L : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith L φ)
    (a : ℝ) {b : ℝ} (hb : 0 < b) (N : ℕ) {t : ℝ}
    (ht : a ≤ t) (ht' : t ≤ gridPoint a b N) :
    |gridInterpolation φ a b N t - φ t| ≤ 2 * (L : ℝ) * b := by
  induction N with
  | zero =>
    have heq : t = a := le_antisymm (by simpa only [gridPoint, Nat.cast_zero, zero_mul, add_zero]
      using ht') ht
    rw [heq, gridInterpolation, Finset.range_zero, Finset.sum_empty, add_zero, sub_self, abs_zero]
    positivity
  | succ N ih =>
    rw [gridInterpolation_succ]
    by_cases hN : t ≤ gridPoint a b N
    · rw [max_eq_right (sub_nonpos.mpr hN), min_eq_left hb.le, mul_zero, add_zero]
      exact ih hN
    · have hpos : 0 ≤ t - gridPoint a b N := sub_nonneg.mpr (lt_of_not_ge hN).le
      have hle : t - gridPoint a b N ≤ b := by
        rw [gridPoint_succ] at ht'
        linarith only [ht']
      rw [max_eq_left hpos, min_eq_left hle,
        gridInterpolation_of_ge φ a hb N (lt_of_not_ge hN).le, add_sub_right_comm]
      have h₁ : |φ (gridPoint a b N) - φ t| ≤ (L : ℝ) * b := by
        have h := hφ.dist_le_mul (gridPoint a b N) t
        rw [Real.dist_eq, dist_comm (gridPoint a b N) t, Real.dist_eq, abs_of_nonneg hpos] at h
        exact h.trans (mul_le_mul_of_nonneg_left hle L.coe_nonneg)
      have h₂ : |gridSlope φ a b N * (t - gridPoint a b N)| ≤ (L : ℝ) * b := by
        rw [abs_mul, abs_of_nonneg hpos]
        exact mul_le_mul (abs_gridSlope_le hφ a hb N) hle hpos L.coe_nonneg
      have h := (abs_add_le _ _).trans (add_le_add h₁ h₂)
      linarith only [h]

private theorem pairwise_disjoint_grid_strips (a : ℝ) {b : ℝ} (hb : 0 ≤ b)
    (N : ℕ) :
    Pairwise (Disjoint on fun i : Fin N ↦ Ioo (gridPoint a b i) (gridPoint a b i + b)) := by
  have ordered (i j : Fin N) (h : i < j) :
      gridPoint a b i + b ≤ gridPoint a b j := by
    rw [← gridPoint_succ a b i]
    exact add_le_add_right (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.succ_le_of_lt h) hb) a
  have disj (i j : Fin N) (h : i < j) :
      Disjoint (Ioo (gridPoint a b i) (gridPoint a b i + b))
        (Ioo (gridPoint a b j) (gridPoint a b j + b)) :=
    disjoint_left.mpr fun _ hi hj ↦ not_lt_of_ge (ordered i j h) (hj.1.trans hi.2)
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact disj i j hij
  · exact (disj j i hji).symm

private noncomputable def interpolateDomain {u : C(CarpetPoints, ℝ)}
    (hu : continuousLp p u ∈ E.domain) (φ : ℝ → ℝ) (a b : ℝ) (N : ℕ) : E.domain :=
  (∑ i : Fin N, gridSlope φ a b i •
    E.shiftedTruncation (gridPoint a b i) b ⟨continuousLp p u, hu⟩) +
    ⟨constantLp p (φ a), E.constant_mem (φ a)⟩

private theorem interpolateDomain_ae {u : C(CarpetPoints, ℝ)}
    (hu : continuousLp p u ∈ E.domain) (φ : ℝ → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    (E.interpolateDomain hu φ a b N : CarpetLp p) =ᵐ[carpetMeasure]
      gridInterpolation φ a b N ∘ u := by
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let w (i : Fin N) := E.shiftedTruncation (gridPoint a b i) b f
  let g (i : Fin N) := gridSlope φ a b i • w i
  have hg (i : Fin N) : (g i : CarpetLp p) =ᵐ[carpetMeasure] fun x ↦
      gridSlope φ a b i * min (max (u x - gridPoint a b i) 0) b := by
    filter_upwards [Lp.coeFn_smul (gridSlope φ a b i) (w i : CarpetLp p),
      E.shiftedTruncation_ae (gridPoint a b i) hb f, continuousLp_ae_eq p u] with x h₁ h₂ h₃
    change (g i : CarpetLp p) x = gridSlope φ a b i * (w i : CarpetLp p) x at h₁
    change (w i : CarpetLp p) x = min (max ((f : CarpetLp p) x - gridPoint a b i) 0) b at h₂
    change (f : CarpetLp p) x = u x at h₃
    rw [h₁, h₂, h₃]
  have hsum : ((∑ i, g i : E.domain) : CarpetLp p) =ᵐ[carpetMeasure]
      fun x ↦ ∑ i : Fin N, (g i : CarpetLp p) x := by
    rw [Submodule.coe_sum]
    exact Lp.coeFn_fun_finsetSum ..
  let c := constantLp p (φ a)
  filter_upwards [hsum, ae_all_iff.mpr hg, Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (φ a),
    Lp.coeFn_add ((∑ i, g i : E.domain) : CarpetLp p) c] with x h₁ h₂ h₃ h₄
  change (E.interpolateDomain hu φ a b N : CarpetLp p) x =
    ((∑ i, g i : E.domain) : CarpetLp p) x + c x at h₄
  change c x = φ a at h₃
  change (E.interpolateDomain hu φ a b N : CarpetLp p) x = gridInterpolation φ a b N (u x)
  rw [h₄, h₁, h₃, add_comm, gridInterpolation, ← Fin.sum_univ_eq_sum_range]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ h₂ i

private theorem exists_comp_continuousLp {u : C(CarpetPoints, ℝ)}
    (hu : continuousLp p u ∈ E.domain) {L : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith L φ) :
    ∃ g : E.domain,
      (g : CarpetLp p) = continuousLp p ((⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp u) ∧
      E.rootSeminorm g ≤ (L : ℝ) * E.rootSeminorm ⟨continuousLp p u, hu⟩ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  let a : ℝ := -‖u‖
  let B : ℝ := 2 * ‖u‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let b (n : ℕ) : ℝ := B * (1 / ((n : ℝ) + 1))
  have hb (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  have hbB (n : ℕ) : b n ≤ B := by
    change B * (1 / ((n : ℝ) + 1)) ≤ B
    exact mul_le_of_le_one_right hB.le
      ((div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n)))
  have ht (n : ℕ) (x : CarpetPoints) : a ≤ u x ∧ u x ≤ gridPoint a (b n) (n + 1) := by
    have hux := abs_le.mp ((Real.norm_eq_abs (u x)) ▸ u.norm_coe_le_norm x)
    refine ⟨hux.1, ?_⟩
    have hgrid : gridPoint a (b n) (n + 1) = a + B := by
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      simp only [gridPoint, b, Nat.cast_add, Nat.cast_one]
      field_simp [hn]
    rw [hgrid]
    dsimp only [a, B]
    linarith only [hux.2]
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let g (n : ℕ) := E.interpolateDomain hu φ a (b n) (n + 1)
  let v : C(CarpetPoints, ℝ) := (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp u
  let fv := continuousLp p v
  have hbound (n : ℕ) : E.rootSeminorm (g n) ≤ (L : ℝ) * E.rootSeminorm f := by
    have hs := E.rootSeminorm_sum_shiftedTruncation_le u hu
      (fun i : Fin (n + 1) ↦ gridPoint a (b n) i) (fun _ ↦ b n)
      (fun i ↦ gridSlope φ a (b n) i) (fun _ ↦ hb n) L.coe_nonneg
      (fun i ↦ abs_gridSlope_le hφ a (hb n) i) (pairwise_disjoint_grid_strips a (hb n).le (n + 1))
    change E.rootSeminorm (g n) ≤ _
    unfold g interpolateDomain
    rw [E.rootSeminorm_apply, E.add_constant, ← E.rootSeminorm_apply]
    exact hs
  have hdist (n : ℕ) : ‖(g n : CarpetLp p) - fv‖ ≤ 2 * (L : ℝ) * b n := by
    apply norm_carpetLp_le_of_ae_bound _ (mul_nonneg (by positivity) (hb n).le)
    filter_upwards [E.interpolateDomain_ae hu φ a (hb n) (n + 1), continuousLp_ae_eq p v,
      Lp.coeFn_sub (g n : CarpetLp p) fv] with x h₁ h₂ h₃
    change (g n : CarpetLp p) x = gridInterpolation φ a (b n) (n + 1) (u x) at h₁
    change fv x = φ (u x) at h₂
    change ((g n : CarpetLp p) - fv) x = (g n : CarpetLp p) x - fv x at h₃
    rw [h₃, h₁, h₂, Real.norm_eq_abs]
    exact abs_gridInterpolation_sub_le hφ a (hb n) (n + 1) (ht n x).1 (ht n x).2
  have hlim : Tendsto (fun n ↦ (g n : CarpetLp p)) atTop (𝓝 fv) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have h₀ : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h₁ : Tendsto (fun n ↦ 2 * (L : ℝ) * b n) atTop (𝓝 0) := by
      simpa only [b, mul_zero] using (h₀.const_mul B).const_mul (2 * (L : ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h₁
      (fun _ ↦ norm_nonneg _) hdist
  have hgraph (n : ℕ) : E.graphSeminorm (g n) ≤
      (((L : ℝ) * E.rootSeminorm f) ^ p +
        (2 * (L : ℝ) * B + ‖fv‖) ^ p) ^ p⁻¹ := by
    apply E.graphSeminorm_le_of_le _ _ (hbound n)
    calc
      ‖(g n : CarpetLp p)‖ ≤ ‖((g n : CarpetLp p) - fv)‖ + ‖fv‖ := by
        exact (congrArg norm (sub_add_cancel (g n : CarpetLp p) fv)).symm.le.trans
          (norm_add_le _ _)
      _ ≤ _ := add_le_add ((hdist n).trans
        (mul_le_mul_of_nonneg_left (hbB n) (by positivity))) le_rfl
  exact E.exists_domain_of_tendsto_of_seminorm_le E.rootSeminorm E.rootSeminorm_le_graphSeminorm
    g fv hgraph (fun r hr ↦ Eventually.of_forall fun n ↦ (hbound n).trans hr.le) hlim

private theorem exists_comp_of_lipschitzWith {L : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith L φ) (f : E.domain) :
    ∃ g : E.domain, (g : CarpetLp p) =ᵐ[carpetMeasure] φ ∘ (f : CarpetLp p) ∧
      E.rootSeminorm g ≤ (L : ℝ) * E.rootSeminorm f := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose u hu happrox using fun n ↦ E.regular_graph f (ε n) (hε n)
  let fₙ (n : ℕ) : E.domain := ⟨continuousLp p (u n), hu n⟩
  have hnorm (n : ℕ) : ‖(fₙ n : CarpetLp p) - (f : CarpetLp p)‖ ≤ ε n :=
    (E.norm_coe_le_graphSeminorm (fₙ n - f)).trans (happrox n).le
  have hroot (n : ℕ) : E.rootSeminorm (fₙ n) ≤ E.rootSeminorm f + ε n := by
    calc
      _ = E.rootSeminorm ((fₙ n - f) + f) := by rw [sub_add_cancel]
      _ ≤ E.rootSeminorm (fₙ n - f) + E.rootSeminorm f := map_add_le_add _ _ _
      _ ≤ _ := by
        rw [add_comm (E.rootSeminorm f)]
        exact add_le_add_left ((E.rootSeminorm_le_graphSeminorm _).trans (happrox n).le) _
  have hf : Tendsto (fun n ↦ (fₙ n : CarpetLp p)) atTop (𝓝 (f : CarpetLp p)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεlim
        (fun _ ↦ norm_nonneg _) hnorm)
  let ψ (t : ℝ) := φ t - φ 0
  have hψ : LipschitzWith L ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (φ x - φ 0) (φ y - φ 0) ≤ _
    rw [Real.dist_eq, sub_sub_sub_cancel_right, ← Real.dist_eq]
    exact hφ.dist_le_mul x y
  have hψ₀ : ψ 0 = 0 := sub_self _
  let c := constantLp p (φ 0)
  let T (v : CarpetLp p) : CarpetLp p := hψ.compLp hψ₀ v + c
  have hT : Continuous T := (hψ.continuous_compLp hψ₀).add continuous_const
  have hTae (v : CarpetLp p) : T v =ᵐ[carpetMeasure] φ ∘ v := by
    filter_upwards [Lp.coeFn_add (hψ.compLp hψ₀ v) c, hψ.coeFn_compLp hψ₀ v,
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (φ 0)] with x h₁ h₂ h₃
    change T v x = (hψ.compLp hψ₀ v) x + c x at h₁
    change (hψ.compLp hψ₀ v) x = φ (v x) - φ 0 at h₂
    change c x = φ 0 at h₃
    change T v x = φ (v x)
    rw [h₁, h₂, h₃, sub_add_cancel]
  choose g hg henergy using fun n ↦ E.exists_comp_continuousLp (hu n) hφ
  have hgT (n : ℕ) : (g n : CarpetLp p) = T (fₙ n : CarpetLp p) := by
    apply Lp.ext
    rw [hg n]
    exact (continuousLp_ae_eq p _).trans
      (((hTae (fₙ n : CarpetLp p)).trans
        ((continuousLp_ae_eq p (u n)).mono fun _ hx ↦ congrArg φ hx))).symm
  have hlim : Tendsto (fun n ↦ (g n : CarpetLp p)) atTop (𝓝 (T f)) := by
    have h := (hT.tendsto (f : CarpetLp p)).comp hf
    simpa only [Function.comp_def, hgT] using h
  have hb (n : ℕ) : E.rootSeminorm (g n) ≤ (L : ℝ) * (E.rootSeminorm f + ε n) :=
    (henergy n).trans (mul_le_mul_of_nonneg_left (hroot n) L.coe_nonneg)
  have hgB (n : ℕ) : E.graphSeminorm (g n) ≤
      (((L : ℝ) * (E.rootSeminorm f + 1)) ^ p +
        ((L : ℝ) * (‖(f : CarpetLp p)‖ + 1) + ‖c‖) ^ p) ^ p⁻¹ := by
    apply E.graphSeminorm_le_of_le
    · rw [hgT]
      have hfB : ‖(fₙ n : CarpetLp p)‖ ≤ ‖(f : CarpetLp p)‖ + 1 := by
        calc
          _ = ‖((fₙ n : CarpetLp p) - (f : CarpetLp p)) + (f : CarpetLp p)‖ := by
            rw [sub_add_cancel]
          _ ≤ ‖((fₙ n : CarpetLp p) - (f : CarpetLp p))‖ + ‖(f : CarpetLp p)‖ :=
            norm_add_le _ _
          _ ≤ _ := by
            rw [add_comm ‖(f : CarpetLp p)‖]
            exact add_le_add_left ((hnorm n).trans (hεle n)) _
      calc
        ‖T (fₙ n : CarpetLp p)‖ ≤ ‖hψ.compLp hψ₀ (fₙ n : CarpetLp p)‖ + ‖c‖ := norm_add_le _ _
        _ ≤ _ := add_le_add_left ((hψ.norm_compLp_le hψ₀ _).trans
          (mul_le_mul_of_nonneg_left hfB L.coe_nonneg)) _
    · exact (hb n).trans (mul_le_mul_of_nonneg_left (add_le_add_right (hεle n) _) L.coe_nonneg)
  have hb' : Tendsto (fun n ↦ (L : ℝ) * (E.rootSeminorm f + ε n)) atTop
      (𝓝 ((L : ℝ) * E.rootSeminorm f)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hεlim).const_mul (L : ℝ)
  obtain ⟨v, hv, hrootv⟩ := E.exists_domain_of_tendsto_of_seminorm_le E.rootSeminorm
    E.rootSeminorm_le_graphSeminorm g (T f) hgB
    (fun r hr ↦ (hb'.eventually_lt_const hr).mono fun n hn ↦ (hb n).trans hn.le) hlim
  exact ⟨v, hv ▸ hTae f, hrootv⟩

/-- Composition with a Lipschitz scalar map has energy measure bounded by the
`p`-th power of the Lipschitz constant times the original measure (Lemma 3.3(b)). -/
theorem exists_energyMeasure_comp_le {L : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith L φ) (f : E.domain) :
    ∃ g : E.domain, (g : CarpetLp p) =ᵐ[carpetMeasure] φ ∘ (f : CarpetLp p) ∧
      E.energyMeasure g ≤ ((L ^ p : ℝ≥0) : ℝ≥0∞) • E.energyMeasure f := by
  classical
  choose T hT hroot using E.exists_comp_of_lipschitzWith hφ
  refine ⟨T f, hT f, E.energyMeasure_le_of_compScalar_energy_le T hT (L ^ p) ?_ f⟩
  intro v
  have hp := zero_lt_one.trans E.one_lt_p
  have heq (w : E.domain) : (E.rootSeminorm w) ^ p = (E.energy w : ℝ) :=
    (congrArg (fun t : ℝ ↦ t ^ p) (E.rootSeminorm_apply w)).trans
      (Real.rpow_inv_rpow (E.energy w).property hp.ne')
  have h : (E.energy (T v) : ℝ) ≤ (L : ℝ) ^ p * (E.energy v : ℝ) := by
    calc
      _ = (E.rootSeminorm (T v)) ^ p := (heq _).symm
      _ ≤ ((L : ℝ) * E.rootSeminorm v) ^ p :=
        Real.rpow_le_rpow (apply_nonneg E.rootSeminorm _) (hroot v) hp.le
      _ = (L : ℝ) ^ p * (E.rootSeminorm v) ^ p := Real.mul_rpow L.coe_nonneg (apply_nonneg _ _)
      _ = _ := congrArg ((L : ℝ) ^ p * ·) (heq v)
  exact_mod_cast h

end CarpetEnergy.SelfSimilarPEnergy
