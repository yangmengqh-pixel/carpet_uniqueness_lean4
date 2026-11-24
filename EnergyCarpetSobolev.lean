import CarpetWordSteps
import EnergyCellMeanIncrements
import EnergyFoldingAmplification
import EnergyApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Subcritical Sobolev estimates on the carpet

The (L^q) norms of the increments of the cell averages form a
geometric series. The strict range of exponents is sufficient for the
planar blowup argument of Theorem 5.2.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private noncomputable def meansStep (n : ℕ) (f : E.domain) : CarpetPoints → ℝ :=
  wordStep (fun w : Fin n → Fin 8 ↦ E.wordMean (List.ofFn w) f)

private theorem meansStep_tendsto (u : E.continuousCore) :
    ∀ᵐ x ∂carpetMeasure,
      Tendsto (fun n ↦ E.meansStep n (E.continuousCoreToDomain u) x) atTop (𝓝 (u.val x)) := by
  filter_upwards [ae_all_iff.mpr ae_notMem_carpetCellBoundary] with x hx
  refine Metric.tendsto_atTop.mpr (fun ε hε ↦ ?_)
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous u.val.continuous) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_wordMap_radius.eventually_lt_const hδ)
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨w, hw⟩ := exists_wordMap_range n x
  rw [Real.dist_eq, meansStep, wordStep_eq_of_mem _ hw (hx n)]
  have hu : continuousLp p u.val ∈ E.domain := u.property
  change |E.wordMean (List.ofFn w) ⟨continuousLp p u.val, hu⟩ - u.val x| < ε
  rw [E.wordMean_continuousLp _ _ hu]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply SelfSimilarComponent.abs_wordMean_sub_le
  intro y
  exact (Real.dist_eq _ _ ▸ hosc ((wordMap_dist_le n w (mem_range_self y) hw).trans_lt (hN n hn))).le

private theorem lpNorm_meansStep_zero (f : E.domain) {q : ℝ} (hq : 0 < q)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    lpNorm (E.meansStep 0 f) (ENNReal.ofReal q) carpetMeasure ≤ ‖(f : CarpetLp p)‖ := by
  let w : Fin 0 → Fin 8 := Fin.elim0
  have hnil : List.ofFn w = [] := List.length_eq_zero_iff.mp List.length_ofFn
  have hs : E.meansStep 0 f = fun _ ↦ E.wordMean [] f := by
    ext x
    have h : x ∈ range (wordMap (List.ofFn w)) := by rw [hnil]; exact mem_range_self x
    unfold meansStep wordStep
    rw [Finset.sum_eq_single w, indicator_of_mem h]
    · exact congrArg (fun v ↦ E.wordMean v f) hnil
    · exact fun v _ hne ↦ (hne (Subsingleton.elim v w)).elim
    · intro hne
      exact (hne (Finset.mem_univ w)).elim
  rw [hs, lpNorm_const (ENNReal.ofReal_ne_zero_iff.mpr hq) (IsProbabilityMeasure.ne_zero _)]
  have hm : carpetMeasure.real univ = 1 := by simp [Measure.real]
  rw [hm, Real.one_rpow, mul_one]
  change ‖∫ x, (E.pullbackWord [] f : CarpetLp p) x ∂carpetMeasure‖ ≤ _
  have hpb : E.pullbackWord [] f = f := by
    apply Subtype.ext
    apply Lp.ext
    exact E.pullbackWord_isLpPullback [] f
  rw [hpb]
  simpa only [Measure.restrict_univ] using norm_setIntegral_le univ (f : CarpetLp p)

set_option maxHeartbeats 1500000 in
private theorem lpNorm_meansStep_succ_sub_le {C q : ℝ} (hC : 0 ≤ C) (hpq : p ≤ q)
    (hInc : ∀ (f : E.domain) (n : ℕ) (w : Fin (n + 1) → Fin 8),
      |E.wordMean (List.ofFn w) f - E.wordMean (List.ofFn (w ∘ Fin.castSucc)) f| ≤
        (C * (E.energy (E.pullbackWord (List.ofFn (w ∘ Fin.castSucc)) f) : ℝ)) ^ p⁻¹)
    (f : E.domain) (n : ℕ) :
    lpNorm (E.meansStep (n + 1) f - E.meansStep n f) (ENNReal.ofReal q) carpetMeasure ≤
      (C ^ p⁻¹ * E.rootSeminorm f) *
        (((8 : ℝ)⁻¹) ^ q⁻¹ * E.scalingFactor⁻¹ ^ p⁻¹) ^ n := by
  have hp := zero_lt_one.trans E.one_lt_p
  have hρ := E.isScalingFactor_scalingFactor.1
  let e (w : Fin n → Fin 8) := (E.energy (E.pullbackWord (List.ofFn w) f) : ℝ)
  let a (w : Fin n → Fin 8) := (C * e w) ^ p⁻¹
  have ha (w) : 0 ≤ a w := Real.rpow_nonneg (mul_nonneg hC (NNReal.coe_nonneg _)) _
  have hdom : ∀ᵐ x ∂carpetMeasure,
      ‖(E.meansStep (n + 1) f - E.meansStep n f) x‖ ≤ wordStep a x := by
    filter_upwards [ae_notMem_carpetCellBoundary n, ae_notMem_carpetCellBoundary (n + 1)]
      with x hx hx'
    obtain ⟨w, hw⟩ := exists_wordMap_range (n + 1) x
    have hv := range_wordMap_child_subset w hw
    rw [Pi.sub_apply, meansStep, meansStep, wordStep_eq_of_mem _ hw hx',
      wordStep_eq_of_mem _ hv hx, Real.norm_eq_abs, wordStep_eq_of_mem _ hv hx]
    exact hInc f n w
  have hm (k : ℕ) : MemLp (E.meansStep k f) (ENNReal.ofReal q) carpetMeasure :=
    memLp_wordStep _ _
  have hnorm := eLpNorm_mono_ae_real (p := ENNReal.ofReal q)
    ((hm (n + 1)).sub (hm n)).aestronglyMeasurable hdom
  have hb : lpNorm (E.meansStep (n + 1) f - E.meansStep n f) (ENNReal.ofReal q) carpetMeasure ≤
      lpNorm (wordStep a) (ENNReal.ofReal q) carpetMeasure :=
    ENNReal.toReal_mono (memLp_wordStep a (ENNReal.ofReal q)).eLpNorm_ne_top hnorm
  refine hb.trans ((lpNorm_wordStep_le a hp hpq).trans_eq ?_)
  have hs : (∑ w, |a w| ^ p) = C * (E.scalingFactor ^ n)⁻¹ * (E.energy f : ℝ) := by
    have hcell (w) : |a w| ^ p = C * e w := by
      rw [abs_of_nonneg (ha w)]
      exact Real.rpow_inv_rpow (mul_nonneg hC (NNReal.coe_nonneg _)) hp.ne'
    simp only [hcell, ← Finset.mul_sum]
    rw [E.energy_eq_sum_words n f]
    dsimp only [e]
    rw [mul_assoc C, ← mul_assoc (E.scalingFactor ^ n)⁻¹, inv_mul_cancel₀ (pow_pos hρ _).ne', one_mul]
  have commPow (x : ℝ) (hx : 0 ≤ x) (r : ℝ) : (x ^ n) ^ r = (x ^ r) ^ n := by
    rw [← Real.rpow_natCast_mul hx, mul_comm (n : ℝ), Real.rpow_mul_natCast hx]
  rw [hs, Real.mul_rpow (by positivity) (NNReal.coe_nonneg _),
    Real.mul_rpow hC (by positivity), ← inv_pow,
    commPow _ (inv_nonneg.mpr hρ.le), commPow _ (by norm_num : 0 ≤ ((8 : ℝ)⁻¹)),
    mul_pow, E.rootSeminorm_apply]
  ring

set_option maxHeartbeats 1800000 in
/-- In the strict Sobolev range, the continuous core embeds into (L^q). -/
theorem exists_lpNorm_le_graph_of_geometric_ratio {q : ℝ} (hpq : p ≤ q)
    (hr : ((8 : ℝ)⁻¹) ^ q⁻¹ * E.scalingFactor⁻¹ ^ p⁻¹ < 1) :
    ∃ A > (0 : ℝ), ∀ u : E.continuousCore,
      lpNorm u.val (ENNReal.ofReal q) carpetMeasure ≤ A * E.graphSeminorm (E.continuousCoreToDomain u) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hq := (zero_lt_one.trans E.one_lt_p).trans_le hpq
  have hq₁ : 1 ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr (E.one_lt_p.le.trans hpq)
  let r := ((8 : ℝ)⁻¹) ^ q⁻¹ * E.scalingFactor⁻¹ ^ p⁻¹
  have hr₀ : 0 ≤ r := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (inv_nonneg.mpr E.isScalingFactor_scalingFactor.1.le) _)
  obtain ⟨C, hC, hInc⟩ := E.exists_wordMean_increment_bound
  let A := 1 + C ^ p⁻¹ * (1 - r)⁻¹
  have hA : 0 < A := add_pos_of_pos_of_nonneg one_pos
    (mul_nonneg (Real.rpow_nonneg hC.le _) (inv_nonneg.mpr (sub_nonneg.mpr hr.le)))
  refine ⟨A, hA, fun u ↦ ?_⟩
  let f := E.continuousCoreToDomain u
  let b := C ^ p⁻¹ * E.rootSeminorm f
  have hb : 0 ≤ b := mul_nonneg (Real.rpow_nonneg hC.le _) (apply_nonneg E.rootSeminorm f)
  let M := ‖(f : CarpetLp p)‖ + b * (1 - r)⁻¹
  have hMem (n : ℕ) : MemLp (E.meansStep n f) (ENNReal.ofReal q) carpetMeasure := memLp_wordStep _ _
  have hsum (n : ℕ) :
      lpNorm (E.meansStep n f) (ENNReal.ofReal q) carpetMeasure ≤
        ‖(f : CarpetLp p)‖ + b * ∑ k ∈ Finset.range n, r ^ k := by
    induction n with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] using
        E.lpNorm_meansStep_zero f hq
    | succ n ih =>
      have hh := lpNorm_le_lpNorm_add_lpNorm_sub' (f := E.meansStep (n + 1) f) (hMem n) hq₁
      have hi := E.lpNorm_meansStep_succ_sub_le hC.le hpq hInc f n
      rw [Finset.sum_range_succ, mul_add, ← add_assoc]
      exact hh.trans (add_le_add ih hi)
  have hbound (n : ℕ) :
      lpNorm (E.meansStep n f) (ENNReal.ofReal q) carpetMeasure ≤ M := by
    have hs := (summable_geometric_of_lt_one hr₀ hr).sum_le_tsum (Finset.range n)
      (fun k _ ↦ pow_nonneg hr₀ k)
    rw [tsum_geometric_of_lt_one hr₀ hr] at hs
    exact (hsum n).trans (add_le_add_right (mul_le_mul_of_nonneg_left hs hb) _)
  have hLim := Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall fun n ↦ by
      rw [← ofReal_lpNorm (hMem n)]
      exact ENNReal.ofReal_le_ofReal (hbound n))
    (fun n ↦ (hMem n).aestronglyMeasurable) u.val.continuous.aestronglyMeasurable
    (E.meansStep_tendsto u)
  have hM : 0 ≤ M := add_nonneg (norm_nonneg _)
    (mul_nonneg hb (inv_nonneg.mpr (sub_nonneg.mpr hr.le)))
  have hlp : lpNorm u.val (ENNReal.ofReal q) carpetMeasure ≤ M := by
    change (eLpNorm u.val (ENNReal.ofReal q) carpetMeasure).toReal ≤ M
    simpa only [ENNReal.toReal_ofReal hM] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hLim
  refine hlp.trans ?_
  have hroot := E.rootSeminorm_le_graphSeminorm f
  have hnorm := E.norm_coe_le_graphSeminorm f
  dsimp only [A, M, b]
  rw [add_mul, one_mul, mul_assoc (C ^ p⁻¹), mul_comm (E.rootSeminorm f),
    mul_assoc (C ^ p⁻¹)]
  exact add_le_add hnorm (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hroot (inv_nonneg.mpr (sub_nonneg.mpr hr.le)))
    (Real.rpow_nonneg hC.le _))

end CarpetEnergy.SelfSimilarPEnergy
