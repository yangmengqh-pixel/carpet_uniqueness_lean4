import PlanarSobolevRoot
import SmoothSobolevWeightTail

/-!
# Small weak derivatives of upper-tail truncations
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

set_option maxHeartbeats 3800000 in
/-- Upper-tail truncations with arbitrarily small derivative moments
and their bounded reciprocal cutoffs. -/
theorem exists_planar_sobolev_tail {p : ℝ} (hp : 1 < p)
    {a : Plane2 → ℝ} (ha : Measurable a) (ha₀ : ∀ x, 0 ≤ a x) (haI : Integrable a volume)
    (g : Fin 2 → Plane2 → ℝ)
    (hgI : ∀ i, Integrable (g i) volume) (hgLp : ∀ i, MemLp (g i) (ENNReal.ofReal p) volume)
    (hg : ∀ i, HasWeakDirectionalDerivative volume a (g i) (planarDirection i))
    (κ : Measure Plane2) [IsFiniteMeasure κ] {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∃ b T : Plane2 → ℝ,
      Measurable b ∧ (∀ x, b x ∈ Icc (0 : ℝ) 1) ∧ Integrable b volume ∧
      (∫ x, |b x| ^ p ∂κ) < δ ∧
      Measurable T ∧ Integrable T volume ∧
      (∀ x, (a x + 1) * (1 - b x) ≤ C) ∧
      (∀ x y, (a x + 1) * |b y - b x| ≤ |T y - T x|) ∧
      ∃ V : Fin 2 → Plane2 → ℝ, (∀ i, Integrable (V i) volume ∧
        Integrable (fun x ↦ |V i x| ^ p) volume ∧
        HasWeakDirectionalDerivative volume T (V i) (planarDirection i)) ∧
        ((∫ x, |V 0 x| ^ p ∂volume) + ∫ x, |V 1 x| ^ p ∂volume) < δ := by
  obtain ⟨D, hD, hchoose⟩ := exists_smooth_tail_weight_cutoffs
  let c (n : ℕ) : ℝ := (n : ℝ) + 1
  have hc (n : ℕ) : 0 ≤ c n := by dsimp only [c]; positivity
  have hclim : Tendsto c atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  choose T F hT hT₀ hTzero hTb hF hF01 hFzero hFrec hinc using fun n ↦ hchoose (c n) (hc n)
  let V (n : ℕ) (i : Fin 2) (x : Plane2) := deriv (T n) (a x) * g i x
  let b (n : ℕ) := F n ∘ a
  let u (n : ℕ) := T n ∘ a
  have hbM (n : ℕ) : Measurable (b n) := (hF n).continuous.measurable.comp ha
  have huM (n : ℕ) : Measurable (u n) := (hT n).continuous.measurable.comp ha
  have hgp (i : Fin 2) : Integrable (fun x ↦ |g i x| ^ p) volume := by
    have hp₀ : 0 < p := zero_lt_one.trans hp
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp₀.le] using
      (hgLp i).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top
  have hvC (n : ℕ) : Continuous (deriv (T n)) := (hT n).continuous_deriv (by norm_num)
  have hvM (n : ℕ) (i : Fin 2) : AEStronglyMeasurable (V n i) volume :=
    ((hvC n).comp_aestronglyMeasurable ha.aestronglyMeasurable).mul (hgI i).aestronglyMeasurable
  have hvI (n : ℕ) (i : Fin 2) : Integrable (V n i) volume :=
    (hgI i).bdd_mul ((hvC n).comp_aestronglyMeasurable ha.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hTb n _)
  have hvbound (n : ℕ) (i : Fin 2) (x : Plane2) : |V n i x| ^ p ≤ D ^ p * |g i x| ^ p := by
    dsimp only [V]
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) (hTb n _) (zero_le_one.trans hp.le))
      (Real.rpow_nonneg (abs_nonneg _) _)
  have hvMp (n : ℕ) (i : Fin 2) : AEStronglyMeasurable (fun x ↦ |V n i x| ^ p) volume :=
    (Real.continuous_rpow_const (zero_le_one.trans hp.le)).comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable (hvM n i))
  have hvIp (n : ℕ) (i : Fin 2) : Integrable (fun x ↦ |V n i x| ^ p) volume :=
    ((hgp i).const_mul (D ^ p)).mono' (hvMp n i) (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact hvbound n i x)
  have hlimitV (i : Fin 2) : Tendsto (fun n ↦ ∫ x, |V n i x| ^ p ∂volume) atTop (𝓝 0) := by
    rw [← integral_zero (μ := (volume : Measure Plane2)) (G := ℝ)]
    apply tendsto_integral_of_dominated_convergence (fun x ↦ D ^ p * |g i x| ^ p)
      (fun n ↦ hvMp n i) ((hgp i).const_mul _)
    · intro n
      exact Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]; exact hvbound n i x
    · apply Eventually.of_forall
      intro x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hclim.eventually_ge_atTop (a x)] with n hn
      dsimp only [V]
      rw [(hTzero n _ hn).2, zero_mul, abs_zero, Real.zero_rpow (zero_lt_one.trans hp).ne']
  have hbI (n : ℕ) : Integrable (b n) volume := by
    apply haI.mono' (hbM n).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖F n (a x)‖ ≤ a x
    rw [Real.norm_eq_abs, abs_of_nonneg (hF01 n _).1]
    rcases le_or_gt (a x) (c n) with hx | hx
    · exact (hFzero n _ hx).le.trans (ha₀ x)
    · exact (hF01 n _).2.trans (show 1 ≤ a x by dsimp only [c] at hx; linarith [Nat.cast_nonneg (α := ℝ) n])
  have huI (n : ℕ) : Integrable (u n) volume := by
    let D₀ : ℝ≥0 := ⟨D, hD.le⟩
    have hLip : LipschitzWith D₀ (T n) := lipschitzWith_of_nnNorm_deriv_le
      ((hT n).differentiable (by norm_num)) (fun x ↦ by change ‖deriv (T n) x‖ ≤ D; rw [Real.norm_eq_abs]; exact hTb n x)
    apply (haI.const_mul D).mono' (huM n).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    have hh := hLip.dist_le_mul (a x) 0
    change dist (T n (a x)) (T n 0) ≤ D * dist (a x) 0 at hh
    simpa only [Real.dist_eq, (hTzero n 0 (hc n)).1, sub_zero,
      abs_of_nonneg (ha₀ x), Real.norm_eq_abs, u, Function.comp_apply] using hh
  have hbκ : Tendsto (fun n ↦ ∫ x, |b n x| ^ p ∂κ) atTop (𝓝 0) := by
    rw [← integral_zero (μ := κ) (G := ℝ)]
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
    · exact fun n ↦ ((Real.continuous_rpow_const (zero_le_one.trans hp.le)).measurable.comp
        (continuous_abs.measurable.comp (hbM n))).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall fun x ↦ by
        change ‖|F n (a x)| ^ p‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_of_nonneg (hF01 n _).1]
        exact Real.rpow_le_one (hF01 n _).1 (hF01 n _).2 (zero_le_one.trans hp.le)
    · apply Eventually.of_forall
      intro x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hclim.eventually_ge_atTop (a x)] with n hn
      change (0 : ℝ) = |F n (a x)| ^ p
      rw [hFzero n _ hn, abs_zero, Real.zero_rpow (zero_lt_one.trans hp).ne']
  have hVlim := (hlimitV 0).add (hlimitV 1)
  rw [zero_add] at hVlim
  obtain ⟨n, hbn, hvn⟩ := ((hbκ.eventually_lt_const hδ).and (hVlim.eventually_lt_const hδ)).exists
  exact ⟨c n + 2, by linarith [hc n], b n, u n, hbM n, fun x ↦ hF01 n (a x), hbI n, hbn,
    huM n, huI n, fun x ↦ hFrec n _ (ha₀ x), fun x y ↦ hinc n _ (ha₀ x) _ (ha₀ y), V n,
    fun i ↦ ⟨hvI n i, hvIp n i, (hg i).comp_bounded_deriv haI (hgI i) (hT n)
      (hTzero n 0 (hc n)).1 hD.le (hTb n)⟩, hvn⟩

end CarpetEnergy
