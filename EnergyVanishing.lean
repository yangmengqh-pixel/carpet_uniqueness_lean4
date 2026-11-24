import EnergyApproximation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Vanishing energy for functions with a common zero set

The graph-norm compactness argument for Lemma 3.8 uses only two integrals:
the integral on the prescribed zero set and the integral on the whole carpet.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem integrable_carpetLp [hp : Fact (1 ≤ ENNReal.ofReal p)] (f : CarpetLp p) :
    Integrable f carpetMeasure :=
  (Lp.memLp f).integrable hp.out

/-- An integral over a measurable part of the carpet is controlled by the Lp norm. -/
theorem norm_setIntegral_le [hp : Fact (1 ≤ ENNReal.ofReal p)]
    (A : Set CarpetPoints) (f : CarpetLp p) :
    ‖∫ x in A, f x ∂carpetMeasure‖ ≤ ‖f‖ := by
  have hf := Lp.aestronglyMeasurable f
  have h := norm_integral_le_lintegral_norm (μ := carpetMeasure.restrict A) f
  refine h.trans ?_
  simp_rw [ofReal_norm, ← eLpNorm_one_eq_lintegral_eNorm hf.restrict]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    ((eLpNorm_mono_measure f Measure.restrict_le_self).trans
      (eLpNorm_le_eLpNorm_of_exponent_le hp.out))

/-- Integration on a measurable part of the carpet as a continuous linear functional. -/
noncomputable def lpSetIntegral [Fact (1 ≤ ENNReal.ofReal p)] (A : Set CarpetPoints) :
    CarpetLp p →L[ℝ] ℝ :=
  let T : CarpetLp p →ₗ[ℝ] ℝ :=
    { toFun := fun f ↦ ∫ x in A, f x ∂carpetMeasure
      map_add' := fun f g ↦ by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
        exact integral_add (integrable_carpetLp f).restrict (integrable_carpetLp g).restrict
      map_smul' := fun c f ↦ by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
        exact integral_smul c (f : CarpetPoints → ℝ) }
  T.mkContinuous 1 fun f ↦ by
    change ‖∫ x in A, f x ∂carpetMeasure‖ ≤ 1 * ‖f‖
    rw [one_mul]
    exact norm_setIntegral_le A f

include E in
/-- For a nonnegative function bounded by M, its p-th moment is controlled by its integral. -/
theorem norm_rpow_le_integral (f : CarpetLp p) {M : ℝ}
    (hf : ∀ᵐ x ∂carpetMeasure, 0 ≤ f x ∧ f x ≤ M) :
    ‖f‖ ^ p ≤ M ^ (p - 1) * ∫ x, f x ∂carpetMeasure := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hN : ‖f‖ = (∫ x, ‖f x‖ ^ p ∂carpetMeasure) ^ p⁻¹ := by
    rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal]
    · rw [ENNReal.toReal_ofReal hp.le]
    · exact Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _
  rw [hN, Real.rpow_inv_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hp.ne']
  rw [← integral_const_mul]
  apply integral_mono_ae
  · simpa only [ENNReal.toReal_ofReal hp.le] using (Lp.memLp f).integrable_norm_rpow'
  · exact (integrable_carpetLp f).const_mul _
  filter_upwards [hf] with x hx
  have hp1 := sub_nonneg.mpr E.one_lt_p.le
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  calc
    f x ^ p = f x ^ ((p - 1) + 1) := congrArg (fun t : ℝ ↦ f x ^ t) (by ring)
    _ = f x ^ (p - 1) * f x := by
      rw [Real.rpow_add' hx.1 (by linarith), Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1 hx.2 hp1) hx.1

private theorem not_exists_small_rootSeminorm (A : Set CarpetPoints) (hA : carpetMeasure A ≠ 0)
    (R δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n : ℕ, ∃ f : E.domain, E.graphSeminorm f ≤ R ∧
      E.rootSeminorm f ≤ 1 / ((n : ℝ) + 1) ∧
      (∫ x in A, (f : CarpetLp p) x ∂carpetMeasure) = 0 ∧
      δ ≤ ∫ x, (f : CarpetLp p) x ∂carpetMeasure := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  intro h
  let T := (lpSetIntegral (p := p) A).comp E.graphInclusion
  let U := (lpSetIntegral (p := p) univ).comp E.graphInclusion
  let toDomain : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := E.rootSeminorm.comp toDomain
  have hS : Continuous S :=
    Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm
      (fun z ↦ E.rootSeminorm_le_graphSeminorm (E.graphToDomain z))
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let C (n : ℕ) : Set E.GraphDomain :=
    Metric.closedBall 0 R ∩ (S.closedBall 0 (r n) ∩ (T ⁻¹' ({0} : Set ℝ) ∩ U ⁻¹' Ici δ))
  have hmono : Antitone C := by
    intro m n hmn x hx
    have hr : r n ≤ r m :=
      one_div_le_one_div_of_le (by positivity)
        (add_le_add (Nat.cast_le.mpr hmn) le_rfl)
    have hs : S x ≤ r n := by simpa only [S.closedBall_zero_eq, mem_ofPred_eq] using hx.2.1
    refine ⟨hx.1, ?_, hx.2.2⟩
    rw [S.closedBall_zero_eq]
    exact hs.trans hr
  have hclosed (n : ℕ) : IsClosed (C n) := by
    have hball : IsClosed (S.closedBall 0 (r n)) := by
      rw [S.closedBall_zero_eq]
      exact isClosed_le hS continuous_const
    exact Metric.isClosed_closedBall.inter (hball.inter
      ((isClosed_singleton.preimage T.continuous).inter (isClosed_Ici.preimage U.continuous)))
  have hconv (n : ℕ) : Convex ℝ (C n) :=
    (convex_closedBall _ _).inter ((S.convex_closedBall 0 (r n)).inter
      ((convex_singleton (0 : ℝ)).linear_preimage T.toLinearMap |>.inter
        ((convex_Ici δ).linear_preimage U.toLinearMap)))
  have hne (n : ℕ) : (C n).Nonempty := by
    obtain ⟨f, hf, hs, ht, hu⟩ := h n
    refine ⟨E.toGraph f, mem_closedBall_zero_iff.mpr hf, ?_, ht, ?_⟩
    · rw [S.closedBall_zero_eq]
      exact hs
    · change δ ≤ ∫ x in univ, (f : CarpetLp p) x ∂carpetMeasure
      simpa only [Measure.restrict_univ] using hu
  obtain ⟨z, hz⟩ := exists_mem_antitone_closed_convex C hmono hclosed hconv hne
    (fun x h ↦ mem_closedBall_zero_iff.mp h.1)
  have hzroot (n : ℕ) : S z ≤ r n := by
    simpa only [S.closedBall_zero_eq, mem_ofPred_eq] using (hz n).2.1
  have hzero := le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall hzroot)) (apply_nonneg S z)
  let f := E.graphToDomain z
  have he : E.energy f = 0 := by
    change E.rootSeminorm f = 0 at hzero
    have hp : 0 < p := zero_lt_one.trans E.one_lt_p
    have hpow := (E.rootSeminorm_apply f).symm.trans hzero
    have henergy := congrArg (fun x : ℝ ↦ x ^ p) hpow
    exact NNReal.eq ((Real.rpow_inv_rpow (E.energy f).property hp.ne').symm.trans
      (henergy.trans (Real.zero_rpow hp.ne')))
  obtain ⟨b, hb⟩ := (E.zero_iff_constant f).mp he
  have hconst : (f : CarpetLp p) =ᵐ[carpetMeasure] fun _ ↦ b := by
    rw [hb]
    exact Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure b
  have ht : (∫ x in A, (f : CarpetLp p) x ∂carpetMeasure) = 0 := (hz 0).2.2.1
  rw [integral_congr_ae (ae_restrict_of_ae hconst), integral_const, Measure.real,
    Measure.restrict_apply_univ,
    smul_eq_mul] at ht
  have hb0 : b = 0 := (mul_eq_zero.mp ht).resolve_left
    (ENNReal.toReal_ne_zero.mpr ⟨hA, measure_ne_top _ _⟩)
  have hu : δ ≤ ∫ x in univ, (f : CarpetLp p) x ∂carpetMeasure := (hz 0).2.2.2
  rw [Measure.restrict_univ, integral_congr_ae hconst, hb0, integral_zero] at hu
  exact hδ.not_ge hu

/-- Lemma 3.8. A uniformly bounded nonnegative sequence that vanishes on a fixed
set of positive measure converges to zero in Lp if its energies tend to zero. -/
theorem tendsto_norm_zero_of_energy_tendsto_zero_of_ae_zero
    (A : Set CarpetPoints) (hA : carpetMeasure A ≠ 0) {M : ℝ} (hM : 0 < M)
    (f : ℕ → E.domain)
    (hbound : ∀ n, ∀ᵐ x ∂carpetMeasure, 0 ≤ (f n : CarpetLp p) x ∧ (f n : CarpetLp p) x ≤ M)
    (hzero : ∀ n, (f n : CarpetLp p) =ᵐ[carpetMeasure.restrict A] fun _ ↦ 0)
    (henergy : Tendsto (fun n ↦ (E.energy (f n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖(f n : CarpetLp p)‖) atTop (𝓝 0) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hpow : Tendsto (fun n ↦ E.rootSeminorm (f n)) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) ^ p⁻¹ = 0 := Real.zero_rpow (inv_ne_zero hp.ne')
    have hlim := henergy.rpow_const (p := p⁻¹) (Or.inr (inv_nonneg.mpr hp.le))
    simpa only [E.rootSeminorm_apply, h0] using hlim
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _), fun ε hε ↦ ?_⟩
  by_contra h
  have hlarge : ∃ᶠ n in atTop, ε ≤ ‖(f n : CarpetLp p)‖ := by
    simpa only [Filter.Frequently, not_le] using h
  let δ := ε ^ p / M ^ (p - 1)
  have hδ : 0 < δ := div_pos (Real.rpow_pos_of_pos hε _) (Real.rpow_pos_of_pos hM _)
  apply E.not_exists_small_rootSeminorm A hA ((1 + M ^ p) ^ p⁻¹) δ hδ
  intro n
  have hr : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  obtain ⟨j, hj, hj'⟩ := ((hpow.eventually_lt_const hr).and_frequently hlarge).exists
  refine ⟨f j, ?_, hj.le, ?_, ?_⟩
  · have hn := norm_carpetLp_le_of_ae_bound (f j : CarpetLp p) hM.le
      ((hbound j).mono fun x hx ↦ by rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2)
    have hs : E.rootSeminorm (f j) ≤ 1 := hj.le.trans
      ((div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n)))
    exact E.graphSeminorm_le_of_le (f j) hn hs |>.trans_eq (by rw [Real.one_rpow])
  · rw [integral_congr_ae (hzero j), integral_zero]
  · apply (div_le_iff₀ (Real.rpow_pos_of_pos hM (p - 1))).mpr
    rw [mul_comm]
    exact (Real.rpow_le_rpow hε.le hj' hp.le).trans (E.norm_rpow_le_integral (f j) (hbound j))

end CarpetEnergy.SelfSimilarPEnergy
