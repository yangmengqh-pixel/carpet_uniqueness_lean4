import EnergySpectralGap
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Harmonic energy minimization

A constraint on the integral over a set of positive carpet measure pins
down additive constants. The spectral gap then bounds the minimizing
sublevels in the graph norm.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A set integral together with the energy root controls the ambient norm. -/
theorem exists_norm_le_of_setIntegral (A : Set CarpetPoints) (hA : carpetMeasure A ≠ 0) :
    ∃ C ≥ (0 : ℝ), ∀ f : E.domain,
      ‖(f : CarpetLp p)‖ ≤ |∫ x in A, (f : CarpetLp p) x ∂carpetMeasure| /
        (carpetMeasure A).toReal + C * E.rootSeminorm f := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨B, hB, hgap⟩ := E.exists_spectral_gap
  let m := (carpetMeasure A).toReal
  have hm : 0 < m := ENNReal.toReal_pos hA (measure_ne_top _ _)
  let K := B ^ p⁻¹
  have hK : 0 ≤ K := Real.rpow_nonneg hB.le _
  refine ⟨(1 + m⁻¹) * K, by positivity, fun f ↦ ?_⟩
  let v : CarpetLp p := f
  let c := ∫ x, v x ∂carpetMeasure
  let T : CarpetLp p →L[ℝ] ℝ := lpSetIntegral A
  have hT (z : CarpetLp p) : |T z| ≤ ‖z‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le A z
  have hc : T (constantLp p c) = m * c := by
    change (∫ x in A, (constantLp p c) x ∂carpetMeasure) = m * c
    unfold constantLp
    rw [integral_congr_ae ((Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c).filter_mono
      (ae_mono Measure.restrict_le_self))]
    change (∫ _ : CarpetPoints, c ∂carpetMeasure.restrict A) = m * c
    rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  have hcenter : ‖centerLp p v‖ ≤ K * E.rootSeminorm f := by
    rw [E.rootSeminorm_apply, ← Real.mul_rpow hB.le (NNReal.coe_nonneg (E.energy f))]
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) (hgap f)
      (inv_nonneg.mpr hp.le)
    rw [← centerLp_apply, Real.rpow_rpow_inv (norm_nonneg _) hp.ne'] at h
    exact h
  have hv : v = constantLp p c + centerLp p v := by rw [centerLp_apply]; abel
  have hnormConst : ‖constantLp p c‖ = |c| := by
    unfold constantLp
    rw [Lp.norm_const _ _ _ (ENNReal.ofReal_ne_zero_iff.mpr hp)]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, Real.one_rpow, mul_one,
      Real.norm_eq_abs]
  have hmean : m * |c| ≤ |T v| + ‖centerLp p v‖ := by
    have he : m * c = T v - T (centerLp p v) := by
      rw [← hc, ← map_sub, centerLp_apply]
      congr 1
      abel
    have hmabs : |m * c| = m * |c| := by rw [abs_mul, abs_of_pos hm]
    rw [← hmabs, he]
    exact (abs_sub _ _).trans (add_le_add_right (hT (centerLp p v)) |T v|)
  change ‖v‖ ≤ |T v| / m + _
  calc
    ‖v‖ ≤ |c| + ‖centerLp p v‖ := by
      nth_rw 1 [hv]
      exact (norm_add_le _ _).trans_eq (by rw [hnormConst])
    _ ≤ (|T v| + ‖centerLp p v‖) / m + ‖centerLp p v‖ :=
      add_le_add_left (show |c| ≤ (|T v| + ‖centerLp p v‖) / m from
        (le_div_iff₀ hm).mpr ((mul_comm |c| m).le.trans hmean)) _
    _ = |T v| / m + (1 + m⁻¹) * ‖centerLp p v‖ := by rw [add_div, div_eq_mul_inv]; ring
    _ ≤ _ := by
      rw [mul_assoc]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hcenter
        (show 0 ≤ 1 + m⁻¹ by positivity)) _

/-- On every nonempty graph-closed convex constraint with fixed background
integral on a positive-measure set, the energy attains its minimum. -/
theorem exists_energy_minimizer_of_setIntegral (A : Set CarpetPoints)
    (hA : carpetMeasure A ≠ 0) (C : Set E.GraphDomain) (hC : IsClosed C)
    (hconv : Convex ℝ C) (hne : C.Nonempty) (b : ℝ)
    (hb : ∀ z ∈ C, (∫ x in A, (E.graphToDomain z : CarpetLp p) x ∂carpetMeasure) = b) :
    ∃ z ∈ C, ∀ w ∈ C, E.energy (E.graphToDomain z) ≤ E.energy (E.graphToDomain w) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨K, hK, hbound⟩ := E.exists_norm_le_of_setIntegral A hA
  let toDomain : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := E.rootSeminorm.comp toDomain
  have hS : Continuous S :=
    Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm
      (fun z ↦ E.rootSeminorm_le_graphSeminorm (E.graphToDomain z))
  let d := sInf (S '' C)
  have hbelow : BddBelow (S '' C) :=
    ⟨0, by rintro _ ⟨x, _, rfl⟩; exact apply_nonneg S x⟩
  have hd (x : E.GraphDomain) (hx : x ∈ C) : d ≤ S x :=
    csInf_le hbelow (mem_image_of_mem _ hx)
  let r (n : ℕ) : ℝ := d + 1 / ((n : ℝ) + 1)
  have hnr (n : ℕ) : d < r n := lt_add_of_pos_right _ (by positivity)
  let Cn (n : ℕ) : Set E.GraphDomain := C ∩ S.closedBall 0 (r n)
  have hmono : Antitone Cn := by
    intro m n hmn x hx
    refine ⟨hx.1, ?_⟩
    rw [S.closedBall_zero_eq]
    have h' : S x ≤ r n := by simpa only [S.closedBall_zero_eq, mem_ofPred_eq] using hx.2
    have hnm : (m : ℝ) + 1 ≤ (n : ℝ) + 1 :=
      add_le_add_left (Nat.cast_le.mpr hmn : (m : ℝ) ≤ (n : ℝ)) 1
    have hf := one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1) hnm
    exact h'.trans (add_le_add_right hf d)
  have hclosed (n : ℕ) : IsClosed (Cn n) := by
    apply hC.inter
    rw [S.closedBall_zero_eq]
    exact isClosed_le hS continuous_const
  have hcv (n : ℕ) : Convex ℝ (Cn n) := hconv.inter (S.convex_closedBall 0 (r n))
  have hn (n : ℕ) : (Cn n).Nonempty := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hl⟩ := exists_lt_of_csInf_lt (hne.image S) (hnr n)
    refine ⟨x, hx, ?_⟩
    rw [S.closedBall_zero_eq]
    exact hl.le
  let L := |b| / (carpetMeasure A).toReal + K * r 0
  have hgraph : ∀ x ∈ Cn 0, ‖x‖ ≤ (r 0 ^ p + L ^ p) ^ p⁻¹ := by
    intro z hz
    have hr : S z ≤ r 0 := by simpa only [S.closedBall_zero_eq, mem_ofPred_eq] using hz.2
    have hl := hbound (E.graphToDomain z)
    rw [hb z hz.1] at hl
    change E.graphSeminorm (E.graphToDomain z) ≤ _
    exact E.graphSeminorm_le_of_le (E.graphToDomain z)
      (hl.trans (add_le_add_right (mul_le_mul_of_nonneg_left hr hK) _)) hr
  obtain ⟨z, hz⟩ := exists_mem_antitone_closed_convex Cn hmono hclosed hcv hn hgraph
  refine ⟨z, (hz 0).1, fun w hw ↦ ?_⟩
  have hr : Tendsto r atTop (𝓝 d) := by
    have hconst : Tendsto (fun _ : ℕ ↦ d) atTop (𝓝 d) := tendsto_const_nhds
    have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [add_zero] using hconst.add hlim
  have hzr (n : ℕ) : S z ≤ r n := by
    simpa only [S.closedBall_zero_eq, mem_ofPred_eq] using (hz n).2
  have hzmin := (le_of_tendsto_of_tendsto tendsto_const_nhds hr (Eventually.of_forall hzr)).trans (hd w hw)
  have hpow (v : E.GraphDomain) : S v ^ p = (E.energy (E.graphToDomain v) : ℝ) := by
    change E.rootSeminorm (E.graphToDomain v) ^ p = _
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'
  have he := Real.rpow_le_rpow (apply_nonneg S z) hzmin hp.le
  rw [hpow z, hpow w] at he
  exact NNReal.coe_le_coe.mp he

/-- Fixing a function almost everywhere on a positive-measure set yields
an energy minimizer with the same boundary data. -/
theorem exists_harmonic_with_fixed_values (A : Set CarpetPoints)
    (hA : carpetMeasure A ≠ 0) (f : E.domain) :
    ∃ h : E.domain, (h : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (f : CarpetLp p) ∧
      ∀ g : E.domain, (g : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (f : CarpetLp p) →
        E.energy h ≤ E.energy g := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  let L (S : Set CarpetPoints) : E.GraphDomain →L[ℝ] ℝ :=
    (lpSetIntegral (S ∩ A)).comp E.graphInclusion
  let C : Set E.GraphDomain :=
    ⋂ S : {S : Set CarpetPoints // MeasurableSet S}, L S ⁻¹' {L S (E.toGraph f)}
  have hC (z : E.GraphDomain) :
      z ∈ C ↔ (E.graphToDomain z : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (f : CarpetLp p) := by
    let u : CarpetLp p := E.graphToDomain z
    let v : CarpetLp p := f
    have h (S : Set CarpetPoints) (hS : MeasurableSet S) :
        L S z = L S (E.toGraph f) ↔
          (∫ x in S, u x ∂carpetMeasure.restrict A) =
            ∫ x in S, v x ∂carpetMeasure.restrict A := by
      change ((∫ x in S ∩ A, u x ∂carpetMeasure) = ∫ x in S ∩ A, v x ∂carpetMeasure) ↔ _
      rw [Measure.restrict_restrict hS]
    rw [show z ∈ C ↔ ∀ S : {S : Set CarpetPoints // MeasurableSet S}, L S z = L S (E.toGraph f)
      from mem_iInter]
    change _ ↔ u =ᵐ[carpetMeasure.restrict A] v
    constructor
    · intro he
      have hi (w : CarpetLp p) : Integrable w (carpetMeasure.restrict A) :=
        integrableOn_Lp_of_measure_ne_top w (ENNReal.one_le_ofReal.mpr E.one_lt_p.le)
          (measure_ne_top _ _)
      refine (hi u).ae_eq_of_forall_setIntegral_eq u v (hi v) fun S hS _ ↦ ?_
      exact (h S hS).mp (he ⟨S, hS⟩)
    · intro he S
      apply (h S S.property).mpr
      exact integral_congr_ae (he.filter_mono (ae_mono Measure.restrict_le_self))
  have hclosed : IsClosed C :=
    isClosed_iInter fun S ↦ isClosed_singleton.preimage (L S).continuous
  have hconv : Convex ℝ C :=
    convex_iInter fun S ↦ (convex_singleton _).linear_preimage (L S).toLinearMap
  have hne : C.Nonempty := ⟨E.toGraph f, (hC _).2 EventuallyEq.rfl⟩
  have hf (z : E.GraphDomain) (hz : z ∈ C) :
      (∫ x in A, (E.graphToDomain z : CarpetLp p) x ∂carpetMeasure) =
        ∫ x in A, (f : CarpetLp p) x ∂carpetMeasure := integral_congr_ae ((hC z).mp hz)
  obtain ⟨z, hz, hmin⟩ := E.exists_energy_minimizer_of_setIntegral A hA C hclosed hconv hne _ hf
  exact ⟨E.graphToDomain z, (hC z).mp hz, fun g hg ↦ hmin (E.toGraph g) ((hC _).mpr hg)⟩

end CarpetEnergy.SelfSimilarPEnergy
