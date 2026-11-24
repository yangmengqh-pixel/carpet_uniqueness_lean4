import EnergyCompactCutoff
import EnergyCoreProduct
import EnergyLipschitz
import CarpetWordIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Graph approximation with support constraints

A bounded domain function which vanishes off a closed set can be
approximated inside any larger open set. Clip the continuous
approximants before multiplying by a cutoff, then take a closed
convex tail in the graph norm.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Graph-domain images of continuous profiles vanishing off a set. -/
noncomputable def supportedCoreGraph (U : Set CarpetPoints) : Submodule ℝ E.GraphDomain where
  carrier := {z | ∃ v : E.continuousCore, E.toGraph (E.continuousCoreToDomain v) = z ∧
    ∀ x ∉ U, v.val x = 0}
  zero_mem' := ⟨0, map_zero E.continuousCoreToDomain, fun _ _ ↦ rfl⟩
  add_mem' := by
    rintro _ _ ⟨v, rfl, hv⟩ ⟨w, rfl, hw⟩
    refine ⟨v + w, map_add E.continuousCoreToDomain v w, fun x hx ↦ ?_⟩
    change v.val x + w.val x = 0
    rw [hv x hx, hw x hx, add_zero]
  smul_mem' := by
    rintro a _ ⟨v, rfl, hv⟩
    refine ⟨a • v, map_smul E.continuousCoreToDomain a v, fun x hx ↦ ?_⟩
    change a * v.val x = 0
    rw [hv x hx, mul_zero]

private def symmetricClip (M x : ℝ) : ℝ := min (max x (-M)) M

private theorem lipschitzWith_symmetricClip (M : ℝ) : LipschitzWith 1 (symmetricClip M) :=
  ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).max_const (-M)).min_const M

private theorem abs_symmetricClip_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |symmetricClip M x| ≤ M := by
  apply abs_le.mpr
  exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩

private theorem symmetricClip_eq_of_abs_le {M x : ℝ} (hx : |x| ≤ M) : symmetricClip M x = x := by
  obtain ⟨hl, hr⟩ := abs_le.mp hx
  simp only [symmetricClip, max_eq_left hl, min_eq_left hr]

private theorem symmetricClip_zero {M : ℝ} (hM : 0 ≤ M) : symmetricClip M 0 = 0 :=
  symmetricClip_eq_of_abs_le (by simpa only [abs_zero] using hM)

private theorem abs_symmetricClip_le_abs {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    |symmetricClip M x| ≤ |x| := by
  have h := (lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_symmetricClip M)) x 0
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, symmetricClip_zero hM, sub_zero] using h

private theorem rootSeminorm_le_of_energy_le {f g : E.domain} (h : E.energy f ≤ E.energy g) :
    E.rootSeminorm f ≤ E.rootSeminorm g := by
  rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
  exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr h)
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt_p).le)

set_option maxHeartbeats 2400000 in
theorem mem_supportedCoreGraph_closure_of_ae_bound {K U : Set CarpetPoints}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (f : E.domain)
    (hf : ∀ᵐ x ∂carpetMeasure.restrict Kᶜ, (f : CarpetLp p) x = 0) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂carpetMeasure, |(f : CarpetLp p) x| ≤ M) :
    E.toGraph f ∈ closure (E.supportedCoreGraph U : Set E.GraphDomain) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨χ, hχ₀, hχ₁, hχ⟩ := E.exists_core_cutoff hU hK hKU
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr₁ (n : ℕ) : r n ≤ 1 := by
    dsimp [r]
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  choose u hu hnear using fun n ↦ E.regular_graph f (r n) (hr n)
  let v (n : ℕ) : E.continuousCore := ⟨u n, hu n⟩
  choose w hw hweq hW using fun n ↦ E.exists_continuous_comp_energy_le_mul (v n).val
    (v n).property (lipschitzWith_symmetricClip M)
  let c (n : ℕ) : E.continuousCore := ⟨w n, hw n⟩
  let z (n : ℕ) := E.mulCore χ (c n)
  let g (n : ℕ) := E.continuousCoreToDomain (z n)
  have hc (n : ℕ) (x : CarpetPoints) : |(c n).val x| ≤ M := by
    change |w n x| ≤ M
    rw [hweq]
    exact abs_symmetricClip_le hM _
  have hR (n : ℕ) : E.rootSeminorm (E.continuousCoreToDomain (c n)) ≤ ‖E.toGraph f‖ + 1 := by
    have h := hW n
    simp only [NNReal.coe_one, Real.one_rpow, one_mul] at h
    have hh := E.rootSeminorm_le_of_energy_le (NNReal.coe_le_coe.mp h)
    refine hh.trans ((E.rootSeminorm_le_graphSeminorm (E.continuousCoreToDomain (v n))).trans ?_)
    rw [← E.norm_toGraph]
    have hu' : E.toGraph (E.continuousCoreToDomain (v n)) =
        (E.toGraph (E.continuousCoreToDomain (v n)) - E.toGraph f) + E.toGraph f :=
      (sub_add_cancel _ _).symm
    nth_rw 1 [hu']
    have hnear' : ‖E.toGraph (E.continuousCoreToDomain (v n)) - E.toGraph f‖ < r n := hnear n
    exact (norm_add_le _ _).trans (by linarith only [hnear', hr₁ n])
  have hcNorm (n : ℕ) : ‖(c n).val‖ ≤ M :=
    (ContinuousMap.norm_le _ hM).mpr fun x ↦ by rw [Real.norm_eq_abs]; exact hc n x
  have hχNorm : ‖χ.val‖ ≤ 1 :=
    (ContinuousMap.norm_le _ zero_le_one).mpr fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχ x).1]
      exact (hχ x).2
  have hgNorm (n : ℕ) : ‖(g n : CarpetLp p)‖ ≤ M := by
    apply norm_carpetLp_le_of_ae_bound _ hM
    filter_upwards [continuousLp_ae_eq p (z n).val] with x hx
    change (g n : CarpetLp p) x = (z n).val x at hx
    rw [hx, Real.norm_eq_abs, E.mulCore_apply, abs_mul, abs_of_nonneg (hχ x).1]
    exact (mul_le_mul_of_nonneg_right (hχ x).2 (abs_nonneg _)).trans (by simpa only [one_mul] using hc n x)
  let B := 2 * (M * E.rootSeminorm (E.continuousCoreToDomain χ) + (‖E.toGraph f‖ + 1))
  have hgRoot (n : ℕ) : E.rootSeminorm (g n) ≤ B := by
    apply (E.rootSeminorm_mulCore_le_cross χ (c n)).trans
    have h₁ := mul_le_mul_of_nonneg_right (hcNorm n)
      (apply_nonneg E.rootSeminorm (E.continuousCoreToDomain χ))
    have h₂ := mul_le_mul hχNorm (hR n) (apply_nonneg E.rootSeminorm (E.continuousCoreToDomain (c n))) zero_le_one
    rw [one_mul] at h₂
    exact mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by norm_num)
  have hgGraph (n : ℕ) : E.graphSeminorm (g n) ≤ (B ^ p + M ^ p) ^ p⁻¹ :=
    E.graphSeminorm_le_of_le (g n) (hgNorm n) (hgRoot n)
  have hχf : ∀ᵐ x ∂carpetMeasure, χ.val x * (f : CarpetLp p) x = (f : CarpetLp p) x := by
    filter_upwards [(ae_restrict_iff' hK.measurableSet.compl).mp hf] with x hx
    by_cases hxK : x ∈ K
    · rw [hχ₁ x hxK, one_mul]
    · rw [hx hxK, mul_zero]
  have hdist (n : ℕ) : ‖(g n : CarpetLp p) - (f : CarpetLp p)‖ ≤
      ‖(E.continuousCoreToDomain (v n) : CarpetLp p) - (f : CarpetLp p)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    let a : CarpetLp p := E.continuousCoreToDomain (v n)
    let b : CarpetLp p := g n
    let F : CarpetLp p := f
    filter_upwards [Lp.coeFn_sub b F, Lp.coeFn_sub a F, continuousLp_ae_eq p (v n).val,
      continuousLp_ae_eq p (z n).val, hχf, hb] with x h₁ h₂ h₃ h₄ h₅ h₆
    change (b - F) x = b x - F x at h₁
    change (a - F) x = a x - F x at h₂
    change a x = (v n).val x at h₃
    change b x = (z n).val x at h₄
    have hcl := (lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_symmetricClip M)) (a x) (F x)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, symmetricClip_eq_of_abs_le h₆] at hcl
    change ‖(b - F) x‖ ≤ ‖(a - F) x‖
    rw [h₁, h₂, Real.norm_eq_abs, Real.norm_eq_abs, h₄, E.mulCore_apply]
    nth_rw 1 [← h₅]
    change |χ.val x * w n x - χ.val x * F x| ≤ |a x - F x|
    rw [hweq, ← h₃, ← mul_sub, abs_mul, abs_of_nonneg (hχ x).1]
    exact (mul_le_mul_of_nonneg_right (hχ x).2 (abs_nonneg _)).trans (by simpa only [one_mul] using hcl)
  have hlim : Tendsto (fun n ↦ (g n : CarpetLp p)) atTop (𝓝 (f : CarpetLp p)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ ↦ norm_nonneg _) fun n ↦ (hdist n).trans ?_
    have hle := E.norm_coe_le_graphSeminorm (E.continuousCoreToDomain (v n) - f)
    rw [← E.norm_toGraph] at hle
    exact hle.trans (hnear n).le
  obtain ⟨f', hf', htail⟩ := E.exists_mem_graphClosedConvexTails g (f : CarpetLp p) hgGraph hlim
  have hfg : f' = f := Subtype.ext hf'
  rw [← hfg]
  apply closure_mono _ (htail 0)
  apply convexHull_min _ (E.supportedCoreGraph U).convex
  rintro _ ⟨n, _, rfl⟩
  refine ⟨z n, rfl, fun x hx ↦ ?_⟩
  rw [E.mulCore_apply, hχ₀ x hx, zero_mul]

set_option maxHeartbeats 2500000 in
/-- Domain functions vanishing almost everywhere off a closed set are
graph limits of continuous domain functions vanishing off any larger
open set. -/
theorem mem_supportedCoreGraph_closure_of_ae_zero {K U : Set CarpetPoints}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (f : E.domain)
    (hf : ∀ᵐ x ∂carpetMeasure.restrict Kᶜ, (f : CarpetLp p) x = 0) :
    E.toGraph f ∈ closure (E.supportedCoreGraph U : Set E.GraphDomain) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let F : CarpetLp p := f
  choose g hval hent using fun n : ℕ ↦
    E.exists_energyMeasure_comp_le (lipschitzWith_symmetricClip (n : ℝ)) f
  have hval' (n : ℕ) :
      ∀ᵐ x ∂carpetMeasure, (g n : CarpetLp p) x = symmetricClip (n : ℝ) (F x) := hval n
  have he (n : ℕ) : E.energy (g n) ≤ E.energy f := by
    have h := hent n univ
    simp only [NNReal.one_rpow, ENNReal.coe_one, one_smul, E.energyMeasure_univ] at h
    exact ENNReal.coe_le_coe.mp h
  have hnorm (n : ℕ) : ‖(g n : CarpetLp p)‖ ≤ ‖F‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hval' n] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hx]
    exact abs_symmetricClip_le_abs (Nat.cast_nonneg _) _
  have hgraph (n : ℕ) : E.graphSeminorm (g n) ≤ (E.rootSeminorm f ^ p + ‖F‖ ^ p) ^ p⁻¹ :=
    E.graphSeminorm_le_of_le (g n) (hnorm n) (E.rootSeminorm_le_of_energy_le (he n))
  have hmem (n : ℕ) : E.toGraph (g n) ∈ closure (E.supportedCoreGraph U : Set E.GraphDomain) := by
    refine E.mem_supportedCoreGraph_closure_of_ae_bound hK hU hKU (g n) ?_
      (M := (n : ℝ)) (Nat.cast_nonneg _) ?_
    · filter_upwards [hf, (hval' n).filter_mono (ae_mono Measure.restrict_le_self)] with x hx hv
      change F x = 0 at hx
      rw [hv, hx, symmetricClip_zero (Nat.cast_nonneg _)]
    · filter_upwards [hval' n] with x hx
      rw [hx]
      exact abs_symmetricClip_le (Nat.cast_nonneg _) _
  let P (n : ℕ) (x : CarpetPoints) := |((g n : CarpetLp p) - F) x| ^ p
  have hMeas (n : ℕ) : AEStronglyMeasurable (P n) carpetMeasure := by
    have h : Continuous (fun t : ℝ ↦ |t| ^ p) :=
      continuous_abs.rpow_const (fun _ ↦ Or.inr hp.le)
    exact h.comp_aestronglyMeasurable (Lp.aestronglyMeasurable ((g n : CarpetLp p) - F))
  have hInt : Integrable (fun x ↦ (2 * |F x|) ^ p) carpetMeasure := by
    have h := (Lp.memLp F).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    have h' := h.const_mul ((2 : ℝ) ^ p)
    simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _)] using h'
  have hdom (n : ℕ) : ∀ᵐ x ∂carpetMeasure, ‖P n x‖ ≤ (2 * |F x|) ^ p := by
    filter_upwards [Lp.coeFn_sub (g n : CarpetLp p) F, hval' n] with x hx hv
    have hx' : ((g n : CarpetLp p) - F) x = (g n : CarpetLp p) x - F x := hx
    dsimp only [P]
    rw [hx', hv, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    have h := (abs_sub (symmetricClip (n : ℝ) (F x)) (F x)).trans
      (add_le_add_left (abs_symmetricClip_le_abs (Nat.cast_nonneg _) (F x)) _)
    linarith only [h]
  have hpoint : ∀ᵐ x ∂carpetMeasure, Tendsto (fun n ↦ P n x) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.mpr fun n ↦ Lp.coeFn_sub (g n : CarpetLp p) F,
      ae_all_iff.mpr hval'] with x hx hv
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Nat.ceil |F x|)] with n hn
    have heq := symmetricClip_eq_of_abs_le ((Nat.le_ceil _).trans (Nat.cast_le.mpr hn))
    have hx' : ((g n : CarpetLp p) - F) x = (g n : CarpetLp p) x - F x := hx n
    dsimp only [P]
    rw [hx', hv n, heq, sub_self, abs_zero, Real.zero_rpow hp.ne']
  have hpow := tendsto_integral_of_dominated_convergence (fun x ↦ (2 * |F x|) ^ p)
    hMeas hInt hdom hpoint
  simp only [integral_zero] at hpow
  have hpow' : Tendsto (fun n ↦ ‖(g n : CarpetLp p) - F‖ ^ p) atTop (𝓝 0) := by
    convert hpow using 1
    ext n
    exact (integral_abs_rpow_eq_norm_rpow hp _).symm
  have hlim : Tendsto (fun n ↦ (g n : CarpetLp p)) atTop (𝓝 F) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have h := hpow'.rpow_const (Or.inr (inv_nonneg.mpr hp.le))
    simpa only [Real.rpow_rpow_inv (norm_nonneg _) hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')] using h
  obtain ⟨f', hf', htail⟩ := E.exists_mem_graphClosedConvexTails g F hgraph hlim
  rw [← (Subtype.ext hf' : f' = f)]
  refine closure_minimal (convexHull_min ?_ (E.supportedCoreGraph U).convex.closure)
    isClosed_closure (htail 0)
  rintro _ ⟨n, _, rfl⟩
  exact hmem n

end CarpetEnergy.SelfSimilarPEnergy
