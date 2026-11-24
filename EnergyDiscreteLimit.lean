import EnergyDiscreteInterpolation
import EnergyGammaComparison

/-!
# Comparing discrete limits with a self-similar energy

A discrete-energy bound along a sequence of increasingly fine levels
gives a continuum-energy bound. The cellwise interpolation remains
graph-norm bounded and its difference from the piecewise-constant lift
tends to zero in Lp.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)
variable [Fact (1 ≤ ENNReal.ofReal p)]

theorem exists_energy_le_of_tendsto_discreteCellEnergy :
    ∃ C > (0 : ℝ), ∀ (j : ℕ → ℕ) (u : ℕ → CarpetLp p) (f : CarpetLp p)
      (B : ℝ≥0), Tendsto j atTop atTop → Tendsto u atTop (𝓝 f) →
      (∀ n, discreteCellEnergy p E.scalingFactor (j n) (u n) ≤ (B : ℝ≥0∞)) →
      ∃ v : E.domain, (v : CarpetLp p) = f ∧ (E.energy v : ℝ) ≤ C * (B : ℝ) := by
  obtain ⟨P⟩ := E.exists_zeroCornerProfile
  obtain ⟨A, hA, hi⟩ := P.exists_interpolate_cellValues
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hρ : 0 < E.scalingFactor := E.isScalingFactor_scalingFactor.1
  let C := 2 * A + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun j u f B hj hu hB ↦ ?_⟩
  choose g hdom _ hg henergy using
    fun n ↦ hi (j n) (fun w ↦ ambientWordMean p (List.ofFn w) (u n))
  let d (n : ℕ) : E.domain := ⟨continuousLp p (g n), hdom n⟩
  have hdE (n : ℕ) : (E.energy (d n) : ℝ) ≤ C * (B : ℝ) := by
    let S := ∑ w : Fin (j n) → Fin 8, ∑ v ∈ gridNeighbors w,
      |ambientWordMean p (List.ofFn w) (u n) - ambientWordMean p (List.ofFn v) (u n)| ^ p
    have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg
      (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _))
    have h := hB n
    rw [discreteCellEnergy_eq_grid hp (j n), ← ENNReal.ofReal_coe_nnreal] at h
    have hb : E.scalingFactor ^ j n / 2 * S ≤ (B : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg B)).mp h
    have he : (E.energy (d n) : ℝ) ≤ A * (E.scalingFactor ^ j n * S) := henergy n
    have hk := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * A by positivity)
    rw [show 2 * A * (E.scalingFactor ^ j n / 2 * S) =
      A * (E.scalingFactor ^ j n * S) by ring] at hk
    exact he.trans (hk.trans (by dsimp only [C]; linarith [NNReal.coe_nonneg B]))
  have hscale : 1 < 8 * E.scalingFactor := by
    have h₁ := E.three_rpow_div_eight_le_scalingFactor
    have h₂ := Real.one_lt_rpow (show (1 : ℝ) < 3 by norm_num) hp
    linarith [(div_le_iff₀ (show 0 < (8 : ℝ) by norm_num)).mp h₁]
  have hr₀ : 0 ≤ (8 * E.scalingFactor)⁻¹ := by positivity
  have hr₁ : (8 * E.scalingFactor)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hscale
  have hdecay : Tendsto (fun n ↦ 2 * ((8 * E.scalingFactor)⁻¹) ^ j n * (B : ℝ))
      atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).comp hj).const_mul (2 : ℝ)
    simpa only [mul_zero, zero_mul, Function.comp_apply] using h.mul_const (B : ℝ)
  have hdiff : Tendsto (fun n ↦ (d n : CarpetLp p) - cellAveraging p (j n) (u n))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    rw [tendsto_order]
    refine ⟨fun a ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _), fun a ha ↦ ?_⟩
    filter_upwards [hdecay.eventually_lt_const (Real.rpow_pos_of_pos ha p)] with n hn
    have hbound := P.norm_sub_cellAveraging_rpow_le (j n) (u n) (g n) (hg n)
    have hb : (discreteCellEnergy p E.scalingFactor (j n) (u n)).toReal ≤ (B : ℝ) := by
      simpa only [ENNReal.coe_toReal] using ENNReal.toReal_mono ENNReal.coe_ne_top (hB n)
    apply (Real.rpow_lt_rpow_iff (norm_nonneg _) ha.le hp).mp
    exact (hbound.trans (mul_le_mul_of_nonneg_left hb (by positivity))).trans_lt hn
  have hproj := cellAveraging_tendsto_of_tendsto E.one_lt_p.le hj hu
  have ht : Tendsto (fun n ↦ (d n : CarpetLp p)) atTop (𝓝 f) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add hproj
  obtain ⟨L, hL⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto (fun n ↦ (d n : CarpetLp p)) ht)
  let R := (C * (B : ℝ)) ^ p⁻¹
  have hroot (n : ℕ) : E.rootSeminorm (d n) ≤ R := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (E.energy (d n)).property (hdE n) (inv_nonneg.mpr hp.le)
  obtain ⟨v, hv, hvr⟩ := E.exists_domain_of_tendsto_of_seminorm_le E.rootSeminorm
    E.rootSeminorm_le_graphSeminorm d f
    (fun n ↦ E.graphSeminorm_le_of_le (d n) (hL _ (mem_range_self n)) (hroot n))
    (fun a ha ↦ Eventually.of_forall fun n ↦ (hroot n).trans ha.le) ht
  refine ⟨v, hv, ?_⟩
  rw [E.rootSeminorm_apply] at hvr
  exact (Real.rpow_le_rpow_iff (E.energy v).property (by positivity) (inv_pos.mpr hp)).mp hvr


theorem exists_discreteCellEnergy_le :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ n (v : E.domain),
      discreteCellEnergy p E.scalingFactor n v ≤ (C : ℝ≥0∞) * E.energy v := by
  obtain ⟨B, hB, hgrid⟩ := E.exists_gridMean_energy_le
  let C : ℝ≥0 := ⟨B / 2, by positivity⟩
  refine ⟨C, by exact_mod_cast (show 0 < B / 2 by positivity), fun n v ↦ ?_⟩
  let L : E.GraphDomain → ℝ≥0∞ := fun z ↦
    discreteCellEnergy p E.scalingFactor n (E.graphInclusion z)
  let R : E.GraphDomain → ℝ := fun z ↦ E.rootSeminorm (E.graphToDomain z)
  have hL : Continuous L :=
    (continuous_discreteCellEnergy (zero_lt_one.trans E.one_lt_p) n).comp E.graphInclusion.continuous
  let s : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hR : Continuous R := Seminorm.continuous_of_le (p := E.rootSeminorm.comp s)
    (q := normSeminorm ℝ E.GraphDomain) continuous_norm
    (fun z ↦ E.rootSeminorm_le_graphSeminorm (E.graphToDomain z))
  let U : E.GraphDomain → ℝ≥0∞ := fun z ↦ ENNReal.ofReal ((C : ℝ) * R z ^ p)
  have hU : Continuous U := ENNReal.continuous_ofReal.comp
    (((Real.continuous_rpow_const (zero_le_one.trans E.one_lt_p.le)).comp hR).const_mul (C : ℝ))
  have hUeq (z : E.domain) : U (E.toGraph z) = (C : ℝ≥0∞) * E.energy z := by
    dsimp only [U, R]
    change ENNReal.ofReal ((C : ℝ) * E.rootSeminorm z ^ p) = _
    rw [E.rootSeminorm_apply, Real.rpow_inv_rpow (NNReal.coe_nonneg (E.energy z))
      (zero_lt_one.trans E.one_lt_p).ne', ← ENNReal.coe_mul]
    simpa only [NNReal.coe_mul] using (ENNReal.ofReal_coe_nnreal (p := C * E.energy z))
  have hc (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain) :
      L (E.toGraph ⟨continuousLp p f, hf⟩) ≤ U (E.toGraph ⟨continuousLp p f, hf⟩) := by
    let z : E.domain := ⟨continuousLp p f, hf⟩
    change discreteCellEnergy p E.scalingFactor n (continuousLp p f) ≤ U (E.toGraph z)
    rw [hUeq, ← ENNReal.coe_mul]
    rw [discreteCellEnergy_eq_grid (zero_lt_one.trans E.one_lt_p) n]
    simp_rw [ambientWordMean_continuousLp]
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hh := hgrid n f hf
    change E.scalingFactor ^ n / 2 * (∑ w : Fin n → Fin 8, ∑ v ∈ gridNeighbors w,
      |continuousWordMean f (List.ofFn w) - continuousWordMean f (List.ofFn v)| ^ p)
        ≤ B / 2 * (E.energy z : ℝ)
    linarith
  have hclosed : IsClosed {z | L z ≤ U z} := isClosed_le hL hU
  have hmem : E.toGraph v ∈ {z | L z ≤ U z} := by
    apply hclosed.closure_subset_iff.mpr
      (show {z | ∃ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain),
        z = E.toGraph ⟨continuousLp p f, hf⟩} ⊆ {z | L z ≤ U z} from by
        rintro z ⟨f, hf, rfl⟩
        exact hc f hf)
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨f, hf, hdist⟩ := E.regular_graph v ε hε
    refine ⟨E.toGraph ⟨continuousLp p f, hf⟩, ⟨f, hf, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact hdist
  change L (E.toGraph v) ≤ (C : ℝ≥0∞) * E.energy v
  rw [← hUeq]
  exact hmem

theorem IsGammaLimit.energy_le_mul_discreteLimit {j : ℕ → ℕ} (hj : StrictMono j)
    {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ f : CarpetLp p, F f < ∞ →
      ∃ v : E.domain, (v : CarpetLp p) = f ∧ (E.energy v : ℝ≥0∞) ≤ (C : ℝ≥0∞) * F f := by
  obtain ⟨D, hD, he⟩ := E.exists_energy_le_of_tendsto_discreteCellEnergy
  let C : ℝ≥0 := ⟨D, hD.le⟩
  have hC : 0 < C := by exact_mod_cast hD
  refine ⟨C, hC, fun f hf ↦ ?_⟩
  have h (a : ℝ≥0) (ha : F f < (a : ℝ≥0∞)) :
      ∃ v : E.domain, (v : CarpetLp p) = f ∧ (E.energy v : ℝ≥0∞) ≤ (C : ℝ≥0∞) * a := by
    obtain ⟨k, u, hk, hu, hE⟩ := hF.exists_tendsto_of_lt f ha
    obtain ⟨v, hv, hvE⟩ := he (j ∘ k) u f a (hj.tendsto_atTop.comp hk) hu (fun n ↦ (hE n).le)
    exact ⟨v, hv, by exact_mod_cast hvE⟩
  obtain ⟨a, ha, _⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hf
  obtain ⟨v, hv, _⟩ := h a ha
  refine ⟨v, hv, ?_⟩
  by_contra! hlt
  have hdiv : F f < (E.energy v : ℝ≥0∞) / (C : ℝ≥0∞) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl (by exact_mod_cast hC.ne')) (Or.inl ENNReal.coe_ne_top)).mpr
      (by simpa only [mul_comm] using hlt)
  obtain ⟨a, ha, hav⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hdiv
  obtain ⟨w, hw, hwE⟩ := h a ha
  have hwv : w = v := Subtype.ext (hw.trans hv.symm)
  rw [hwv] at hwE
  exact (not_lt_of_ge hwE) (by
    have hlt' := (ENNReal.lt_div_iff_mul_lt (Or.inl (by exact_mod_cast hC.ne'))
      (Or.inl ENNReal.coe_ne_top)).mp hav
    simpa only [mul_comm] using hlt')

/-- Every Γ-limit at the scale of an existing self-similar energy is finite
on exactly its domain and bounded by a multiple of its energy. -/
theorem IsGammaLimit.discreteLimit_domain_eq {j : ℕ → ℕ} (hj : StrictMono j)
    {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F) :
    {f | F f < ∞} = (E.domain : Set (CarpetLp p)) := by
  obtain ⟨C, _, hgrid⟩ := E.exists_discreteCellEnergy_le
  obtain ⟨D, _, hcont⟩ := IsGammaLimit.energy_le_mul_discreteLimit E hj hF
  ext f
  constructor
  · intro hf
    obtain ⟨v, hv, _⟩ := hcont f hf
    exact hv ▸ v.property
  · intro hf
    let v : E.domain := ⟨f, hf⟩
    have h : F f ≤ (C : ℝ≥0∞) * E.energy v :=
      (hF.le_iSup f).trans (iSup_le fun n ↦ hgrid (j n) v)
    exact h.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)


/-- On the common domain a Γ-limit at the self-similar scale is
comparable to the original energy, in both directions. -/
theorem IsGammaLimit.discreteLimit_comparable {j : ℕ → ℕ} (hj : StrictMono j)
    {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F) :
    ∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ v : E.domain,
      A * (E.energy v : ℝ) ≤ (F v).toReal ∧ (F v).toReal ≤ B * (E.energy v : ℝ) := by
  obtain ⟨C, hC, hgrid⟩ := E.exists_discreteCellEnergy_le
  obtain ⟨D, hD, hcont⟩ := IsGammaLimit.energy_le_mul_discreteLimit E hj hF
  have hC₀ : 0 < (C : ℝ) := by exact_mod_cast hC
  have hD₀ : 0 < (D : ℝ) := by exact_mod_cast hD
  refine ⟨(D : ℝ)⁻¹, inv_pos.mpr hD₀, C, hC₀, fun v ↦ ?_⟩
  have h := (hF.le_iSup (v : CarpetLp p)).trans (iSup_le fun n ↦ hgrid (j n) v)
  have htop := ENNReal.mul_lt_top (a := (C : ℝ≥0∞)) (b := (E.energy v : ℝ≥0∞))
    ENNReal.coe_lt_top ENNReal.coe_lt_top
  obtain ⟨w, hw, h'⟩ := hcont v (h.trans_lt htop)
  have hEq : w = v := Subtype.ext hw
  rw [hEq] at h'
  have hlo := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (h.trans_lt htop).ne) h'
  have hhi := ENNReal.toReal_mono htop.ne h
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hlo hhi
  exact ⟨(inv_mul_le_iff₀ hD₀).mpr (by simpa only [mul_comm (D : ℝ)] using hlo), hhi⟩

end CarpetEnergy.SelfSimilarPEnergy
