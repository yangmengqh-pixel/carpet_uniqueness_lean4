import EnergySideNullity

/-!
# Energy measures vanish on cell boundaries

The interpolation with linear traces gives null energy mass on the
outer sides. Uniformly energy-bounded approximation then gives outer
boundary nullity on the entire domain, and self-similarity propagates
it to every cell boundary.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent SelfSimilarComponent.CornerProfile

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem interpolate_energyMeasure_boundary_eq_zero
    (P : E.zeroComponent.CornerProfile)
    (hP : ∀ z : CarpetPoints, (z : Plane) 1 = 0 ∨ (z : Plane) 1 = 1 →
      P.toContinuousMap z = (z : Plane) 0)
    (a : Fin 2 → Fin 2 → ℝ) (hf : continuousLp p (P.interpolate a) ∈ E.domain) :
    E.energyMeasure ⟨continuousLp p (P.interpolate a), hf⟩ carpetOuterBoundary = 0 := by
  apply measure_iUnion_null
  intro j
  apply measure_iUnion_null
  intro b
  have ha (t : Fin 2) (x : CarpetPoints) (hx : (x : Plane) 1 = t.val) :
      P.toContinuousMap x = (x : Plane) 0 := by
    apply hP
    fin_cases t
    · exact Or.inl hx
    · exact Or.inr hx
  have hV (t : Fin 2) (x : CarpetPoints) (hx : (x : Plane) 0 = t.val) :
      P.vertical x = (x : Plane) 1 := by
    exact ha t (carpetSymmetry axisSwap x) hx
  fin_cases j
  · change E.energyMeasure ⟨_, hf⟩ (carpetSide 0 b) = 0
    apply E.energyMeasure_carpetSide_eq_zero_of_affine (P.interpolate a)
      P.vertical hf P.vertical_mem_kernel.choose 0 b (a b 1 - a b 0) (a b 0)
    · intro x hx
      have h := hV b x hx
      rw [P.interpolate_vertical_side a b x hx, h]
      change (1 - (x : Plane) 1) * a b 0 + (x : Plane) 1 * a b 1 =
        (a b 1 - a b 0) * (x : Plane) 1 + a b 0
      ring
    · intro x hx
      exact hV b x hx
  · change E.energyMeasure ⟨_, hf⟩ (carpetSide 1 b) = 0
    apply E.energyMeasure_carpetSide_eq_zero_of_affine (P.interpolate a)
      P.toContinuousMap hf P.mem_kernel.choose 1 b (a 1 b - a 0 b) (a 0 b)
    · intro x hx
      have h := ha b x hx
      rw [P.interpolate_horizontal_side a b x hx, h]
      change (1 - (x : Plane) 0) * a 0 b + (x : Plane) 0 * a 1 b =
        (a 1 b - a 0 b) * (x : Plane) 0 + a 0 b
      ring
    · intro x hx
      exact ha b x hx

private theorem energyMeasure_boundary_eq_zero_of_cellwise_interpolation
    (P : E.zeroComponent.CornerProfile)
    (hP : ∀ z : CarpetPoints, (z : Plane) 1 = 0 ∨ (z : Plane) 1 = 1 →
      P.toContinuousMap z = (z : Plane) 0)
    (n : ℕ) (g : C(CarpetPoints, ℝ)) (hg : continuousLp p g ∈ E.domain)
    (a : (Fin n → Fin 8) → Fin 2 → Fin 2 → ℝ)
    (hG : ∀ (w : Fin n → Fin 8) x, g (wordMap (List.ofFn w) x) = P.interpolate (a w) x) :
    E.energyMeasure ⟨continuousLp p g, hg⟩ carpetOuterBoundary = 0 := by
  let u : E.domain := ⟨continuousLp p g, hg⟩
  rw [E.energyMeasure_eq_sum_words n u, Measure.sum_apply _ measurableSet_carpetOuterBoundary]
  apply tsum_eq_zero_iff.mpr
  intro w
  rw [smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_wordMap _).measurable measurableSet_carpetOuterBoundary]
  have he := continuousLp_interpolate_word_eq g hg (P.interpolate (a w)) _ (hG w)
  have hw : continuousLp p (P.interpolate (a w)) ∈ E.domain := he.symm ▸ (E.pullbackWord _ u).property
  have he' : (⟨continuousLp p (P.interpolate (a w)), hw⟩ : E.domain) =
      E.pullbackWord (List.ofFn w) u := Subtype.ext he
  have hsub : wordMap (List.ofFn w) ⁻¹' carpetOuterBoundary ⊆ carpetOuterBoundary := by
    intro x hx
    obtain ⟨j, b, hj⟩ := (mem_carpetOuterBoundary _).mp hx
    exact (mem_carpetOuterBoundary x).mpr ⟨j, b, (wordMap_preimage_side w j b x hj).1⟩
  rw [← he', measure_mono_null hsub (E.interpolate_energyMeasure_boundary_eq_zero P hP (a w) hw), mul_zero]

private theorem energyMeasure_boundary_eq_zero_continuous (f : C(CarpetPoints, ℝ))
    (hf : continuousLp p f ∈ E.domain) :
    E.energyMeasure ⟨continuousLp p f, hf⟩ carpetOuterBoundary = 0 := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨P, hP⟩ := E.exists_cornerProfile_linear_traces
  obtain ⟨C, hC, hinterp⟩ := P.exists_interpolate_cellValues
  obtain ⟨D, _, hgrid⟩ := E.exists_gridMean_energy_le
  choose g hg _ hG he using fun n ↦ hinterp n (fun v ↦ continuousWordMean f (List.ofFn v))
  let u (n : ℕ) : E.domain := ⟨continuousLp p (g n), hg n⟩
  let B := C * (D * (E.energy ⟨continuousLp p f, hf⟩ : ℝ))
  have henergy (n : ℕ) : (E.energy (u n) : ℝ) ≤ B :=
    (he n).trans (mul_le_mul_of_nonneg_left (hgrid n f hf) hC)
  obtain ⟨hL, hlim⟩ := P.cellMeanInterpolation_tendsto f g hG
  have hgraph (n : ℕ) : E.graphSeminorm (u n) ≤ ((B ^ p⁻¹) ^ p + ‖f‖ ^ p) ^ p⁻¹ := by
    apply E.graphSeminorm_le_of_le (u n) (hL n)
    rw [E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (henergy n) (inv_nonneg.mpr hp.le)
  let S := E.energyMeasureSeminorm carpetOuterBoundary measurableSet_carpetOuterBoundary
  have hS : S ≤ E.graphSeminorm := fun x ↦
    (E.energyMeasureSeminorm_le_rootSeminorm _ _ x).trans (E.rootSeminorm_le_graphSeminorm x)
  have hz (n : ℕ) : S (u n) = 0 := by
    have h := E.energyMeasure_boundary_eq_zero_of_cellwise_interpolation P hP n (g n) (hg n)
      (fun w ↦ cornerData (cornerAverage n (fun v ↦ continuousWordMean f (List.ofFn v))) (List.ofFn w)) (hG n)
    change (E.energyMeasure (u n) carpetOuterBoundary).toReal ^ p⁻¹ = 0
    rw [h, ENNReal.toReal_zero, Real.zero_rpow (inv_ne_zero hp.ne')]
  obtain ⟨v, hv, hroot⟩ := E.exists_domain_of_tendsto_of_seminorm_le S hS u (continuousLp p f) hgraph
    (R := 0) (fun r hr ↦ Eventually.of_forall fun n ↦ (hz n).trans_le hr.le) hlim
  have hv' : v = (⟨continuousLp p f, hf⟩ : E.domain) := Subtype.ext hv
  have hn := hroot.antisymm (apply_nonneg S v)
  change (E.energyMeasure v carpetOuterBoundary).toReal ^ p⁻¹ = 0 at hn
  have hz' := (Real.rpow_eq_zero ENNReal.toReal_nonneg (inv_ne_zero hp.ne')).mp hn
  rw [← hv']
  rw [← ENNReal.ofReal_toReal (measure_ne_top (E.energyMeasure v) carpetOuterBoundary),
    hz', ENNReal.ofReal_zero]

/-- Equation (4.4) for the outer boundary, for every energy satisfying Definition 2.1. -/
theorem energyMeasure_carpetOuterBoundary_eq_zero (f : E.domain) :
    E.energyMeasure f carpetOuterBoundary = 0 := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let S := E.energyMeasureSeminorm carpetOuterBoundary measurableSet_carpetOuterBoundary
  let toDomain : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let T := S.comp toDomain
  have hT : Continuous T :=
    Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm (fun z ↦
      (E.energyMeasureSeminorm_le_rootSeminorm carpetOuterBoundary measurableSet_carpetOuterBoundary (E.graphToDomain z)).trans
        (E.rootSeminorm_le_graphSeminorm _))
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose u hu hnear using fun n ↦ E.regular_graph f (ε n) (hε n)
  let g (n : ℕ) : E.domain := ⟨continuousLp p (u n), hu n⟩
  have hlim : Tendsto (fun n ↦ E.toGraph (g n)) atTop (𝓝 (E.toGraph f)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ ↦ norm_nonneg _)
      (fun n ↦ (hnear n).le)
  have hz (n : ℕ) : T (E.toGraph (g n)) = 0 := by
    change (E.energyMeasure (g n) carpetOuterBoundary).toReal ^ p⁻¹ = 0
    rw [E.energyMeasure_boundary_eq_zero_continuous (u n) (hu n),
      ENNReal.toReal_zero, Real.zero_rpow (inv_ne_zero hp.ne')]
  have hzlim : Tendsto (fun n ↦ T (E.toGraph (g n))) atTop (𝓝 0) := by
    rw [show (fun n ↦ T (E.toGraph (g n))) = (fun _ ↦ 0) from funext hz]
    exact tendsto_const_nhds
  have he : T (E.toGraph f) = 0 :=
    tendsto_nhds_unique ((hT.tendsto _).comp hlim) hzlim
  change (E.energyMeasure f carpetOuterBoundary).toReal ^ p⁻¹ = 0 at he
  have hf := (Real.rpow_eq_zero ENNReal.toReal_nonneg (inv_ne_zero hp.ne')).mp he
  rw [← ENNReal.ofReal_toReal (measure_ne_top (E.energyMeasure f) carpetOuterBoundary),
    hf, ENNReal.ofReal_zero]

/-- Equation (4.4) for the countable union of all cell boundaries. -/
theorem energyMeasure_allCellBoundaries_eq_zero (f : E.domain) :
    E.energyMeasure f carpetAllCellBoundaries = 0 :=
  E.energyMeasure_carpetAllCellBoundaries_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero f

end CarpetEnergy.SelfSimilarPEnergy
