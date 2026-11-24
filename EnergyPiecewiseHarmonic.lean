import EnergyZeroTraceExtension

/-!
# Density of piecewise harmonic functions

A test vanishing on a cell boundary extends by zero to a variational
competitor on the whole carpet. The global minimizer is therefore
harmonic on each cell. The nested replacements give graph-norm density.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Harmonicity tested against continuous energy-domain functions with
zero exterior trace. In particular it holds against the continuous
compactly supported interior core. -/
def IsInteriorHarmonic (g : E.domain) : Prop :=
  ∀ (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain),
    (∀ x ∈ carpetOuterBoundary, u x = 0) →
    E.energy g ≤ E.energy (g + ⟨continuousLp p u, hu⟩)

/-- The variational interior test space is the graph closure of the
continuous finite-energy functions compactly supported in the interior. -/
noncomputable def interiorTestSpace : Set E.GraphDomain :=
  closure {z | ∃ u : C(CarpetPoints, ℝ),
    continuousLp p u = (E.graphToDomain z : CarpetLp p) ∧
    tsupport (u : CarpetPoints → ℝ) ⊆ carpetOuterBoundaryᶜ}

theorem IsInteriorHarmonic.energy_le_add_test {g : E.domain}
    (hg : E.IsInteriorHarmonic g) {u : E.GraphDomain} (hu : u ∈ E.interiorTestSpace) :
    E.energy g ≤ E.energy (g + E.graphToDomain u) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let toDomain : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := E.rootSeminorm.comp toDomain
  have hS : Continuous S :=
    Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm
      (fun z ↦ E.rootSeminorm_le_graphSeminorm (E.graphToDomain z))
  let P : E.GraphDomain → ℝ := fun z ↦ (E.energy (g + E.graphToDomain z) : ℝ)
  have hP : Continuous P := by
    have he : ∀ z : E.GraphDomain, P z = S (E.toGraph g + z) ^ p := by
      intro z
      change (E.energy (g + E.graphToDomain z) : ℝ) = E.rootSeminorm (g + E.graphToDomain z) ^ p
      rw [E.rootSeminorm_apply]
      exact (Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne').symm
    simp only [funext he]
    exact (hS.comp (continuous_const.add continuous_id)).rpow_const (fun _ ↦ Or.inr hp.le)
  have hc : E.interiorTestSpace ⊆ {z | (E.energy g : ℝ) ≤ P z} := by
    apply closure_minimal _ (isClosed_le continuous_const hP)
    rintro z ⟨v, hv, hs⟩
    have hv' : continuousLp p v ∈ E.domain := hv.symm ▸ (E.graphToDomain z).property
    have he : (⟨continuousLp p v, hv'⟩ : E.domain) = E.graphToDomain z := Subtype.ext hv
    have hzero (x : CarpetPoints) (hx : x ∈ carpetOuterBoundary) : v x = 0 := by
      by_contra h
      exact (hs (subset_tsupport _ h)) hx
    have h := hg v hv' hzero
    rw [he] at h
    exact NNReal.coe_le_coe.mpr h
  exact NNReal.coe_le_coe.mp (hc hu)

private theorem boundaryCompetitors_translate
    (n : ℕ) (f v : C(CarpetPoints, ℝ)) (hv : continuousLp p v ∈ E.domain)
    (htrace : ∀ x ∈ carpetCellBoundary n, v x = 0) {z : E.GraphDomain}
    (hz : z ∈ closure (E.boundaryCompetitors n f)) :
    z + E.toGraph ⟨continuousLp p v, hv⟩ ∈ closure (E.boundaryCompetitors n f) := by
  let V : E.GraphDomain := E.toGraph ⟨continuousLp p v, hv⟩
  let U := E.boundaryCompetitors n f
  have hc : closure U ⊆ (fun x ↦ x + V) ⁻¹' closure U := by
    apply closure_minimal _ (isClosed_closure.preimage (continuous_id.add continuous_const))
    rintro z ⟨u, hu, huf⟩
    refine subset_closure ⟨u + v, ?_, ?_⟩
    · change continuousLpLinear p (u + v) = _
      rw [map_add]
      change continuousLp p u + continuousLp p v =
        (E.graphToDomain z : CarpetLp p) + continuousLp p v
      rw [hu]
    · intro x hx
      change u x + v x = f x
      rw [huf x hx, htrace x hx, add_zero]
  exact hc hz

private theorem isInteriorHarmonic_pullbackWord_of_cellBoundary_variation
    (n : ℕ) (Z : E.domain)
    (hmin : ∀ (v : C(CarpetPoints, ℝ)) (hv : continuousLp p v ∈ E.domain),
      (∀ x ∈ carpetCellBoundary n, v x = 0) →
      E.energy Z ≤ E.energy (Z + ⟨continuousLp p v, hv⟩))
    (w : Fin n → Fin 8) :
    E.IsInteriorHarmonic (E.pullbackWord (List.ofFn w) Z) := by
  classical
  intro u hu htrace
  obtain ⟨v, hv, hzero, htarget, hother⟩ := E.exists_zeroTrace_extension n w u hu htrace
  let V : E.domain := ⟨continuousLp p v, hv⟩
  let U : E.domain := ⟨continuousLp p u, hu⟩
  have hW : E.pullbackWord (List.ofFn w) V = U :=
    Subtype.ext (continuousLp_interpolate_word_eq v hv u _ htarget).symm
  have hO (a : Fin n → Fin 8) (ha : a ≠ w) :
      E.pullbackWord (List.ofFn a) V = 0 := by
    let c := ContinuousMap.const CarpetPoints (0 : ℝ)
    have h := continuousLp_interpolate_word_eq v hv c (List.ofFn a) (hother a ha)
    apply Subtype.ext
    rw [← h]
    apply Lp.ext
    exact (continuousLp_ae_eq p c).trans (Lp.coeFn_zero _ _ _).symm
  have hd : (E.energy Z : ℝ) ≤ (E.energy (Z + V) : ℝ) :=
    NNReal.coe_le_coe.mpr (hmin v hv hzero)
  rw [E.energy_eq_sum_words n Z, E.energy_eq_sum_words n (Z + V)] at hd
  have hp := pow_pos E.isScalingFactor_scalingFactor.1 n
  have hs := le_of_mul_le_mul_left hd hp
  let A (a : Fin n → Fin 8) := (E.energy (E.pullbackWord (List.ofFn a) Z) : ℝ)
  let B (a : Fin n → Fin 8) := (E.energy (E.pullbackWord (List.ofFn a) (Z + V)) : ℝ)
  change (∑ a, A a) ≤ ∑ a, B a at hs
  have hsum : ∑ a ∈ Finset.univ.erase w, A a = ∑ a ∈ Finset.univ.erase w, B a := by
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := (Finset.mem_erase.mp ha).1
    dsimp only [A, B]
    rw [E.pullbackWord_add, hO a ha', add_zero]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ w),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ w), hsum] at hs
  have hh : A w ≤ B w := le_of_add_le_add_left hs
  dsimp only [A, B] at hh
  rw [E.pullbackWord_add, hW] at hh
  exact NNReal.coe_le_coe.mp hh

/-- Every cell pullback of a boundary minimizer is interior-harmonic. -/
theorem isInteriorHarmonic_pullbackWord_of_boundary_minimizer
    (n : ℕ) (f : C(CarpetPoints, ℝ)) (z : E.GraphDomain)
    (hz : z ∈ closure (E.boundaryCompetitors n f))
    (hmin : ∀ w ∈ closure (E.boundaryCompetitors n f),
      E.energy (E.graphToDomain z) ≤ E.energy (E.graphToDomain w))
    (w : Fin n → Fin 8) :
    E.IsInteriorHarmonic (E.pullbackWord (List.ofFn w) (E.graphToDomain z)) := by
  apply E.isInteriorHarmonic_pullbackWord_of_cellBoundary_variation n _ _ w
  intro v hv hzero
  exact hmin (z + E.toGraph ⟨continuousLp p v, hv⟩)
    (E.boundaryCompetitors_translate n f v hv hzero hz)

theorem IsInteriorHarmonic.pullbackWord {f : E.domain} (hf : E.IsInteriorHarmonic f)
    (w : List (Fin 8)) : E.IsInteriorHarmonic (E.pullbackWord w f) := by
  let n := w.length
  let W : Fin n → Fin 8 := w.get
  rw [show w = List.ofFn W from (List.ofFn_get w).symm]
  apply E.isInteriorHarmonic_pullbackWord_of_cellBoundary_variation n _ _ W
  intro v hv hz
  exact hf v hv (fun x hx ↦ hz x (carpetOuterBoundary_subset_cellBoundary n hx))

/-- The piecewise harmonic functions are dense in the energy graph norm. -/
theorem exists_piecewiseHarmonic_graph_approximation (f : E.domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (u : E.domain), (∀ w : Fin n → Fin 8,
      E.IsInteriorHarmonic (E.pullbackWord (List.ofFn w) u)) ∧ E.graphSeminorm (u - f) < ε := by
  obtain ⟨v, hv, hnear⟩ := E.regular_graph f (ε / 2) (half_pos hε)
  let V : E.domain := ⟨continuousLp p v, hv⟩
  obtain ⟨n, z, _, _, hz, hmin, hlim⟩ := E.exists_boundary_replacement_tendsto v hv
  obtain ⟨k, hk⟩ : ∃ k, dist (z k) (E.toGraph V) < ε / 2 :=
    (hlim.eventually (Metric.ball_mem_nhds _ (half_pos hε))).exists
  let u := E.graphToDomain (z k)
  refine ⟨n k, u, fun w ↦ E.isInteriorHarmonic_pullbackWord_of_boundary_minimizer _ v
    (z k) (hz k) (hmin k) w, ?_⟩
  rw [dist_eq_norm] at hk
  have h₁ : E.graphSeminorm (u - V) < ε / 2 := hk
  calc
    _ = E.graphSeminorm ((u - V) + (V - f)) := by rw [sub_add_sub_cancel]
    _ ≤ E.graphSeminorm (u - V) + E.graphSeminorm (V - f) := map_add_le_add _ _ _
    _ < _ := by linarith

end CarpetEnergy.SelfSimilarPEnergy
