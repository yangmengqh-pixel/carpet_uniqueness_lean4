import EnergyCellClamp

/-!
# Variational replacement with word-cell boundary data

Continuous competitors agreeing on the level boundary can be clamped
without raising their energy. Closed graph-norm sublevels then give a
minimizer in the closure of the continuous competitors.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Continuous energy-domain functions agreeing with the datum on the
level boundary, viewed as points of the graph space. -/
def boundaryCompetitors (n : ℕ) (f : C(CarpetPoints, ℝ)) : Set E.GraphDomain :=
  {z | ∃ u : C(CarpetPoints, ℝ),
    continuousLp p u = (E.graphToDomain z : CarpetLp p) ∧
    ∀ x ∈ carpetCellBoundary n, u x = f x}

theorem convex_boundaryCompetitors (n : ℕ) (f : C(CarpetPoints, ℝ)) :
    Convex ℝ (E.boundaryCompetitors n f) := by
  rintro z ⟨u, hu, huf⟩ w ⟨v, hv, hvf⟩ a b _ _ hab
  refine ⟨a • u + b • v, ?_, ?_⟩
  · change continuousLpLinear p (a • u + b • v) = _
    rw [map_add, map_smul, map_smul]
    change a • continuousLp p u + b • continuousLp p v =
      a • (E.graphToDomain z : CarpetLp p) + b • (E.graphToDomain w : CarpetLp p)
    rw [hu, hv]
  · intro x hx
    change a * u x + b * v x = f x
    rw [huf x hx, hvf x hx, ← add_mul, hab, one_mul]

/-- A variational replacement keeps the ambient error below the maximal
oscillation of the boundary datum on level cells. -/
theorem exists_minimizer_boundaryCompetitors (n : ℕ) (f : C(CarpetPoints, ℝ))
    (hf : continuousLp p f ∈ E.domain) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ (w : Fin n → Fin 8) x y,
      |f (wordMap (List.ofFn w) x) - f (wordMap (List.ofFn w) y)| ≤ ε) :
    ∃ z ∈ closure (E.boundaryCompetitors n f),
      ‖(E.graphToDomain z : CarpetLp p) - continuousLp p f‖ ≤ ε ∧
      ∀ w ∈ closure (E.boundaryCompetitors n f),
        E.energy (E.graphToDomain z) ≤ E.energy (E.graphToDomain w) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let U := E.boundaryCompetitors n f
  let T := E.graphInclusion
  let f' := continuousLp p f
  let toDomain : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := E.rootSeminorm.comp toDomain
  have hS : Continuous S :=
    Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm
      (fun z ↦ E.rootSeminorm_le_graphSeminorm (E.graphToDomain z))
  have hune : U.Nonempty := ⟨E.toGraph ⟨f', hf⟩, f, rfl, fun _ _ ↦ rfl⟩
  let d := sInf (S '' U)
  have hbelow : BddBelow (S '' U) := ⟨0, by rintro _ ⟨v, _, rfl⟩; exact apply_nonneg S v⟩
  have hcl : closure U ⊆ {w | d ≤ S w} :=
    closure_minimal (fun w hw ↦ csInf_le hbelow (mem_image_of_mem _ hw))
      (isClosed_le continuous_const hS)
  let r (k : ℕ) : ℝ := d + 1 / ((k : ℝ) + 1)
  let A (k : ℕ) : Set E.GraphDomain :=
    closure U ∩ (T ⁻¹' closedBall f' ε) ∩ S.closedBall 0 (r k)
  have hmono : Antitone A := by
    intro i j hij x hx
    refine ⟨hx.1, ?_⟩
    rw [S.closedBall_zero_eq]
    have hs : S x ≤ r j := by
      simpa only [S.closedBall_zero_eq, mem_ofPred_eq] using hx.2
    have hn : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := add_le_add_left (Nat.cast_le.mpr hij) _
    exact hs.trans (add_le_add_right (one_div_le_one_div_of_le (by positivity) hn) _)
  have hclose (k : ℕ) : IsClosed (A k) := by
    refine (isClosed_closure.inter (isClosed_closedBall.preimage T.continuous)).inter ?_
    rw [S.closedBall_zero_eq]
    exact isClosed_le hS continuous_const
  have hconv (k : ℕ) : Convex ℝ (A k) :=
    ((E.convex_boundaryCompetitors n f).closure.inter
      ((convex_closedBall _ _).linear_preimage T.toLinearMap)).inter (S.convex_closedBall 0 (r k))
  have hne (k : ℕ) : (A k).Nonempty := by
    have hr : d < r k := lt_add_of_pos_right _ (by positivity)
    obtain ⟨_, ⟨z, ⟨v, hz, hzf⟩, rfl⟩, hs⟩ := exists_lt_of_csInf_lt (hune.image S) hr
    have hv : continuousLp p v ∈ E.domain := hz.symm ▸ (E.graphToDomain z).property
    obtain ⟨g, hg, hgf, hnorm, henergy⟩ := E.exists_cellwise_clamp n f v hv hzf hε hosc
    let G : E.domain := ⟨continuousLp p g, hg⟩
    have hz' : (⟨continuousLp p v, hv⟩ : E.domain) = E.graphToDomain z := Subtype.ext hz
    refine ⟨E.toGraph G, ⟨subset_closure ⟨g, rfl, hgf⟩, ?_⟩, ?_⟩
    · change dist (G : CarpetLp p) f' ≤ ε
      rw [dist_eq_norm]
      rw [← show continuousLp p (g - f) = continuousLp p g - continuousLp p f
        from (continuousLpLinear p).map_sub g f]
      exact norm_carpetLp_le_of_ae_bound _ hε
        ((continuousLp_ae_eq p (g - f)).mono fun x hx ↦ by
          rw [hx]
          exact ((g - f).norm_coe_le_norm x).trans hnorm)
    · rw [S.closedBall_zero_eq]
      change E.rootSeminorm G ≤ r k
      rw [hz'] at henergy
      apply le_trans _ hs.le
      change E.rootSeminorm G ≤ E.rootSeminorm (E.graphToDomain z)
      rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr henergy)
        (inv_nonneg.mpr hp.le)
  have hbounded : ∀ x ∈ A 0, ‖x‖ ≤ ((r 0) ^ p + (‖f'‖ + ε) ^ p) ^ p⁻¹ := by
    intro z hz
    have hs : S z ≤ r 0 := by simpa only [S.closedBall_zero_eq, mem_ofPred_eq] using hz.2
    have hLp : ‖T z - f'‖ ≤ ε := by
      rw [← dist_eq_norm]
      exact hz.1.2
    have hnorm : ‖T z‖ ≤ ‖f'‖ + ε :=
      (norm_le_norm_sub_add _ _).trans (by linarith)
    exact E.graphSeminorm_le_of_le (E.graphToDomain z) hnorm hs
  obtain ⟨z, hz⟩ := exists_mem_antitone_closed_convex A hmono hclose hconv hne hbounded
  refine ⟨z, (hz 0).1.1, ?_, fun w hw ↦ ?_⟩
  · rw [← dist_eq_norm]
    exact (hz 0).1.2
  have ht : Tendsto r atTop (𝓝 d) := by
    have hconst : Tendsto (fun _ : ℕ ↦ d) atTop (𝓝 d) := tendsto_const_nhds
    simpa only [add_zero] using hconst.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hsz (k : ℕ) : S z ≤ r k := by
    simpa only [S.closedBall_zero_eq, mem_ofPred_eq] using (hz k).2
  have hmin := (le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hsz)).trans (hcl hw)
  have he := Real.rpow_le_rpow (apply_nonneg S z) hmin hp.le
  have hP (x : E.GraphDomain) : S x ^ p = (E.energy (E.graphToDomain x) : ℝ) := by
    change E.rootSeminorm (E.graphToDomain x) ^ p = _
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'
  rw [hP z, hP w] at he
  exact NNReal.coe_le_coe.mp he

end CarpetEnergy.SelfSimilarPEnergy
