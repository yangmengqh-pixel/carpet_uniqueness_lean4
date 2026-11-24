import EnergyBoundaryReplacement
import UniformConvexMidpoints

/-!
# Graph convergence of nested variational replacements

Dense boundary levels and the cellwise oscillation bound give ambient
convergence. The energy comparison at midpoints upgrades it to strong
convergence in the uniformly convex graph norm.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy

private theorem wordMap_append_singleton (w : List (Fin 8)) (i : Fin 8) (x : CarpetPoints) :
    wordMap (w ++ [i]) x = wordMap w (cellMap i x) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change cellMap j (wordMap (w ++ [i]) x) = cellMap j (wordMap w (cellMap i x))
    rw [ih]

theorem monotone_carpetCellBoundary : Monotone carpetCellBoundary := by
  apply monotone_nat_of_le_succ
  intro n z hz
  obtain ⟨w, x, hx, rfl⟩ := mem_iUnion.mp hz
  obtain ⟨u, y, rfl⟩ := exists_wordMap_range 1 x
  obtain ⟨j, a, haj⟩ := (mem_carpetOuterBoundary _).mp hx
  have hy : y ∈ carpetOuterBoundary :=
    (mem_carpetOuterBoundary y).mpr ⟨j, a, (wordMap_preimage_side u j a y haj).1⟩
  let i := u 0
  have hu : List.ofFn u = [i] := by rw [List.ofFn_succ]; rfl
  let v := List.ofFn w ++ [i]
  have hv : v.length = n + 1 := by simp [v]
  let U : Fin (n + 1) → Fin 8 := fun t ↦ v.get (Fin.cast hv.symm t)
  have he : List.ofFn U = v := by
    apply List.ext_get
    · exact List.length_ofFn.trans hv.symm
    · intro a ha ha'
      rw [List.get_ofFn]
      rfl
  refine mem_iUnion.mpr ⟨U, y, hy, ?_⟩
  rw [he, hu]
  exact wordMap_append_singleton _ _ _

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem antitone_boundaryCompetitors (f : C(CarpetPoints, ℝ)) :
    Antitone (fun n ↦ closure (E.boundaryCompetitors n f)) := by
  intro i j hij
  apply closure_mono
  rintro z ⟨u, hu, huf⟩
  exact ⟨u, hu, fun x hx ↦ huf x (monotone_carpetCellBoundary hij hx)⟩

/-- A continuous datum is the graph-norm limit of boundary minimizers on
a cofinal sequence of levels. -/
theorem exists_boundary_replacement_tendsto (f : C(CarpetPoints, ℝ))
    (hf : continuousLp p f ∈ E.domain) :
    ∃ (n : ℕ → ℕ) (z : ℕ → E.GraphDomain), Monotone n ∧ (∀ k, k ≤ n k) ∧
      (∀ k, z k ∈ closure (E.boundaryCompetitors (n k) f)) ∧
      (∀ k (w : E.GraphDomain), w ∈ closure (E.boundaryCompetitors (n k) f) →
        E.energy (E.graphToDomain (z k)) ≤ E.energy (E.graphToDomain w)) ∧
      Tendsto z atTop (𝓝 (E.toGraph ⟨continuousLp p f, hf⟩)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hω (k : ℕ) : ∃ N, ∀ m ≥ N, ∀ (w : Fin m → Fin 8) x y,
      |f (wordMap (List.ofFn w) x) - f (wordMap (List.ofFn w) y)| ≤ ε k := by
    obtain ⟨δ, hδ, hdist⟩ :=
      Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous)
        (ε k) (hε k)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_wordMap_radius.eventually_lt_const hδ)
    refine ⟨N, fun m hm w x y ↦ ?_⟩
    have h := wordMap_dist_le m w (mem_range_self x) (mem_range_self y)
    exact (show |f (wordMap (List.ofFn w) x) - f (wordMap (List.ofFn w) y)| < ε k from
      (Real.dist_eq _ _ ▸ hdist (h.trans_lt (hN m hm)))).le
  choose N hN using hω
  let n (k : ℕ) := k + (Finset.range (k + 1)).sup N
  have hmono : Monotone n := fun i j hij ↦
    add_le_add hij (Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hij)))
  have hn (k : ℕ) : k ≤ n k := Nat.le_add_right _ _
  have hnN (k : ℕ) : N k ≤ n k :=
    (Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans (Nat.le_add_left _ _)
  choose z hz hnorm hmin using fun k ↦
    E.exists_minimizer_boundaryCompetitors (n k) f hf (hε k).le (hN k (n k) (hnN k))
  refine ⟨n, z, hmono, hn, hz, hmin, ?_⟩
  let T := E.graphInclusion
  let f' := continuousLp p f
  let P (k : ℕ) := (E.energy (E.graphToDomain (z k)) : ℝ)
  have hPmono : Monotone P := by
    intro i j hij
    exact NNReal.coe_le_coe.mpr (hmin i _ (E.antitone_boundaryCompetitors f (hmono hij) (hz j)))
  have hPbound : BddAbove (range P) := by
    refine ⟨(E.energy ⟨f', hf⟩ : ℝ), ?_⟩
    rintro _ ⟨k, rfl⟩
    exact NNReal.coe_le_coe.mpr (hmin k _ (subset_closure ⟨f, rfl, fun _ _ ↦ rfl⟩))
  let A := ⨆ k, P k
  have hP : Tendsto P atTop (𝓝 A) := tendsto_atTop_ciSup hPmono hPbound
  have hL : Tendsto (fun k ↦ T (z k)) atTop (𝓝 f') := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεlim
      (fun _ ↦ norm_nonneg _) hnorm
  let a := (A + ‖f'‖ ^ p) ^ p⁻¹
  have hG (w : E.GraphDomain) :
      ‖w‖ = ((E.energy (E.graphToDomain w) : ℝ) + ‖T w‖ ^ p) ^ p⁻¹ := by
    change E.graphSeminorm (E.graphToDomain w) = _
    rw [E.graphSeminorm_apply, energyGraphNorm]
    rfl
  have hnormlim : Tendsto (fun k ↦ ‖z k‖) atTop (𝓝 a) := by
    simpa only [hG] using
      (hP.add (hL.norm.rpow_const (Or.inr hp.le))).rpow_const (Or.inr (inv_nonneg.mpr hp.le))
  have hc : CauchySeq z := cauchySeq_of_norm_tendsto_of_midpoints z a hnormlim (by
    intro i j hi hj
    have hAt (k : ℕ → ℕ) (hk : ∀ n, n ≤ k n) : Tendsto k atTop atTop :=
      tendsto_atTop_mono' atTop (Eventually.of_forall hk) tendsto_id
    let m (k : ℕ) := min (i k) (j k)
    have hm : Tendsto m atTop atTop := hAt m (fun k ↦ le_min (hi k) (hj k))
    let y (k : ℕ) := (1 / 2 : ℝ) • (z (i k) + z (j k))
    have hB (k : ℕ) : P (m k) ≤ (E.energy (E.graphToDomain (y k)) : ℝ) := by
      have hC := (E.convex_boundaryCompetitors (n (m k)) f).closure
      have h₁ := E.antitone_boundaryCompetitors f (hmono (min_le_left (i k) (j k))) (hz (i k))
      have h₂ := E.antitone_boundaryCompetitors f (hmono (min_le_right (i k) (j k))) (hz (j k))
      have hh := hC.midpoint_mem h₁ h₂
      rw [midpoint_eq_smul_add, invOf_eq_inv, ← one_div] at hh
      exact NNReal.coe_le_coe.mpr (hmin (m k) _ hh)
    have hY : Tendsto (fun k ↦ T (y k)) atTop (𝓝 f') := by
      have ht : Tendsto (fun k ↦ (1 / 2 : ℝ) • (T (z (i k)) + T (z (j k)))) atTop
          (𝓝 ((1 / 2 : ℝ) • (f' + f'))) :=
        tendsto_const_nhds.smul ((hL.comp (hAt i hi)).add (hL.comp (hAt j hj)))
      rw [← two_smul ℝ f', smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at ht
      simpa only [y, map_smul, map_add] using ht
    have hlow : Tendsto (fun k ↦ (P (m k) + ‖T (y k)‖ ^ p) ^ p⁻¹) atTop (𝓝 a) :=
      ((hP.comp hm).add (hY.norm.rpow_const (Or.inr hp.le))).rpow_const
        (Or.inr (inv_nonneg.mpr hp.le))
    have hupp : Tendsto (fun k ↦ (‖z (i k)‖ + ‖z (j k)‖) / 2) atTop (𝓝 a) := by
      have h := ((hnormlim.comp (hAt i hi)).add (hnormlim.comp (hAt j hj))).div_const 2
      rw [show (a + a) / 2 = a by ring] at h
      simpa only [Function.comp_apply] using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
    · intro k
      change (P (m k) + ‖T (y k)‖ ^ p) ^ p⁻¹ ≤ ‖y k‖
      rw [hG]
      exact Real.rpow_le_rpow
        (add_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
        (add_le_add_left (hB k) _) (inv_nonneg.mpr hp.le)
    · intro k
      change ‖(1 / 2 : ℝ) • (z (i k) + z (j k))‖ ≤ _
      rw [norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      simpa only [one_div, div_eq_inv_mul, mul_one] using
        (div_le_div_of_nonneg_right (norm_add_le (z (i k)) (z (j k))) (by norm_num : 0 ≤ (2 : ℝ))))
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  have he := tendsto_nhds_unique ((T.continuous.tendsto w).comp hw) hL
  have hw' : w = E.toGraph ⟨f', hf⟩ := Subtype.ext he
  rwa [hw'] at hw

end SelfSimilarPEnergy
end CarpetEnergy
