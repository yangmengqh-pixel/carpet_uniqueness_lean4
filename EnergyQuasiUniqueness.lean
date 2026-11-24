import EnergyComponentInterpolation
import CarpetCapacity

/-!
# Quasi-uniqueness of self-similar carpet energies

The interpolants of the cell means of a boundary profile have a fixed
positive energy lower bound. The discrete energy bounds therefore identify
the scaling factors of two energies. Interpolating arbitrary cell means
then gives the common domain and two-sided energy comparison.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent SelfSimilarComponent.CornerProfile

variable {p : ℝ} (E : SelfSimilarPEnergy p)

noncomputable def zeroComponent : E.SelfSimilarComponent where
  mass := 0
  rootSeminorm := 0
  rootSeminorm_apply f := by
    change 0 = (0 : ℝ) ^ p⁻¹
    rw [Real.zero_rpow (inv_ne_zero (zero_lt_one.trans E.one_lt_p).ne')]
  mass_le_energy _ := zero_le
  selfSimilar _ := by simp
  symmetry _ _ := rfl
  contraction _ _ _ _ := by simp

theorem exists_zeroCornerProfile : Nonempty (E.zeroComponent).CornerProfile := by
  obtain ⟨u⟩ := E.nonempty_leftRightProfile
  exact (E.zeroComponent).exists_cornerProfile_of_sides ⟨u.mem_domain, rfl⟩ u.left u.right

private theorem wordMap_preimage_coord_side {n : ℕ} (w : Fin n → Fin 8) (a : Fin 2)
    (x : CarpetPoints) (hx : (wordMap (List.ofFn w) x : Plane) 0 = a.val) :
    (x : Plane) 0 = a.val ∧ (gridCoordinate (List.ofFn w) 0 : ℝ) =
      ((3 : ℝ) ^ n - 1) * a.val := by
  have h := wordMap_scaled_coord (List.ofFn w) x 0
  rw [List.length_ofFn, hx] at h
  have hg := gridCoordinate_lt (List.ofFn w) 0
  rw [List.length_ofFn] at hg
  have hg' : (gridCoordinate (List.ofFn w) 0 : ℝ) + 1 ≤ (3 : ℝ) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt hg
  have hg₀ : 0 ≤ (gridCoordinate (List.ofFn w) 0 : ℝ) := Nat.cast_nonneg _
  have hb := carpet_coord_mem_Icc x 0
  fin_cases a
  · change (3 : ℝ) ^ n * 0 = _ at h
    change (x : Plane) 0 = 0 ∧ (gridCoordinate (List.ofFn w) 0 : ℝ) = (3 ^ n - 1) * 0
    exact ⟨by linarith [hb.1], by linarith [hb.1]⟩
  · change (3 : ℝ) ^ n * 1 = _ at h
    change (x : Plane) 0 = 1 ∧ (gridCoordinate (List.ofFn w) 0 : ℝ) = (3 ^ n - 1) * 1
    exact ⟨by linarith [hb.2], by linarith [hb.2]⟩

private theorem side_distance_of_wordMap (n : ℕ) (w : Fin (n + 1) → Fin 8)
    (a : Fin 2) {z : CarpetPoints} (hz : z ∈ range (wordMap (List.ofFn w)))
    (hza : (z : Plane) 0 = a.val) (x : CarpetPoints) :
    |(wordMap (List.ofFn w) x : Plane) 0 - (a.val : ℝ)| ≤ 1 / 3 := by
  obtain ⟨y, rfl⟩ := hz
  obtain ⟨_, hg⟩ := wordMap_preimage_coord_side w a y hza
  have h := wordMap_scaled_coord (List.ofFn w) x 0
  rw [List.length_ofFn, hg] at h
  have ht : (3 : ℝ) ≤ (3 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    have h' : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    linarith
  have hb := carpet_coord_mem_Icc x 0
  have hw := carpet_coord_mem_Icc (wordMap (List.ofFn w) x) 0
  fin_cases a
  · change (3 : ℝ) ^ (n + 1) * (wordMap (List.ofFn w) x : Plane) 0 =
      ((3 : ℝ) ^ (n + 1) - 1) * 0 + (x : Plane) 0 at h
    change |(wordMap (List.ofFn w) x : Plane) 0 - 0| ≤ _
    rw [sub_zero, abs_of_nonneg hw.1]
    have hle := mul_le_mul_of_nonneg_right ht hw.1
    linarith [hb.2]
  · change (3 : ℝ) ^ (n + 1) * (wordMap (List.ofFn w) x : Plane) 0 =
      ((3 : ℝ) ^ (n + 1) - 1) * 1 + (x : Plane) 0 at h
    change |(wordMap (List.ofFn w) x : Plane) 0 - 1| ≤ _
    rw [abs_of_nonpos (sub_nonpos.mpr hw.2)]
    have hle := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hw.2)
    linarith [hb.1]

theorem splice_mean_eq_side (D : SelfSimilarPEnergy p) (u : D.LeftRightProfile)
    (n : ℕ) (w : Fin (n + 1) → Fin 8) (a : Fin 2) {z : CarpetPoints}
    (hz : z ∈ range (wordMap (List.ofFn w))) (hza : (z : Plane) 0 = a.val) :
    continuousWordMean (D.spliceProfile u).toContinuousMap (List.ofFn w) = a.val := by
  have h (x : CarpetPoints) :=
    side_distance_of_wordMap n w a hz hza x
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply abs_wordMean_sub_le
  intro x
  have hx := h x
  rw [abs_le] at hx
  have he : (D.spliceProfile u).toContinuousMap (wordMap (List.ofFn w) x) = a.val := by
    fin_cases a
    · apply D.spliceProfile_eq_zero
      have hright : (wordMap (List.ofFn w) x : Plane) 0 - 0 ≤ 1 / 3 := hx.2
      simpa only [sub_zero] using hright
    · apply D.spliceProfile_eq_one
      have hleft : -(1 / 3 : ℝ) ≤ (wordMap (List.ofFn w) x : Plane) 0 - 1 := hx.1
      linarith
  rw [he, sub_self, abs_zero]

private theorem interpolate_splice_side {D : SelfSimilarPEnergy p} (u : D.LeftRightProfile)
    {Q : E.SelfSimilarComponent} (P : Q.CornerProfile) (n : ℕ)
    (g : C(CarpetPoints, ℝ))
    (hm : ∀ (w : Fin (n + 1) → Fin 8) x, g (wordMap (List.ofFn w) x) =
      P.interpolate (cornerData (cornerAverage (n + 1)
        (fun v ↦ continuousWordMean (D.spliceProfile u).toContinuousMap (List.ofFn v)))
        (List.ofFn w)) x)
    (a : Fin 2) (x : CarpetPoints) (hx : (x : Plane) 0 = a.val) :
    g x = a.val := by
  obtain ⟨w, y, rfl⟩ := exists_wordMap_range (n + 1) x
  obtain ⟨hy, _⟩ := wordMap_preimage_coord_side w a y hx
  rw [hm, P.interpolate_vertical_side _ a y hy]
  have hcorner (j : Fin 2) : cornerData (cornerAverage (n + 1)
      (fun v ↦ continuousWordMean (D.spliceProfile u).toContinuousMap (List.ofFn v)))
      (List.ofFn w) a j = (a.val : ℝ) := by
    let z := wordMap (List.ofFn w) (cornerPoint a j)
    have hz : (z : Plane) 0 = a.val := by
      have h := wordMap_scaled_coord (List.ofFn w) (cornerPoint a j) 0
      rw [cornerPoint_first, List.length_ofFn, (wordMap_preimage_coord_side w a y hx).2] at h
      have hp : (3 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      exact mul_left_cancel₀ hp (h.trans (by ring))
    change cornerAverage (n + 1) _ z = _
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    apply abs_cornerAverage_sub_le
    intro v hv
    rw [splice_mean_eq_side D u n v a (mem_incidentWords.mp hv) hz, sub_self, abs_zero]
  rw [hcorner 0, hcorner 1]
  ring

private theorem scalingFactor_ge (D : SelfSimilarPEnergy p) :
    D.scalingFactor ≤ E.scalingFactor := by
  by_contra! hlt
  obtain ⟨P⟩ := E.exists_zeroCornerProfile
  obtain ⟨u⟩ := D.nonempty_leftRightProfile
  obtain ⟨C, hC, hinterp⟩ := P.exists_interpolate_cellValues
  obtain ⟨B, _, hgrid⟩ := D.exists_gridMean_energy_le
  let c := E.leftRightCapacity
  have hc : 0 < c := E.leftRightCapacity_pos
  let f := (D.spliceProfile u).toContinuousMap
  let hf := (D.spliceProfile u).mem_domain
  let e := (D.energy ⟨continuousLp p f, hf⟩ : ℝ)
  let r := E.scalingFactor / D.scalingFactor
  have hE := E.isScalingFactor_scalingFactor.1
  have hD := D.isScalingFactor_scalingFactor.1
  have hl : Tendsto (fun n : ℕ ↦ C * (r ^ (n + 1) * (B * e))) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hE.le hD.le)
      ((div_lt_one hD).mpr hlt)
    simpa only [pow_succ, mul_zero, zero_mul] using ((h.mul_const r).mul_const (B * e)).const_mul C
  have hbound (n : ℕ) : c ≤ C * (r ^ (n + 1) * (B * e)) := by
    let m (w : Fin (n + 1) → Fin 8) := continuousWordMean f (List.ofFn w)
    obtain ⟨g, hg, _, heq, he⟩ := hinterp (n + 1) m
    let S := ∑ w : Fin (n + 1) → Fin 8, ∑ v ∈ gridNeighbors w, |m w - m v| ^ p
    have hside (a : Fin 2) (x : CarpetPoints) (hx : (x : Plane) 0 = a.val) : g x = a.val :=
      E.interpolate_splice_side u P n g heq a x hx
    have hbound₀ (x : CarpetPoints) : 0 ≤ g x ∧ g x ≤ 1 := by
      obtain ⟨w, y, rfl⟩ := exists_wordMap_range (n + 1) x
      rw [heq]
      have hh := P.abs_interpolate_sub_le (cornerData (cornerAverage (n + 1) m) (List.ofFn w)) y
        (c := 1 / 2) (R := 1 / 2) (fun i j ↦ by
          apply abs_cornerAverage_sub_le
          intro v _
          apply abs_wordMean_sub_le
          intro z
          have hz := (D.spliceProfile u).bounds (wordMap (List.ofFn v) z)
          dsimp [f]
          exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩)
      rw [abs_le] at hh
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    let W : E.LeftRightProfile := ⟨g, hg, hside 0, hside 1, hbound₀⟩
    have hdisc : D.scalingFactor ^ (n + 1) * S ≤ B * e := hgrid (n + 1) f hf
    calc
      c ≤ (E.energy (W.toDomain E) : ℝ) := E.leftRightCapacity_le_energy W
      _ ≤ C * (E.scalingFactor ^ (n + 1) * S) := he
      _ = C * (r ^ (n + 1) * (D.scalingFactor ^ (n + 1) * S)) := by
        dsimp only [r]
        rw [div_pow]
        congr 1
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdisc (pow_nonneg (div_nonneg hE.le hD.le) _)) hC
  exact hc.not_ge (le_of_tendsto_of_tendsto tendsto_const_nhds hl (Eventually.of_forall hbound))

/-- Any two self-similar p-energies at the same exponent have the same
renormalization factor. -/
theorem scalingFactor_eq (D : SelfSimilarPEnergy p) :
    E.scalingFactor = D.scalingFactor :=
  le_antisymm (D.scalingFactor_ge E) (E.scalingFactor_ge D)

private theorem exists_domain_rootBound_continuous (D : SelfSimilarPEnergy p) :
    ∃ C ≥ (0 : ℝ), ∀ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ D.domain),
      ∃ v : E.domain, (v : CarpetLp p) = continuousLp p f ∧
        E.rootSeminorm v ≤ C * D.rootSeminorm ⟨continuousLp p f, hf⟩ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨P⟩ := E.exists_zeroCornerProfile
  obtain ⟨A, hA, hinterp⟩ := P.exists_interpolate_cellValues
  obtain ⟨B, hB, hgrid⟩ := D.exists_gridMean_energy_le
  let C := (A * B) ^ p⁻¹
  have hC : 0 ≤ C := Real.rpow_nonneg (mul_nonneg hA hB.le) _
  refine ⟨C, hC, fun f hf ↦ ?_⟩
  choose g hg _ hG he using fun n ↦ hinterp n (fun w ↦ continuousWordMean f (List.ofFn w))
  let u (n : ℕ) : E.domain := ⟨continuousLp p (g n), hg n⟩
  let R := C * D.rootSeminorm ⟨continuousLp p f, hf⟩
  have hroot (n : ℕ) : E.rootSeminorm (u n) ≤ R := by
    have he' := he n
    rw [E.scalingFactor_eq D] at he'
    have hh := le_trans he' (mul_le_mul_of_nonneg_left (hgrid n f hf) hA)
    rw [E.rootSeminorm_apply, show R = (A * (B * (D.energy ⟨continuousLp p f, hf⟩ : ℝ))) ^ p⁻¹ by
      let z : D.domain := ⟨continuousLp p f, hf⟩
      change C * D.rootSeminorm z = (A * (B * (D.energy z : ℝ))) ^ p⁻¹
      rw [D.rootSeminorm_apply, ← mul_assoc]
      exact (Real.mul_rpow (mul_nonneg hA hB.le) (NNReal.coe_nonneg (D.energy z))).symm]
    exact Real.rpow_le_rpow (E.energy _).property hh (inv_nonneg.mpr hp.le)
  obtain ⟨hL, hlim⟩ := P.cellMeanInterpolation_tendsto f g hG
  exact E.exists_domain_of_tendsto_of_seminorm_le E.rootSeminorm E.rootSeminorm_le_graphSeminorm
    u (continuousLp p f) (fun n ↦ E.graphSeminorm_le_of_le (u n) (hL n) (hroot n))
    (fun _ h ↦ Eventually.of_forall fun n ↦ (hroot n).trans h.le) hlim

private theorem exists_domain_rootBound (D : SelfSimilarPEnergy p) :
    ∃ C ≥ (0 : ℝ), ∀ f : D.domain, ∃ v : E.domain, (v : CarpetLp p) = f ∧
      E.rootSeminorm v ≤ C * D.rootSeminorm f := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  obtain ⟨C, hC, hc⟩ := E.exists_domain_rootBound_continuous D
  refine ⟨C, hC, fun f ↦ ?_⟩
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε₁ (n : ℕ) : ε n ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose u hu happrox using fun n ↦ D.regular_graph f (ε n) (hε n)
  let g (n : ℕ) : D.domain := ⟨continuousLp p (u n), hu n⟩
  choose v hv hroot using fun n ↦ hc (u n) (hu n)
  have hnorm (n : ℕ) : ‖(v n : CarpetLp p) - (f : CarpetLp p)‖ ≤ ε n := by
    rw [hv]
    exact (D.norm_coe_le_graphSeminorm (g n - f)).trans (happrox n).le
  have ht : Tendsto (fun n ↦ (v n : CarpetLp p)) atTop (𝓝 (f : CarpetLp p)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεlim
        (fun _ ↦ norm_nonneg _) hnorm)
  have hE (n : ℕ) : E.rootSeminorm (v n) ≤ C * (D.rootSeminorm f + ε n) := by
    apply (hroot n).trans (mul_le_mul_of_nonneg_left ?_ hC)
    change D.rootSeminorm (g n) ≤ _
    calc
      _ = D.rootSeminorm ((g n - f) + f) := by rw [sub_add_cancel]
      _ ≤ D.rootSeminorm (g n - f) + D.rootSeminorm f := map_add_le_add _ _ _
      _ ≤ _ := by
        rw [add_comm (D.rootSeminorm f)]
        exact add_le_add_left ((D.rootSeminorm_le_graphSeminorm _).trans (happrox n).le) _
  have hL (n : ℕ) : ‖(v n : CarpetLp p)‖ ≤ ‖(f : CarpetLp p)‖ + 1 := by
    exact (norm_le_norm_sub_add _ _).trans (by linarith [hnorm n, hε₁ n])
  have hR (n : ℕ) : E.rootSeminorm (v n) ≤ C * (D.rootSeminorm f + 1) :=
    (hE n).trans (mul_le_mul_of_nonneg_left (add_le_add_right (hε₁ n) _) hC)
  have hl : Tendsto (fun n ↦ C * (D.rootSeminorm f + ε n)) atTop (𝓝 (C * D.rootSeminorm f)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hεlim).const_mul C
  exact E.exists_domain_of_tendsto_of_seminorm_le E.rootSeminorm E.rootSeminorm_le_graphSeminorm
    v f (fun n ↦ E.graphSeminorm_le_of_le (v n) (hL n) (hR n))
    (fun r hr ↦ (hl.eventually_lt_const hr).mono fun n hn ↦ (hE n).trans hn.le) ht

/-- Every self-similar p-energy is bounded by a constant times any other on
the same carpet, and their domains coincide by applying this in both directions. -/
theorem exists_energy_le (D : SelfSimilarPEnergy p) :
    ∃ (h : D.domain ≤ E.domain) (C : ℝ≥0), 0 < C ∧
      ∀ f : D.domain, E.energy (Submodule.inclusion h f) ≤ C * D.energy f := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨A, hA, h⟩ := E.exists_domain_rootBound D
  have hdom : D.domain ≤ E.domain := fun f hf ↦ by
    obtain ⟨g, hg, _⟩ := h ⟨f, hf⟩
    change (g : CarpetLp p) = f at hg
    exact hg ▸ g.property
  let C : ℝ≥0 := ⟨A ^ p + 1, add_nonneg (Real.rpow_nonneg hA _) zero_le_one⟩
  refine ⟨hdom, C, ?_, fun f ↦ ?_⟩
  · exact_mod_cast (show (0 : ℝ) < A ^ p + 1 from by positivity)
  obtain ⟨g, hg, hroot⟩ := h f
  have hg' : g = Submodule.inclusion hdom f := Subtype.ext hg
  rw [← hg']
  have he := Real.rpow_le_rpow (apply_nonneg E.rootSeminorm g) hroot hp.le
  have hpow (U : SelfSimilarPEnergy p) (z : U.domain) :
      U.rootSeminorm z ^ p = (U.energy z : ℝ) := by
    rw [U.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne'
  rw [Real.mul_rpow hA (apply_nonneg _ _), hpow E g, hpow D f] at he
  apply NNReal.coe_le_coe.mp
  change (E.energy g : ℝ) ≤ (A ^ p + 1) * (D.energy f : ℝ)
  exact he.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (D.energy f).property)

/-- Quasi-uniqueness for every pair satisfying Definition 2.1. -/
theorem domain_eq (D : SelfSimilarPEnergy p) : E.domain = D.domain := by
  obtain ⟨hDE, _, _, _⟩ := E.exists_energy_le D
  obtain ⟨hED, _, _, _⟩ := D.exists_energy_le E
  exact le_antisymm hED hDE

end CarpetEnergy.SelfSimilarPEnergy
