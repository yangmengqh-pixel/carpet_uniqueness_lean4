import EnergySpectralGap
import CarpetGrid

/-!
# Mean differences across a common cell side

Two profiles that agree at their common side can be copied and reflected
onto the first-level cells of the carpet. The spectral gap on that glued
function bounds the difference of the two means by their two energies.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

/-- Reflection in the vertical middle line of the square. -/
def horizontalFlip : SquareSymmetry := (false, fun j ↦ j == 0)

theorem carpetSymmetry_horizontalFlip_first (x : CarpetPoints) :
    (carpetSymmetry horizontalFlip x : Plane) 0 = 1 - (x : Plane) 0 := rfl

theorem carpetSymmetry_horizontalFlip_second (x : CarpetPoints) :
    (carpetSymmetry horizontalFlip x : Plane) 1 = (x : Plane) 1 := rfl

private theorem cellFoldingMap_one_eq_horizontalFlip_zero (x : CarpetPoints) :
    cellFoldingMap 1 x = carpetSymmetry horizontalFlip (cellFoldingMap 0 x) := by
  apply Subtype.ext
  ext j
  fin_cases j <;> rfl

private theorem cellFoldingMap_zero_on_seam (x : CarpetPoints) (hx : (x : Plane) 0 = 1 / 3) :
    (cellFoldingMap 0 x : Plane) 0 = 1 := by
  change foldCoordinate ((x : Plane) 0) = 1
  rw [hx]
  norm_num [foldCoordinate]

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private noncomputable def continuousCell (i : Fin 8) : C(CarpetPoints, CarpetPoints) :=
  ⟨cellMap i, continuous_cellMap i⟩

private noncomputable def sideGlue (u v : C(CarpetPoints, ℝ)) (x : CarpetPoints) : ℝ :=
  if (x : Plane) 0 ≤ 1 / 3 then u (cellFoldingMap 0 x) else v (cellFoldingMap 1 x)

private theorem sideGlue_eq_right (u v : C(CarpetPoints, ℝ))
    (h : ∀ x : CarpetPoints, (x : Plane) 0 = 1 → u x = v (carpetSymmetry horizontalFlip x))
    (x : CarpetPoints) (hx : 1 / 3 ≤ (x : Plane) 0) :
    sideGlue u v x = v (cellFoldingMap 1 x) := by
  rcases lt_or_eq_of_le hx with hl | he
  · exact ite_eq_right hl.not_ge
  · rw [sideGlue, ite_eq_left he.ge, cellFoldingMap_one_eq_horizontalFlip_zero]
    exact h _ (cellFoldingMap_zero_on_seam x he.symm)

private theorem continuous_sideGlue (u v : C(CarpetPoints, ℝ))
    (h : ∀ x : CarpetPoints, (x : Plane) 0 = 1 → u x = v (carpetSymmetry horizontalFlip x)) :
    Continuous (sideGlue u v) := by
  let c (x : CarpetPoints) := (x : Plane) 0
  have hc : Continuous c :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_subtypeVal
  let L := c ⁻¹' Iic (1 / 3)
  let R := c ⁻¹' Ici (1 / 3)
  have hL : IsClosed L := isClosed_Iic.preimage hc
  have hR : IsClosed R := isClosed_Ici.preimage hc
  have htL : ContinuousOn (sideGlue u v) L := (u.continuous.comp (cellFoldingMap 0).continuous).continuousOn.congr
    (fun _ hx ↦ ite_eq_left hx)
  have htR : ContinuousOn (sideGlue u v) R := (v.continuous.comp (cellFoldingMap 1).continuous).continuousOn.congr
    (fun x hx ↦ sideGlue_eq_right u v h x hx)
  have hcov : L ∪ R = univ := eq_univ_of_forall fun x ↦ le_total (c x) (1 / 3)
  have h := htL.union_of_isClosed htR hL hR
  rwa [hcov, continuousOn_univ] at h

private theorem sideGlue_comp_cell (u v : C(CarpetPoints, ℝ))
    (h : ∀ x : CarpetPoints, (x : Plane) 0 = 1 → u x = v (carpetSymmetry horizontalFlip x))
    (i : Fin 8) (y : CarpetPoints) :
    sideGlue u v (cellMap i y) =
      if cellDigit i 0 = 0 then u (cellFoldingMap 0 (cellMap i y))
      else v (cellFoldingMap 1 (cellMap i y)) := by
  have hcoord : (cellMap i y : Plane) 0 = ((y : Plane) 0 + (cellDigit i 0 : ℕ)) / 3 := by
    change cellSimilarity i y 0 = _
    rw [cellSimilarity_coord, ← cellDigit_cast]
  by_cases hi : cellDigit i 0 = 0
  · rw [hi, ite_eq_left rfl]
    apply ite_eq_left
    rw [hcoord, hi, Fin.val_zero, Nat.cast_zero, add_zero]
    linarith [(carpet_coord_mem_Icc y 0).2]
  · rw [ite_eq_right hi]
    apply sideGlue_eq_right _ _ h
    rw [hcoord]
    have hi' : (1 : ℝ) ≤ (cellDigit i 0 : ℕ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun he ↦ hi (Fin.ext he)))
    linarith [(carpet_coord_mem_Icc y 0).1]

theorem exists_folded_cell_energy (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) (i j : Fin 8) :
    ∃ h : continuousLp p ((u.comp (cellFoldingMap i)).comp (continuousCell j)) ∈ E.domain,
      E.energy ⟨continuousLp p ((u.comp (cellFoldingMap i)).comp (continuousCell j)), h⟩ =
        E.energy ⟨continuousLp p u, hu⟩ := by
  obtain ⟨s, hs⟩ := exists_cellFoldingMap_comp_cellMap i j
  let u' : E.domain := ⟨continuousLp p u, hu⟩
  let f := E.pullbackSymmetry s u'
  let v := (u.comp (cellFoldingMap i)).comp (continuousCell j)
  have hLp : continuousLp p v = (f : CarpetLp p) := by
    apply Lp.ext
    refine (continuousLp_ae_eq p v).trans ?_
    have hm := (measurePreserving_carpetSymmetry s).quasiMeasurePreserving.ae_eq_comp
      (continuousLp_ae_eq p u)
    filter_upwards [hm, symmetryPullback_isLpPullback s (continuousLp p u)] with x hm hx
    change (f : CarpetLp p) x = continuousLp p u (carpetSymmetry s x) at hx
    change continuousLp p u (carpetSymmetry s x) = u (carpetSymmetry s x) at hm
    rw [hx, hm]
    exact congrArg u (congrFun hs x)
  have hv : continuousLp p v ∈ E.domain := hLp.symm ▸ f.property
  exact ⟨hv, (congrArg E.energy (Subtype.ext hLp)).trans (E.energy_pullbackSymmetry s u')⟩

private theorem exists_sideGlue_energy (u v : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) (hv : continuousLp p v ∈ E.domain)
    (h : ∀ x : CarpetPoints, (x : Plane) 0 = 1 → u x = v (carpetSymmetry horizontalFlip x)) :
    ∃ (g : C(CarpetPoints, ℝ)) (hg : continuousLp p g ∈ E.domain),
      (∀ x, g (cellMap 0 x) = u x) ∧ (∀ x, g (cellMap 1 x) = v x) ∧
      (E.energy ⟨continuousLp p g, hg⟩ : ℝ) ≤
        (8 * E.scalingFactor) * ((E.energy ⟨continuousLp p u, hu⟩ : ℝ) +
          (E.energy ⟨continuousLp p v, hv⟩ : ℝ)) := by
  let g : C(CarpetPoints, ℝ) := ⟨sideGlue u v, continuous_sideGlue u v h⟩
  let eu := E.energy ⟨continuousLp p u, hu⟩
  let ev := E.energy ⟨continuousLp p v, hv⟩
  have H (i : Fin 8) : ∃ h : continuousLp p (g.comp (continuousCell i)) ∈ E.domain,
      (E.energy ⟨continuousLp p (g.comp (continuousCell i)), h⟩ : ℝ) ≤ (eu : ℝ) + (ev : ℝ) := by
    by_cases hi : cellDigit i 0 = 0
    · have he : g.comp (continuousCell i) = (u.comp (cellFoldingMap 0)).comp (continuousCell i) := by
        ext x
        exact (sideGlue_comp_cell u v h i x).trans (ite_eq_left hi)
      rw [he]
      obtain ⟨hm, hE⟩ := E.exists_folded_cell_energy u hu 0 i
      exact ⟨hm, by rw [hE]; exact le_add_of_nonneg_right (NNReal.coe_nonneg _)⟩
    · have he : g.comp (continuousCell i) = (v.comp (cellFoldingMap 1)).comp (continuousCell i) := by
        ext x
        exact (sideGlue_comp_cell u v h i x).trans (ite_eq_right hi)
      rw [he]
      obtain ⟨hm, hE⟩ := E.exists_folded_cell_energy v hv 1 i
      exact ⟨hm, by rw [hE]; exact le_add_of_nonneg_left (NNReal.coe_nonneg _)⟩
  choose hdom hE using H
  have hg : continuousLp p g ∈ E.domain := (E.continuous_gluing g).2 hdom
  let f : E.domain := ⟨continuousLp p g, hg⟩
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro x
    change sideGlue u v (cellMap 0 x) = u x
    rw [sideGlue_comp_cell u v h 0 x, ite_eq_left (by decide), cellFoldingMap_leftInverse]
  · intro x
    change sideGlue u v (cellMap 1 x) = v x
    rw [sideGlue_comp_cell u v h 1 x, ite_eq_right (by decide), cellFoldingMap_leftInverse]
  · have hle (i : Fin 8) : (E.energy (E.pullback i f) : ℝ) ≤ (eu : ℝ) + (ev : ℝ) :=
      (show E.pullback i f = ⟨_, hdom i⟩ from Subtype.ext (cellPullback_continuousLp p i g)) ▸ hE i
    have hρ := E.isScalingFactor_scalingFactor
    rw [hρ.2]
    calc
      _ ≤ E.scalingFactor * ∑ _ : Fin 8, ((eu : ℝ) + (ev : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hle i) hρ.1.le
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        ring

private theorem abs_cell_mean_sub_le_center [Fact (1 ≤ ENNReal.ofReal p)]
    (g : C(CarpetPoints, ℝ)) (i : Fin 8) :
    |(∫ x, g (cellMap i x) ∂carpetMeasure) - ∫ x, g x ∂carpetMeasure| ≤
      8 * ‖centerLp p (continuousLp p g)‖ := by
  let c := ∫ x, g x ∂carpetMeasure
  let f := continuousLp p g
  let A := range (cellMap i)
  have he : (centerLp p f : CarpetPoints → ℝ) =ᵐ[carpetMeasure] (fun x ↦ g x - c) := by
    rw [centerLp_apply, integral_congr_ae (continuousLp_ae_eq p g)]
    filter_upwards [Lp.coeFn_sub f (constantLp p c), continuousLp_ae_eq p g,
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c] with x hsub hg hconst
    change (constantLp p c) x = c at hconst
    rw [hsub, Pi.sub_apply, hg, hconst]
  have h := norm_setIntegral_le A (centerLp p f)
  rw [integral_congr_ae (ae_restrict_of_ae he)] at h
  change ‖∫ x in range (cellMap i), g x - c ∂carpetMeasure‖ ≤ _ at h
  have hcont : Continuous (fun x ↦ g (cellMap i x)) := g.continuous.comp (continuous_cellMap i)
  have hint : Integrable (fun x ↦ g (cellMap i x)) carpetMeasure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [carpetMeasure_restrict_cellMap i, integral_smul_measure,
    (measurableEmbedding_cellMap i).integral_map, integral_sub hint (integrable_const _)] at h
  have hconst : (∫ _ : CarpetPoints, c ∂carpetMeasure) = c := by simp [Measure.real]
  rw [hconst, smul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h
  linarith

/-- The mean difference of profiles agreeing along a common side is
bounded by their energies, with a constant independent of the profiles. -/
theorem exists_mean_gap_of_common_horizontal_side :
    ∃ C > (0 : ℝ), ∀ (u v : C(CarpetPoints, ℝ))
      (hu : continuousLp p u ∈ E.domain) (hv : continuousLp p v ∈ E.domain),
      (∀ x : CarpetPoints, (x : Plane) 0 = 1 → u x = v (carpetSymmetry horizontalFlip x)) →
      |(∫ x, u x ∂carpetMeasure) - ∫ x, v x ∂carpetMeasure| ^ p ≤
        C * ((E.energy ⟨continuousLp p u, hu⟩ : ℝ) + (E.energy ⟨continuousLp p v, hv⟩ : ℝ)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨C, hC, hgap⟩ := E.exists_spectral_gap
  have hρ := E.isScalingFactor_scalingFactor.1
  refine ⟨(16 : ℝ) ^ p * C * (8 * E.scalingFactor), by positivity, ?_⟩
  intro u v hu hv hside
  obtain ⟨g, hg, hgu, hgv, hbound⟩ := E.exists_sideGlue_energy u v hu hv hside
  let c := ∫ x, g x ∂carpetMeasure
  let f := continuousLp p g
  have hmu := abs_cell_mean_sub_le_center (p := p) g 0
  have hmv := abs_cell_mean_sub_le_center (p := p) g 1
  simp_rw [hgu] at hmu
  simp_rw [hgv] at hmv
  have habs : |(∫ x, u x ∂carpetMeasure) - (∫ x, v x ∂carpetMeasure)| ≤ 16 * ‖centerLp p f‖ := by
    have hg' : |(∫ x, u x ∂carpetMeasure) - (∫ x, v x ∂carpetMeasure)| ≤
         |(∫ x, u x ∂carpetMeasure) - c| + |(∫ x, v x ∂carpetMeasure) - c| := by
      calc
        _ = |((∫ x, u x ∂carpetMeasure) - c) + (c - ∫ x, v x ∂carpetMeasure)| := by rw [sub_add_sub_cancel]
        _ ≤ _ := by rw [abs_sub_comm (∫ x, v x ∂carpetMeasure) c]; exact abs_add_le _ _
    exact hg'.trans (by change _ ≤ 16 * ‖centerLp p (continuousLp p g)‖; linarith)
  have hpw : ‖centerLp p f‖ ^ p ≤ C * (E.energy ⟨continuousLp p g, hg⟩ : ℝ) := by
    rw [centerLp_apply]
    exact hgap ⟨_, hg⟩
  calc
    _ ≤ (16 * ‖centerLp p f‖) ^ p := Real.rpow_le_rpow (abs_nonneg _) habs hp.le
    _ = 16 ^ p * ‖centerLp p f‖ ^ p := Real.mul_rpow (by norm_num) (norm_nonneg _)
    _ ≤ 16 ^ p * (C * (E.energy ⟨continuousLp p g, hg⟩ : ℝ)) :=
      mul_le_mul_of_nonneg_left hpw (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc, mul_assoc (16 ^ p * C)]
      exact mul_le_mul_of_nonneg_left hbound (by positivity)

private def axisOrientation (j : Fin 2) : SquareSymmetry :=
  (decide (j = 1), fun _ ↦ false)

private theorem axisOrientation_coord (j : Fin 2) (x : CarpetPoints) :
    (carpetSymmetry (axisOrientation j) x : Plane) j = (x : Plane) 0 ∧
      (carpetSymmetry (axisOrientation j) x : Plane) j.rev = (x : Plane) 1 := by
  fin_cases j <;> exact ⟨rfl, rfl⟩

private theorem oriented_wordMap_match_side {w v : List (Fin 8)}
    (hlen : w.length = v.length) (j : Fin 2)
    (hj : gridCoordinate v j = gridCoordinate w j + 1)
    (hk : gridCoordinate v j.rev = gridCoordinate w j.rev)
    (x : CarpetPoints) (hx : (x : Plane) 0 = 1) :
    wordMap w (carpetSymmetry (axisOrientation j) x) =
      wordMap v (carpetSymmetry (axisOrientation j) (carpetSymmetry horizontalFlip x)) := by
  let y := carpetSymmetry (axisOrientation j) x
  let z := carpetSymmetry (axisOrientation j) (carpetSymmetry horizontalFlip x)
  have hyj : (y : Plane) j = 1 := (axisOrientation_coord j x).1.trans hx
  have hzj : (z : Plane) j = 0 := by
    change (carpetSymmetry (axisOrientation j) (carpetSymmetry horizontalFlip x) : Plane) j = 0
    rw [(axisOrientation_coord j _).1, carpetSymmetry_horizontalFlip_first, hx, sub_self]
  have hz' : (y : Plane) j.rev = (z : Plane) j.rev := by
    change (carpetSymmetry (axisOrientation j) x : Plane) j.rev =
      (carpetSymmetry (axisOrientation j) (carpetSymmetry horizontalFlip x) : Plane) j.rev
    rw [(axisOrientation_coord j x).2, (axisOrientation_coord j _).2,
      carpetSymmetry_horizontalFlip_second]
  have hpow : (3 : ℝ) ^ w.length ≠ 0 := by positivity
  have hEq (k : Fin 2) (h : (gridCoordinate w k : ℝ) + (y : Plane) k =
      (gridCoordinate v k : ℝ) + (z : Plane) k) :
      (wordMap w y : Plane) k = (wordMap v z : Plane) k := by
    apply (mul_left_cancel₀ hpow)
    calc
      _ = (gridCoordinate w k : ℝ) + (y : Plane) k := wordMap_scaled_coord _ _ _
      _ = (gridCoordinate v k : ℝ) + (z : Plane) k := h
      _ = _ := by rw [hlen]; exact (wordMap_scaled_coord _ _ _).symm
  have hj' : (wordMap w y : Plane) j = (wordMap v z : Plane) j := by
    apply hEq
    rw [hyj, hzj, add_zero, hj, Nat.cast_add, Nat.cast_one]
  have hk' : (wordMap w y : Plane) j.rev = (wordMap v z : Plane) j.rev := by
    apply hEq
    rw [hk, hz']
  apply Subtype.ext
  ext l
  have hl : l = j ∨ l = j.rev := (by decide :
    ∀ l j : Fin 2, l = j ∨ l = j.rev) l j
  exact hl.elim (fun h ↦ h.symm ▸ hj') (fun h ↦ h.symm ▸ hk')

private theorem exists_oriented_word_energy (f : C(CarpetPoints, ℝ))
    (hf : continuousLp p f ∈ E.domain) (w : List (Fin 8)) (j : Fin 2) :
    let v := f.comp ⟨wordMap w, continuous_wordMap w⟩
    let u := v.comp ⟨carpetSymmetry (axisOrientation j), continuous_carpetSymmetry _⟩
    ∃ hu : continuousLp p u ∈ E.domain,
      E.energy ⟨continuousLp p u, hu⟩ = E.energy (E.pullbackWord w ⟨continuousLp p f, hf⟩) := by
  let v := f.comp ⟨wordMap w, continuous_wordMap w⟩
  let u := v.comp ⟨carpetSymmetry (axisOrientation j), continuous_carpetSymmetry _⟩
  let g := E.pullbackWord w ⟨continuousLp p f, hf⟩
  have he : (g : CarpetLp p) = continuousLp p v := by
    apply Lp.ext
    exact (E.pullbackWord_isLpPullback w _).trans
      (((quasiMeasurePreserving_wordMap w).ae_eq_comp (continuousLp_ae_eq p f)).trans
        (continuousLp_ae_eq p v).symm)
  let s := axisOrientation j
  let g' := E.pullbackSymmetry s g
  have he' : continuousLp p u = (g' : CarpetLp p) := by
    apply Lp.ext
    have hv := (measurePreserving_carpetSymmetry s).quasiMeasurePreserving.ae_eq_comp
      (continuousLp_ae_eq p v)
    rw [← he] at hv
    exact (continuousLp_ae_eq p u).trans ((symmetryPullback_isLpPullback s (g : CarpetLp p)).trans hv).symm
  have hu : continuousLp p u ∈ E.domain := he'.symm ▸ g'.property
  exact ⟨hu, (congrArg E.energy (Subtype.ext he')).trans (E.energy_pullbackSymmetry s g)⟩

/-- Two same-level cells sharing a side have their mean difference
controlled by the energies of the two pullbacks. -/
theorem exists_mean_gap_of_adjacent_words :
    ∃ C > (0 : ℝ), ∀ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain)
      (w v : List (Fin 8)) (j : Fin 2), w.length = v.length →
      gridCoordinate v j = gridCoordinate w j + 1 →
      gridCoordinate v j.rev = gridCoordinate w j.rev →
      |(∫ x, f (wordMap w x) ∂carpetMeasure) - ∫ x, f (wordMap v x) ∂carpetMeasure| ^ p ≤
        C * ((E.energy (E.pullbackWord w ⟨continuousLp p f, hf⟩) : ℝ) +
          (E.energy (E.pullbackWord v ⟨continuousLp p f, hf⟩) : ℝ)) := by
  obtain ⟨C, hC, hgap⟩ := E.exists_mean_gap_of_common_horizontal_side
  refine ⟨C, hC, fun f hf w v j hlen hj hk ↦ ?_⟩
  let orient : C(CarpetPoints, CarpetPoints) :=
    ⟨carpetSymmetry (axisOrientation j), continuous_carpetSymmetry _⟩
  let w' := f.comp ⟨wordMap w, continuous_wordMap w⟩
  let v' := f.comp ⟨wordMap v, continuous_wordMap v⟩
  let u := w'.comp orient
  let z := v'.comp orient
  obtain ⟨hu, hue⟩ := E.exists_oriented_word_energy f hf w j
  obtain ⟨hz, hze⟩ := E.exists_oriented_word_energy f hf v j
  have hm := hgap u z hu hz (fun x hx ↦ congrArg f (oriented_wordMap_match_side hlen j hj hk x hx))
  have hme : MeasurableEmbedding (carpetSymmetry (axisOrientation j)) :=
    ((continuous_carpetSymmetry _).isClosedEmbedding (bijective_carpetSymmetry _).1).measurableEmbedding
  change |(∫ x, w' (carpetSymmetry (axisOrientation j) x) ∂carpetMeasure) -
    ∫ x, v' (carpetSymmetry (axisOrientation j) x) ∂carpetMeasure| ^ p ≤ _ at hm
  rw [(measurePreserving_carpetSymmetry _).integral_comp hme (fun x ↦ w' x),
    (measurePreserving_carpetSymmetry _).integral_comp hme (fun x ↦ v' x),
    hue, hze] at hm
  exact hm

end SelfSimilarPEnergy
end CarpetEnergy
