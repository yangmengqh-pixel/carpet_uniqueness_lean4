import EnergyWeightedCapacityNonconcentration
import PlanarLowerDensity

/-!
# Combining cutoff approximations of measurable sets
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy

private theorem abs_add_rpow_le {p a b : ℝ} (hp : 1 ≤ p) :
    |a + b| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  apply (Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (zero_le_one.trans hp)).trans
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨|a|, abs_nonneg _⟩ : ℝ≥0) (⟨|b|, abs_nonneg _⟩ : ℝ≥0) hp

private theorem integrable_abs_rpow_of_smoothSupport {κ : Measure PlanarCoordinates}
    [IsFiniteMeasure κ] {p : ℝ} (hp : 0 < p) {f : PlanarCoordinates → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    Integrable (fun x ↦ |f x| ^ p) κ := by
  apply (hf.abs.rpow_const (fun _ ↦ Or.inr hp.le)).integrable_of_hasCompactSupport
  apply hfs.mono'
  intro x hx
  by_contra hout
  have hzero := notMem_support.mp (fun hx' ↦ hout (subset_tsupport _ hx'))
  exact hx (by change |f x| ^ p = 0; rw [hzero, abs_zero, Real.zero_rpow hp.ne'])

set_option maxHeartbeats 4900000 in
theorem exists_small_weighted_cutoff_union {p : ℝ} (hp : 1 < p)
    {κ : Measure PlanarCoordinates} [IsFiniteMeasure κ]
    {K L : Set PlanarCoordinates} {ε₁ ε₂ : ℝ} {f g : PlanarCoordinates → ℝ}
    (hf : IsSmallWeightedCutoff p κ K ε₁ f) (hg : IsSmallWeightedCutoff p κ L ε₂ g) :
    ∃ w, IsSmallWeightedCutoff p κ (K ∪ L) ((2 : ℝ) ^ (p - 1) * (ε₁ + ε₂)) w := by
  obtain ⟨hfc, hfs, hf01, hf1, hfE, hfD⟩ := hf
  obtain ⟨hgc, hgs, hg01, hg1, hgE, hgD⟩ := hg
  let w := f + (fun x : PlanarCoordinates ↦ 1 - f x) * g
  have hwc : ContDiff ℝ 1 w := hfc.add ((contDiff_const.sub hfc).mul hgc)
  have hws : HasCompactSupport w := hfs.add hgs.mul_left
  have hw01 (x : PlanarCoordinates) : w x ∈ Icc (0 : ℝ) 1 := by
    have hh : 0 ≤ 1 - f x := sub_nonneg.mpr (hf01 x).2
    change f x + (1 - f x) * g x ∈ Icc _ _
    exact ⟨add_nonneg (hf01 x).1 (mul_nonneg hh (hg01 x).1),
      (add_le_add le_rfl (mul_le_of_le_one_right hh (hg01 x).2)).trans_eq (by ring)⟩
  let D := (2 : ℝ) ^ (p - 1)
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hp₀ := zero_lt_one.trans hp
  have hb {W F G : PlanarCoordinates → ℝ}
      (hW : Integrable (fun x ↦ |W x| ^ p) κ)
      (hF : Integrable (fun x ↦ |F x| ^ p) κ)
      (hG : Integrable (fun x ↦ |G x| ^ p) κ)
      (hpt : ∀ x, |W x| ^ p ≤ D * (|F x| ^ p + |G x| ^ p))
      (h₁ : (∫ x, |F x| ^ p ∂κ) ≤ ε₁) (h₂ : (∫ x, |G x| ^ p ∂κ) ≤ ε₂) :
      (∫ x, |W x| ^ p ∂κ) ≤ D * (ε₁ + ε₂) := by
    have h := integral_mono hW ((hF.add hG).const_mul D) hpt
    rw [integral_const_mul] at h
    change _ ≤ D * ∫ x, |F x| ^ p + |G x| ^ p ∂κ at h
    rw [integral_add hF hG] at h
    exact h.trans (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hD)
  have hmin (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (y : ℝ) :
      |(1 - x) * y| ^ p ≤ |y| ^ p := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hx.2)]
    exact Real.rpow_le_rpow (mul_nonneg (sub_nonneg.mpr hx.2) (abs_nonneg _))
      (mul_le_of_le_one_left (abs_nonneg _) (sub_le_self _ hx.1)) hp₀.le
  refine ⟨w, hwc, hws, hw01, ?_, ?_, ?_⟩
  · intro x hx
    change f x + (1 - f x) * g x = 1
    rcases hx with hk | hl
    · rw [hf1 x hk, sub_self, zero_mul, add_zero]
    · rw [hg1 x hl, mul_one]
      ring
  · apply hb (integrable_abs_rpow_of_smoothSupport hp₀ hwc.continuous hws)
      (integrable_abs_rpow_of_smoothSupport hp₀ hfc.continuous hfs)
      (integrable_abs_rpow_of_smoothSupport hp₀ hgc.continuous hgs) _ hfE hgE
    intro x
    exact (abs_add_rpow_le hp.le).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hmin (f x) (hf01 x) (g x))) hD)
  · intro i
    let e : PlanarCoordinates := Pi.single i 1
    let F (x : PlanarCoordinates) := fderiv ℝ f x e
    let G (x : PlanarCoordinates) := fderiv ℝ g x e
    let W (x : PlanarCoordinates) := fderiv ℝ w x e
    have hFe : Continuous F := (hfc.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hGe : Continuous G := (hgc.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hWe : Continuous W := (hwc.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hder (x : PlanarCoordinates) : W x = (1 - g x) * F x + (1 - f x) * G x := by
      have hdF := hfc.differentiable (by norm_num) x
      have hdG := hgc.differentiable (by norm_num) x
      have ha : DifferentiableAt ℝ (fun x ↦ 1 - f x) x := (differentiableAt_const (c := (1 : ℝ))).sub hdF
      change fderiv ℝ (f + (fun x ↦ 1 - f x) * g) x e = _
      rw [fderiv_add hdF (ha.mul hdG), fderiv_mul ha hdG, fderiv_const_sub]
      simp only [add_apply, smul_apply, smul_eq_mul, neg_apply, F, G]
      ring
    apply hb (integrable_abs_rpow_of_smoothSupport hp₀ hWe (hws.fderiv_apply ℝ e))
      (integrable_abs_rpow_of_smoothSupport hp₀ hFe (hfs.fderiv_apply ℝ e))
      (integrable_abs_rpow_of_smoothSupport hp₀ hGe (hgs.fderiv_apply ℝ e)) _ (hfD i) (hgD i)
    intro x
    rw [hder]
    exact (abs_add_rpow_le hp.le).trans (mul_le_mul_of_nonneg_left
      (add_le_add (hmin (g x) (hg01 x) (F x)) (hmin (f x) (hf01 x) (G x))) hD)

/-- A set can be approximated in the measure ν by compact subsets
carrying smooth tests of arbitrarily small κ-weighted energy. -/
def HasSmallWeightedCutoffsInMeasure (p : ℝ) (ν κ : Measure PlanarCoordinates)
    (B : Set PlanarCoordinates) : Prop :=
  ∀ ε > (0 : ℝ), ∃ K ⊆ B, IsCompact K ∧ ν (B \ K) ≤ ENNReal.ofReal ε ∧
    ∃ f, IsSmallWeightedCutoff p κ K ε f

theorem HasSmallWeightedCutoffsOnCompacts.in_measure {p : ℝ}
    {ν κ : Measure PlanarCoordinates} [IsFiniteMeasure ν] {B : Set PlanarCoordinates}
    (h : HasSmallWeightedCutoffsOnCompacts p κ B) (hB : MeasurableSet B) :
    HasSmallWeightedCutoffsInMeasure p ν κ B := by
  intro ε hε
  obtain ⟨K, hKB, hK, hKsmall⟩ := hB.exists_isCompact_sdiff_lt (μ := ν)
    (measure_ne_top _ _) (ENNReal.ofReal_ne_zero_iff.mpr hε)
  exact ⟨K, hKB, hK, hKsmall.le, h K hKB hK ε hε⟩

theorem HasSmallWeightedCutoffsInMeasure.union {p : ℝ} (hp : 1 < p)
    {ν κ : Measure PlanarCoordinates} [IsFiniteMeasure κ] {B C : Set PlanarCoordinates}
    (hB : HasSmallWeightedCutoffsInMeasure p ν κ B)
    (hC : HasSmallWeightedCutoffsInMeasure p ν κ C) :
    HasSmallWeightedCutoffsInMeasure p ν κ (B ∪ C) := by
  intro ε hε
  let R := (2 : ℝ) ^ (p - 1)
  let δ := ε / (2 * (1 + R))
  have hR : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) (by linarith))
  have hε₀ : δ + δ ≤ ε := by
    have h := (div_mul_cancel₀ ε (show 2 * (1 + R) ≠ 0 by positivity))
    change δ * (2 * (1 + R)) = ε at h
    nlinarith only [h, mul_nonneg hδ.le hR]
  have hε₁ : R * (δ + δ) ≤ ε := by
    have h := (div_mul_cancel₀ ε (show 2 * (1 + R) ≠ 0 by positivity))
    change δ * (2 * (1 + R)) = ε at h
    nlinarith only [h, hδ.le]
  obtain ⟨K, hKB, hK, hKt, f, hf⟩ := hB δ hδ
  obtain ⟨L, hLC, hL, hLt, g, hg⟩ := hC δ hδ
  obtain ⟨w, hw⟩ := exists_small_weighted_cutoff_union hp hf hg
  refine ⟨K ∪ L, union_subset_union hKB hLC, hK.union hL, ?_, w, ?_⟩
  · have hsub : (B ∪ C) \ (K ∪ L) ⊆ (B \ K) ∪ (C \ L) := by
      rintro x ⟨hx, hout⟩
      exact hx.elim (fun h ↦ Or.inl ⟨h, fun hk ↦ hout (Or.inl hk)⟩)
        (fun h ↦ Or.inr ⟨h, fun hl ↦ hout (Or.inr hl)⟩)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    exact (add_le_add hKt hLt).trans (by
      rw [← ENNReal.ofReal_add hδ.le hδ.le]
      exact ENNReal.ofReal_le_ofReal hε₀)
  · obtain ⟨hwc, hws, hw01, hwK, hwE, hwD⟩ := hw
    exact ⟨hwc, hws, hw01, hwK, hwE.trans hε₁, fun i ↦ (hwD i).trans hε₁⟩

end CarpetEnergy
