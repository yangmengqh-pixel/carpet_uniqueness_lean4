import PlanarSobolevTail
import PlanarWeightedMollifier
import PlanarRootWeightedMeasure

/-!
# Smooth approximations to reciprocal upper-tail cutoffs
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

theorem integrable_of_continuous_of_ae_mem_compact_measure {κ : Measure Plane2}
    [IsFiniteMeasure κ] {K : Set Plane2} (hK : IsCompact K) (hκK : ∀ᵐ x ∂κ, x ∈ K)
    {f : Plane2 → ℝ} (hf : Continuous f) : Integrable f κ := by
  have hI := hf.continuousOn.integrableOn_compact (μ := κ) hK
  change Integrable f (κ.restrict K) at hI
  rwa [Measure.restrict_eq_self_of_ae_mem hκK] at hI

set_option maxHeartbeats 4100000 in
/-- Smooth mollifications of a reciprocal cutoff retain the arbitrarily
small weighted derivative bound. The limiting cutoff attenuates the original
weight by a uniform constant. -/
theorem exists_planar_reciprocal_approximation {p : ℝ} (hp : 1 < p)
    {κ : Measure Plane2} [IsFiniteMeasure κ] {S : Set Plane2}
    (hS : IsCompact S) (hκS : ∀ᵐ x ∂κ, x ∈ S)
    {s : ℝ≥0∞} (hs : 0 < s) (hsfin : s ≠ ∞)
    {a : Plane2 → ℝ} (ha : Measurable a) (ha₀ : ∀ x, 0 ≤ a x) (haI : Integrable a volume)
    (g : Fin 2 → Plane2 → ℝ) (hgI : ∀ i, Integrable (g i) volume)
    (hgLp : ∀ i, MemLp (g i) (ENNReal.ofReal p) volume)
    (hg : ∀ i, HasWeakDirectionalDerivative volume a (g i) (planarDirection i))
    (hdom : s • κ ≤ volume.withDensity (fun x ↦ ENNReal.ofReal (a x ^ p)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∃ (b : Plane2 → ℝ) (u : ℕ → Plane2 → ℝ),
      Measurable b ∧ (∀ x, b x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, (a x + 1) * (1 - b x) ≤ C) ∧
      (∀ n, ContDiff ℝ 1 (u n) ∧ (∀ x, u n x ∈ Icc (0 : ℝ) 1) ∧
        ∀ i : Fin 2, (∫ x, |fderiv ℝ (u n) x (planarDirection i)| ^ p ∂κ) ≤ δ) ∧
      (∀ᵐ x ∂κ, Tendsto (fun n ↦ u n x) atTop (𝓝 (b x))) ∧
      (∫ x, |b x| ^ p ∂κ) < δ := by
  let J (i : Fin 2) := ∫ x, |fderiv ℝ ((mollifierBump 0).normed volume) x (planarDirection i)| ∂volume
  let L := max 1 (max (J 0) (J 1))
  let D := L ^ p * (2 : ℝ) ^ (p - 1)
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hsR : 0 < s.toReal := ENNReal.toReal_pos hs.ne' hsfin
  let η := min δ (s.toReal * δ / D)
  have hη : 0 < η := lt_min hδ (div_pos (mul_pos hsR hδ) hD)
  obtain ⟨C, hC, b, T, hbM, hb01, hbI, hbδ, hTM, hTI, hrec, hinc, V, hV, hVδ⟩ :=
    exists_planar_sobolev_tail hp ha ha₀ haI g hgI hgLp hg κ hη
  let u (n : ℕ) := mollify volume n b
  have hκac : κ ≪ volume := by
    intro A hA
    have hz := (withDensity_absolutelyContinuous volume (fun x ↦ ENNReal.ofReal (a x ^ p))) hA
    have hh := hdom A
    rw [hz, smul_apply, smul_eq_mul] at hh
    exact (mul_eq_zero.mp (nonpos_iff_eq_zero.mp hh)).resolve_left hs.ne'
  refine ⟨C, hC, b, u, hbM, hb01, hrec, ?_, hκac.ae_le (ae_tendsto_mollify volume hbI),
    hbδ.trans_le (min_le_left _ _)⟩
  intro n
  have huc : ContDiff ℝ 1 (u n) := contDiff_mollify volume hbI
  refine ⟨huc, fun x ↦ ⟨mollify_nonneg volume n (fun y ↦ (hb01 y).1) x, ?_⟩, ?_⟩
  · let K := (mollifierBump (X := Plane2) n).normed volume
    have hKI : Integrable K volume := (mollifierBump n).integrable_normed
    have hKc : Continuous K := (mollifierBump n).continuous_normed
    obtain ⟨M, hM⟩ := ((mollifierBump (X := Plane2) n).hasCompactSupport_normed (μ := volume)).exists_bound_of_continuous hKc
    have htr : Integrable (fun y ↦ b (x - y)) volume := by
      simpa only [sub_eq_add_neg, Function.comp_apply] using (hbI.comp_add_left x).comp_neg
    have hI : Integrable (fun y ↦ K y * b (x - y)) volume :=
      htr.bdd_mul hKc.aestronglyMeasurable (Eventually.of_forall hM)
    change (∫ y, K y * b (x - y) ∂volume) ≤ 1
    rw [← (mollifierBump (X := Plane2) n).integral_normed (μ := volume)]
    exact integral_mono hI hKI (fun y ↦ mul_le_of_le_one_right
      ((mollifierBump (X := Plane2) n).nonneg_normed y) (hb01 _).2)
  · intro i
    let f (x : Plane2) := fderiv ℝ (u n) x (planarDirection i)
    have hf : Continuous f := (huc.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hfp : Integrable (fun x ↦ |f x| ^ p) κ :=
      integrable_of_continuous_of_ae_mem_compact_measure hS hκS
        (hf.abs.rpow_const (fun _ ↦ Or.inr (zero_le_one.trans hp.le)))
    have hcmp := smul_integral_rpow_le_root_weighted_lintegral ha ha₀ hf.measurable
      (zero_lt_one.trans hp) hfp hdom
    have hweighted := lintegral_weighted_mollify_fderiv_rpow_le hp ha₀ hbI hTM hTI hinc V
      (fun j ↦ (hV j).1) (fun j ↦ (hV j).2.1) (fun j ↦ (hV j).2.2) n (planarDirection i)
    have hE := hcmp.trans hweighted
    have hJ₀ : 0 ≤ J i := integral_nonneg (fun _ ↦ abs_nonneg _)
    have hJ : J i ≤ L := by
      fin_cases i
      · exact (le_max_left (J 0) (J 1)).trans (le_max_right _ _)
      · exact (le_max_right (J 0) (J 1)).trans (le_max_right _ _)
    let R := (∫ x, |V 0 x| ^ p ∂volume) + ∫ x, |V 1 x| ^ p ∂volume
    have hR : 0 ≤ R := add_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    change s * ENNReal.ofReal (∫ x, |f x| ^ p ∂κ) ≤ ENNReal.ofReal (J i) ^ p *
      ENNReal.ofReal ((2 : ℝ) ^ (p - 1) * R) at hE
    have hfinite : ENNReal.ofReal (J i) ^ p * ENNReal.ofReal ((2 : ℝ) ^ (p - 1) * R) ≠ ∞ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hJ₀ (zero_le_one.trans hp.le)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hh := ENNReal.toReal_mono hfinite hE
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.ofReal_rpow_of_nonneg hJ₀ (zero_le_one.trans hp.le),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hJ₀ _), ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 : ℝ) ^ (p - 1) * R),
      ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _))] at hh
    apply (mul_le_mul_iff_right₀ hsR).mp
    calc
      _ ≤ J i ^ p * ((2 : ℝ) ^ (p - 1) * R) := hh
      _ ≤ D * R := by
        dsimp only [D]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hJ₀ hJ (zero_le_one.trans hp.le)) (by positivity)
      _ ≤ _ := by
        have hRδ : R ≤ s.toReal * δ / D := hVδ.le.trans (min_le_right _ _)
        nlinarith only [(le_div_iff₀ hD).mp hRδ]

end CarpetEnergy
