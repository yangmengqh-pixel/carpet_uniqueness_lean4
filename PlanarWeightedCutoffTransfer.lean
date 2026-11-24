import PlanarReciprocalApproximation
import PlanarAttenuatedMoments
import EnergyWeightedCapacityNonconcentration

/-!
# Transfer from unweighted to weighted smooth cutoffs
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy

local notation "Plane2" => Fin 2 → ℝ

private theorem abs_add_rpow_le {p a b : ℝ} (hp : 1 ≤ p) :
    |a + b| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  apply (Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (zero_le_one.trans hp)).trans
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨|a|, abs_nonneg _⟩ : ℝ≥0) (⟨|b|, abs_nonneg _⟩ : ℝ≥0) hp

set_option maxHeartbeats 6500000 in
/-- The cutoff implication of Proposition 5.8 for measures supported
on a compact set, in the form used in Proposition 5.11. -/
theorem hasSmallWeightedCutoffsOnCompacts_of_sobolev_dominator
    {p : ℝ} (hp : 1 < p) {κ : Measure Plane2} [IsFiniteMeasure κ] {B S : Set Plane2}
    (hS : IsCompact S) (hκS : ∀ᵐ x ∂κ, x ∈ S)
    {s : ℝ≥0∞} (hs : 0 < s) (hsfin : s ≠ ∞)
    {u : Plane2 → ℝ} (hu : Measurable u) (hu₀ : ∀ x, 0 ≤ u x)
    (hSob : MemPlanarSobolev p u)
    (hdom : s • κ ≤ volume.withDensity (fun x ↦ ENNReal.ofReal (u x ^ p)))
    (hcut : HasSmallWeightedCutoffsOnCompacts p volume B) :
    HasSmallWeightedCutoffsOnCompacts p κ B := by
  intro K hKB hK ε hε
  obtain ⟨a, ha, ha₀, haEq, haI, _, g, hg⟩ := exists_integrable_planar_sobolev_localization hp hu hu₀ hSob hS
  have hdom' := root_weight_domination_of_ae_eq p hS.measurableSet hκS haEq hdom
  let D := (2 : ℝ) ^ (p - 1)
  let δ := ε / (4 * D)
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hD)
  have hε' : D * (δ + δ) ≤ ε := by
    dsimp only [δ]
    field_simp [hD.ne']
    linarith
  obtain ⟨C, hC, b, v, hb, hb01, hrec, hv, hvlim, hbδ⟩ :=
    exists_planar_reciprocal_approximation hp hS hκS hs hsfin ha ha₀ haI g
      (fun i ↦ (hg i).1) (fun i ↦ (hg i).2.1) (fun i ↦ (hg i).2.2) hdom' hδ
  let A := C ^ p / s.toReal
  have hA : 0 ≤ A := div_nonneg (Real.rpow_nonneg hC.le _) ENNReal.toReal_nonneg
  let η := δ / (2 * (A + 1))
  have hη : 0 < η := div_pos hδ (mul_pos (by norm_num) (by linarith))
  have hη' : A * η ≤ δ / 2 := by
    dsimp only [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 2 * (A + 1) by positivity)).mpr
    nlinarith only [hA, hδ.le]
  obtain ⟨f, hf, hfs, hf01, hfK, hfη, hfDη⟩ := hcut K hKB hK η hη
  let T (i : Fin 2) (x : Plane2) := fderiv ℝ f x (planarDirection i)
  have hTc (i : Fin 2) : Continuous (T i) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hTs (i : Fin 2) : HasCompactSupport (T i) := hfs.fderiv_apply ℝ (planarDirection i)
  have hp₀ := zero_lt_one.trans hp
  have hLpK {F : Plane2 → ℝ} (hF : Continuous F) : Integrable (fun x ↦ |F x| ^ p) κ :=
    integrable_of_continuous_of_ae_mem_compact_measure hS hκS
      (hF.abs.rpow_const (fun _ ↦ Or.inr hp₀.le))
  have hLpL {F : Plane2 → ℝ} (hF : Continuous F) (hFs : HasCompactSupport F) :
      Integrable (fun x ↦ |F x| ^ p) volume := by
    apply (hF.abs.rpow_const (fun _ ↦ Or.inr hp₀.le)).integrable_of_hasCompactSupport
    apply hFs.mono'
    intro x hx
    by_contra hx'
    have hz : F x = 0 := notMem_support.mp (fun h ↦ hx' (subset_tsupport _ h))
    exact hx (by
      change |F x| ^ p = 0
      rw [hz, abs_zero, Real.zero_rpow hp₀.ne'])
  have hev {F : Plane2 → ℝ} (hF : Continuous F) (hFs : HasCompactSupport F)
      (hFη : (∫ x, |F x| ^ p ∂volume) ≤ η) :
      ∀ᶠ n in atTop, (∫ x, |(1 - v n x) * F x| ^ p ∂κ) ≤ δ := by
    have hlim := tendsto_integral_attenuated_rpow hp₀ (fun n ↦ (hv n).1.continuous.measurable)
      (fun n ↦ (hv n).2.1) hF.measurable (hLpK hF) hvlim
    have hbound := integral_attenuated_rpow_le hp₀ hs hsfin ha ha₀ hb hb01 hF.measurable (hLpK hF)
      (hLpL hF hFs) hC.le hrec hdom'
    have hh := hbound.trans ((mul_le_mul_of_nonneg_left hFη hA).trans hη')
    exact (hlim.eventually_lt_const (hh.trans_lt (half_lt_self hδ))).mono fun _ hn ↦ hn.le
  have hvL : Tendsto (fun n ↦ ∫ x, |v n x| ^ p ∂κ) atTop (𝓝 (∫ x, |b x| ^ p ∂κ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
    · exact fun n ↦ ((hv n).1.continuous.abs.rpow_const (fun _ ↦ Or.inr hp₀.le)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
          abs_of_nonneg ((hv n).2.1 x).1]
        exact Real.rpow_le_one ((hv n).2.1 x).1 ((hv n).2.1 x).2 hp₀.le
    · filter_upwards [hvlim] with x hx
      exact ((Real.continuous_rpow_const hp₀.le).tendsto _).comp hx.abs
  have heD : ∀ᶠ n in atTop, ∀ i : Fin 2, (∫ x, |(1 - v n x) * T i x| ^ p ∂κ) ≤ δ :=
    Filter.eventually_all.mpr fun i ↦ hev (hTc i) (hTs i) (hfDη i)
  obtain ⟨n, hnv, hnf, hnD⟩ :=
    ((hvL.eventually_lt_const hbδ).and ((hev hf.continuous hfs hfη).and heD)).exists
  let w (x : Plane2) := v n x + (1 - v n x) * f x
  have hw : ContDiff ℝ 1 w := (hv n).1.add ((contDiff_const.sub (hv n).1).mul hf)
  have hw01 (x : Plane2) : w x ∈ Icc (0 : ℝ) 1 := by
    have hx := (hv n).2.1 x
    have hy := hf01 x
    have hh : 0 ≤ 1 - v n x := sub_nonneg.mpr hx.2
    exact ⟨add_nonneg hx.1 (mul_nonneg hh hy.1),
      (add_le_add (le_refl _) (mul_le_of_le_one_right hh hy.2)).trans_eq (by ring)⟩
  obtain ⟨r, hr, hrKS⟩ := (hK.union hS).isBounded.subset_ball_lt 0 (0 : Plane2)
  obtain ⟨_, _, hχ⟩ := exists_planar_ball_cutoffs
  obtain ⟨χ, hχc, hχ01, hχ1, hχ0, _⟩ := hχ 0 r hr
  let F := χ * w
  have hχs : HasCompactSupport χ := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (3 * r))
    (fun x hx ↦ by by_contra hx'; exact hx ((hχ0 x (fun h ↦ hx' (ball_subset_closedBall h))).1))
  have hFc : ContDiff ℝ 1 F := hχc.mul hw
  have hFs : HasCompactSupport F := hχs.mul_right
  have hF01 (x : Plane2) : F x ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hχ01 x).1 (hw01 x).1,
      (mul_le_of_le_one_right (hχ01 x).1 (hw01 x).2).trans (hχ01 x).2⟩
  have hFw (x : Plane2) (hx : x ∈ S) : F =ᶠ[𝓝 x] w := by
    have hball : ∀ᶠ y in 𝓝 x, y ∈ ball (0 : Plane2) r := isOpen_ball.mem_nhds (hrKS (Or.inr hx))
    exact hball.mono fun y hy ↦ by
      change χ y * w y = w y
      rw [hχ1 y hy, one_mul]
  refine ⟨F, hFc, hFs, hF01, ?_, ?_, ?_⟩
  · intro x hxK
    change χ x * (v n x + (1 - v n x) * f x) = 1
    rw [hχ1 x (hrKS (Or.inl hxK)), hfK x hxK, one_mul, mul_one]
    ring
  · have he : (fun x ↦ |F x| ^ p) =ᵐ[κ] fun x ↦ |w x| ^ p := by
      filter_upwards [hκS] with x hx
      rw [(hFw x hx).eq_of_nhds]
    rw [integral_congr_ae he]
    have hI : Integrable (fun x ↦ |(1 - v n x) * f x| ^ p) κ :=
      hLpK ((continuous_const.sub (hv n).1.continuous).mul hf.continuous)
    have hIv : Integrable (fun x ↦ |v n x| ^ p) κ := hLpK (hv n).1.continuous
    have hB := integral_mono (hLpK hw.continuous) ((hIv.add hI).const_mul D)
      (fun x ↦ abs_add_rpow_le (a := v n x) (b := (1 - v n x) * f x) hp.le)
    rw [integral_const_mul] at hB
    change (∫ x, |w x| ^ p ∂κ) ≤ D * ∫ x, |v n x| ^ p + |(1 - v n x) * f x| ^ p ∂κ at hB
    rw [integral_add hIv hI] at hB
    exact hB.trans ((mul_le_mul_of_nonneg_left (add_le_add hnv.le hnf) hD.le).trans hε')
  · intro i
    let e := planarDirection i
    let P (x : Plane2) := fderiv ℝ (v n) x e
    have hPc : Continuous P := ((hv n).1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hd (x : Plane2) : fderiv ℝ w x e =
        (1 - v n x) * T i x + (1 - f x) * P x := by
      have hv' := (hv n).1.differentiable (by norm_num) x
      have hf' := hf.differentiable (by norm_num) x
      have hcomp : DifferentiableAt ℝ (fun x ↦ 1 - v n x) x := (differentiableAt_const (c := (1 : ℝ))).sub hv'
      change fderiv ℝ (v n + (fun y ↦ 1 - v n y) * f) x e = _
      rw [fderiv_add hv' (hcomp.mul hf'), fderiv_mul hcomp hf', fderiv_const_sub]
      simp only [add_apply, smul_apply, smul_eq_mul, neg_apply, T, P, e]
      ring
    have hAe : (fun x ↦ |fderiv ℝ F x e| ^ p) =ᵐ[κ] fun x ↦
        |(1 - v n x) * T i x + (1 - f x) * P x| ^ p := by
      filter_upwards [hκS] with x hx
      rw [(hFw x hx).fderiv_eq, hd]
    change (∫ x, |fderiv ℝ F x e| ^ p ∂κ) ≤ _
    rw [integral_congr_ae hAe]
    let J (x : Plane2) := (1 - v n x) * T i x + (1 - f x) * P x
    have hJ : Continuous J :=
      ((continuous_const.sub (hv n).1.continuous).mul (hTc i)).add
        ((continuous_const.sub hf.continuous).mul hPc)
    have hI : Integrable (fun x ↦ |(1 - v n x) * T i x| ^ p) κ :=
      hLpK ((continuous_const.sub (hv n).1.continuous).mul (hTc i))
    have hIP : Integrable (fun x ↦ |P x| ^ p) κ := hLpK hPc
    have hpoint (x : Plane2) : |J x| ^ p ≤ D * (|(1 - v n x) * T i x| ^ p + |P x| ^ p) := by
      refine (abs_add_rpow_le hp.le).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hD.le)
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hf01 x).2)]
      exact Real.rpow_le_rpow (mul_nonneg (sub_nonneg.mpr (hf01 x).2) (abs_nonneg _))
        (mul_le_of_le_one_left (abs_nonneg _) (sub_le_self _ (hf01 x).1)) hp₀.le
    have hh := integral_mono (hLpK hJ) ((hI.add hIP).const_mul D) hpoint
    rw [integral_const_mul] at hh
    change (∫ x, |J x| ^ p ∂κ) ≤ D * ∫ x, |(1 - v n x) * T i x| ^ p + |P x| ^ p ∂κ at hh
    rw [integral_add hI hIP] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add (hnD i) ((hv n).2.2 i)) hD.le).trans hε')

end CarpetEnergy
