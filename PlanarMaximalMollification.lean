import PlanarBallDensityWeakBound
import PlanarMollifierBallAverage
import MaximalTailMoment

/-!
# Strong (L^p) control of finite maxima of planar mollifications
-/

open ContinuousLinearMap Filter Function MeasureTheory Metric Set
open scoped Convolution ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 4100000 in
/-- Uniform weak tails for families of mollifications, with only the
portion of the input above half the threshold contributing to the bound. -/
theorem exists_planar_mollification_truncated_tail_bound :
    ∃ C > (0 : ℝ), ∀ (f : PlanarCoordinates → ℝ), Measurable f → Integrable f volume →
      (∀ x, 0 ≤ f x) → ∀ t > (0 : ℝ),
      volume {x | ∃ n, t < mollify volume n f x} ≤ ENNReal.ofReal (C / t) *
        ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal (f x) ∂volume := by
  obtain ⟨A, hA, hballs⟩ := exists_planar_mollifier_ball_integral_bounds
  refine ⟨200 * A, mul_pos (by norm_num) hA, fun f hfM hf hf₀ t ht ↦ ?_⟩
  let T : Set PlanarCoordinates := {x | t / 2 < f x}
  have hT : MeasurableSet T := measurableSet_lt measurable_const hfM
  let g := T.indicator f
  let f₀ := Tᶜ.indicator f
  have hg : Integrable g volume := hf.indicator hT
  have hg₀ (x : PlanarCoordinates) : 0 ≤ g x := Set.indicator_nonneg (fun x _ ↦ hf₀ x) _
  have hf₀I : Integrable f₀ volume := hf.indicator hT.compl
  have hf₀t (x : PlanarCoordinates) : f₀ x ≤ t / 2 := by
    by_cases hx : x ∈ T
    · rw [show f₀ x = 0 from indicator_of_notMem (show x ∉ Tᶜ from fun h ↦ h hx) _]
      exact (half_pos ht).le
    · rw [show f₀ x = f x from indicator_of_mem (show x ∈ Tᶜ from hx) _]
      exact le_of_not_gt hx
  let ν := (volume : Measure PlanarCoordinates).withDensity (fun x ↦ ENNReal.ofReal (g x))
  let E := {x | ∃ n, t < mollify volume n f x}
  have hrad (x : PlanarCoordinates) (hx : x ∈ E) :
      ∃ r ∈ Ioc 0 (1 : ℝ), ENNReal.ofReal ((t / (2 * A)) * r ^ (2 : ℕ)) ≤ ν (ball x r) := by
    obtain ⟨n, hn⟩ := hx
    let B := mollifierBump (X := PlanarCoordinates) n
    let K := B.normed volume
    let r := B.rOut
    have hr : 0 < r := B.rOut_pos
    have hr₁ : r ≤ 1 := (div_le_one (by positivity)).mpr
      (le_add_of_nonneg_left (Nat.cast_nonneg _))
    have hK := B.continuous_normed (μ := volume)
    obtain ⟨M, hM⟩ := (B.hasCompactSupport_normed (μ := volume)).exists_bound_of_continuous hK
    have hi {u : PlanarCoordinates → ℝ} (hu : Integrable u volume) :
        Integrable (fun y ↦ K y * u (x - y)) volume := by
      have htr : Integrable (fun y ↦ u (x - y)) volume := by
        simpa only [sub_eq_add_neg, Function.comp_apply] using (hu.comp_add_left x).comp_neg
      exact htr.bdd_mul hK.aestronglyMeasurable (Eventually.of_forall hM)
    have hpoint (y : PlanarCoordinates) : K y * f (x - y) =
        K y * g (x - y) + K y * f₀ (x - y) := by
      by_cases hy : x - y ∈ T
      · rw [show g (x - y) = f (x - y) from indicator_of_mem hy _,
          show f₀ (x - y) = 0 from indicator_of_notMem (show x - y ∉ Tᶜ from fun h ↦ h hy) _,
          mul_zero, add_zero]
      · rw [show g (x - y) = 0 from indicator_of_notMem hy _,
          show f₀ (x - y) = f (x - y) from indicator_of_mem (show x - y ∈ Tᶜ from hy) _,
          mul_zero, zero_add]
    have hsum : mollify volume n f x = mollify volume n g x + mollify volume n f₀ x := by
      change (∫ y, K y * f (x - y) ∂volume) =
        (∫ y, K y * g (x - y) ∂volume) + ∫ y, K y * f₀ (x - y) ∂volume
      rw [← integral_add (hi hg) (hi hf₀I)]
      exact integral_congr_ae (Eventually.of_forall hpoint)
    have hlo : mollify volume n f₀ x ≤ t / 2 := by
      change (∫ y, K y * f₀ (x - y) ∂volume) ≤ _
      have hh := integral_mono (hi hf₀I) (B.integrable_normed.mul_const (t / 2)) (fun y ↦
        mul_le_mul_of_nonneg_left (hf₀t (x - y)) (B.nonneg_normed y))
      simpa only [integral_mul_const, B.integral_normed (μ := volume), one_mul] using hh
    have hh : t / 2 ≤ (A / r ^ (2 : ℕ)) * ∫ y in ball x r, g y ∂volume := by
      refine le_trans ?_ (hballs n g hg hg₀ x).2
      linarith only [hn, hsum, hlo]
    have hrM : (t / (2 * A)) * r ^ (2 : ℕ) ≤ ∫ y in ball x r, g y ∂volume := by
      have hF : t / 2 / (A / r ^ (2 : ℕ)) ≤ ∫ y in ball x r, g y ∂volume :=
        (div_le_iff₀ (div_pos hA (sq_pos_of_pos hr))).mpr (by simpa only [mul_comm] using hh)
      refine (le_of_eq ?_).trans hF
      field_simp [hA.ne', hr.ne']
    refine ⟨r, ⟨hr, hr₁⟩, ?_⟩
    have he : ν (ball x r) = ENNReal.ofReal (∫ y in ball x r, g y ∂volume) := by
      change volume.withDensity (fun y ↦ ENNReal.ofReal (g y)) (ball x r) = _
      rw [withDensity_apply _ isOpen_ball.measurableSet,
        ofReal_integral_eq_lintegral_ofReal hg.restrict (Eventually.of_forall hg₀)]
    rw [he]
    exact ENNReal.ofReal_le_ofReal hrM
  have hb := planar_volume_le_of_ball_density ν (div_pos ht (mul_pos (by norm_num) hA)) hrad
  have hC : 100 / (t / (2 * A)) = (200 * A) / t := by field_simp [ht.ne', hA.ne']; ring
  have hν : ν univ = ∫⁻ x in T, ENNReal.ofReal (f x) ∂volume := by
    change volume.withDensity (fun x ↦ ENNReal.ofReal (T.indicator f x)) univ = _
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← lintegral_indicator hT]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ T
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]
  rwa [hC, hν] at hb

/-- Strong moment bounds for measurable profiles bounded at each point
by some mollification of a fixed nonnegative input. -/
theorem exists_planar_maximal_mollify_moment_bound {p : ℝ} (hp : 1 < p) :
    ∃ C > (0 : ℝ), ∀ (f F : PlanarCoordinates → ℝ), Measurable f → Integrable f volume →
      Measurable F → (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ F x) →
      (∀ x, ∃ n, F x ≤ mollify volume n f x) →
      (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂volume) ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂volume := by
  obtain ⟨A, hA, htail⟩ := exists_planar_mollification_truncated_tail_bound
  refine ⟨A * (p / (p - 1)) * 2 ^ (p - 1), by positivity, fun f F hf hfI hF hf₀ hF₀ hle ↦ ?_⟩
  refine lintegral_rpow_le_of_truncated_tail_bound hp hA.le hf hF hf₀ hF₀ (fun t ht ↦ ?_)
  refine (measure_mono ?_).trans (htail f hf hfI hf₀ t ht)
  intro x hx
  obtain ⟨n, hn⟩ := hle x
  exact ⟨n, (show t < F x from hx).trans_le hn⟩

/-- Bochner-moment form of the maximal mollification bound. -/
theorem exists_planar_maximal_mollify_integral_bound {p : ℝ} (hp : 1 < p) :
    ∃ C > (0 : ℝ), ∀ (f F : PlanarCoordinates → ℝ), Measurable f → Integrable f volume →
      Integrable (fun x ↦ f x ^ p) volume → Measurable F →
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ F x) →
      (∀ x, ∃ n, F x ≤ mollify volume n f x) →
      Integrable (fun x ↦ F x ^ p) volume ∧
        (∫ x, F x ^ p ∂volume) ≤ C * ∫ x, f x ^ p ∂volume := by
  obtain ⟨C, hC, hbound⟩ := exists_planar_maximal_mollify_moment_bound hp
  refine ⟨C, hC, fun f F hf hfI hfP hF hf₀ hF₀ hpt ↦ ?_⟩
  have hp₀ := zero_lt_one.trans hp
  have hb := hbound f F hf hfI hF hf₀ hF₀ hpt
  rw [← ofReal_integral_eq_lintegral_ofReal hfP
    (Eventually.of_forall fun x ↦ Real.rpow_nonneg (hf₀ x) p), ← ENNReal.ofReal_mul hC.le] at hb
  have hI : Integrable (fun x ↦ F x ^ p) volume := by
    refine ⟨((Real.continuous_rpow_const hp₀.le).measurable.comp hF).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x ↦ Real.rpow_nonneg (hF₀ x) p)).mpr
      (hb.trans_lt ENNReal.ofReal_lt_top)
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Eventually.of_forall fun x ↦ Real.rpow_nonneg (hF₀ x) p)] at hb
  exact ⟨hI, (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le
    (integral_nonneg fun x ↦ Real.rpow_nonneg (hf₀ x) p))).mp hb⟩

end CarpetEnergy
