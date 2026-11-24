import EnergyClippedHarmonic
import EnergyCompactCutoff

/-!
# Local energy convergence for uniformly Cauchy harmonic functions
-/

open MeasureTheory Set

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1000000 in
/-- On a closed subset of the harmonicity region, uniform Cauchy
convergence and a global energy bound imply local energy Cauchy
convergence. -/
theorem local_energy_cauchy_of_uniform_cauchy {U V : Set CarpetPoints} (hU : IsOpen U)
    (hV : IsClosed V) (hVU : V ⊆ U) (f : ℕ → E.continuousCore)
    (hharm : ∀ n, E.IsHarmonicOn U (f n)) {M : ℝ}
    (hM : ∀ n, E.rootSeminorm (E.continuousCoreToDomain (f n)) ≤ M)
    (hclose : ∀ δ > (0 : ℝ), ∃ N : ℕ,
      ∀ n m, N ≤ n → N ≤ m → ∀ x ∈ V, |(f n).val x - (f m).val x| ≤ δ) :
    ∀ η > (0 : ℝ), ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m →
      (E.energyMeasure (E.continuousCoreToDomain (f n - f m))).real V < η := by
  intro η hη
  have hM0 : 0 ≤ M := (apply_nonneg E.rootSeminorm _).trans (hM 0)
  have hMp := Real.rpow_nonneg hM0 p
  let ε := η / (4 * (M ^ p + 1))
  have hε : 0 < ε := div_pos hη (by positivity)
  have hεbound : 2 * ε * M ^ p < η / 2 := by
    dsimp only [ε]
    apply (lt_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
    have he : 2 * (η / (4 * (M ^ p + 1))) * M ^ p * 2 = η * M ^ p / (M ^ p + 1) := by
      have hden : M ^ p + 1 ≠ 0 := ne_of_gt (by positivity)
      field_simp [hden]
      ring
    rw [he]
    apply (div_lt_iff₀ (by positivity : 0 < M ^ p + 1)).mpr
    linarith only [mul_pos hη (show (0 : ℝ) < 1 by norm_num)]
  obtain ⟨C, hC, hdeficit⟩ := E.exists_harmonic_mass_sub_le hε
  obtain ⟨χ, hχU, hχV, hχ⟩ := E.exists_core_cutoff hU hV hVU
  let R := E.rootSeminorm (E.continuousCoreToDomain χ)
  let b (t : ℝ) := t / 2 * R
  let err (t : ℝ) := 2 * C * (p * b t * (M + b t) ^ (p - 1))
  have hb : Continuous b := (continuous_id.div_const 2).mul continuous_const
  have hpow : Continuous (fun x : ℝ ↦ x ^ (p - 1)) :=
    Real.continuous_rpow_const (sub_nonneg.mpr E.one_lt_p.le)
  have herr : Continuous err := continuous_const.mul
    ((continuous_const.mul hb).mul (hpow.comp (continuous_const.add hb)))
  have herr0 : err 0 = 0 := by simp [err, b]
  have hopen : IsOpen {t | err t < η / 2} := isOpen_lt herr continuous_const
  have hz : (0 : ℝ) ∈ {t | err t < η / 2} := by
    change err 0 < η / 2
    rw [herr0]
    positivity
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen 0 hz
  let δ := r / 2
  have hδ : 0 < δ := by positivity
  have herrδ : err δ < η / 2 := hrsub (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    change |δ| < r
    rw [abs_of_pos hδ]
    dsimp only [δ]
    linarith only [hr])
  obtain ⟨N, hN⟩ := hclose δ hδ
  refine ⟨N, fun n m hn hm ↦ ?_⟩
  let k : E.continuousCore := δ • χ
  have hk (x : CarpetPoints) : k.val x = δ * χ.val x := rfl
  have hk0 (x : CarpetPoints) : 0 ≤ k.val x := by
    rw [hk]
    exact mul_nonneg hδ.le (hχ x).1
  have hkU (x) (hx : x ∉ U) : k.val x = 0 := by rw [hk, hχU x hx, mul_zero]
  have hkV (x) (hx : x ∈ V) : |(f n).val x - (f m).val x| ≤ k.val x := by
    rw [hk, hχV x hx, mul_one]
    exact hN n m hn hm x hx
  have hbδ : E.rootSeminorm (E.continuousCoreToDomain ((1 / 2 : ℝ) • k)) ≤ b δ := by
    dsimp only [k, b, R]
    rw [smul_smul, map_smul, map_smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) hδ.le)]
    exact le_of_eq (by ring)
  have h := hdeficit hU.measurableSet hVU (f n) (f m) k (hharm n) (hharm m)
    hk0 hkU hkV (hM n) (hM m) hbδ
  change (E.energyMeasure (E.continuousCoreToDomain (f n - f m))).real V ≤
    2 * ε * M ^ p + err δ at h
  linarith only [h, hεbound, herrδ]

end CarpetEnergy.SelfSimilarPEnergy
