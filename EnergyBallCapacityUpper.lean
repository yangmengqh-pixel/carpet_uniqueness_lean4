import EnergyBallScale
import EnergyUniformNeighborhoodCutoff
import EnergyGlobalNormalization

/-!
# An upper capacity bound for pairs of concentric carpet balls
-/

open Filter Function Metric MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 2600000 in
/-- Every Definition 2.1 energy has continuous ball cutoffs with the
upper energy bound at its walk dimension. -/
theorem exists_ball_capacity_cutoff :
    ∃ A C : ℝ, 1 < A ∧ 0 < C ∧ ∀ (x : CarpetPoints) (r : ℝ), 0 < r →
      ∃ g : E.continuousCore,
        (∀ y ∈ ball x (2 * r), g.val y = 1) ∧ tsupport g.val ⊆ ball x (A * r) ∧
        (∀ y, g.val y ∈ Icc (0 : ℝ) 1) ∧
        (E.energy (E.continuousCoreToDomain g) : ℝ) ≤
          C * r ^ (carpetSimilarityDimension - E.walkDimension) := by
  obtain ⟨C₀, hC₀, hcut⟩ := E.exists_uniform_neighborhood_cutoff 2
  let s := carpetSimilarityDimension - E.walkDimension
  let D := diam (univ : Set CarpetPoints)
  have hD : 0 ≤ D := diam_nonneg
  let A := 2 * (3 * ((3 : ℝ) + 1) * D + 1) + 1
  let C := C₀ * ((3 : ℝ) ^ |s| * (2 : ℝ) ^ s)
  have hA : 1 < A := by dsimp only [A]; linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨A, C, hA, hC, fun x r hr ↦ ?_⟩
  by_cases hr₁ : 2 * r ≤ 1
  · have h2r : 0 < 2 * r := by positivity
    obtain ⟨n, hn₀, hn₁⟩ := exists_ternary_radius_bracket h2r hr₁
    let w := centerWord n x
    obtain ⟨g, hg0, hg1, hg01, hg⟩ := hcut n w
    refine ⟨g, ?_, ?_, hg01, ?_⟩
    · exact fun y hy ↦ hg1 y (ball_subset_centerWord_neighborhood_of_le x hn₁ hy)
    · have hG : tsupport g.val ⊆ wordCellUnion (cellNeighborhood w 3) :=
        closure_minimal (fun y hy ↦ by
          by_contra h
          exact hy (hg0 y h)) (isClosed_wordCellUnion _)
      refine hG.trans ((centerWord_neighborhood_subset_ball (k := 3) x h2r hn₀).trans
        (ball_subset_ball ?_))
      push_cast
      have hle : (3 * ((3 : ℝ) + 1) * D + 1) * (2 * r) ≤ A * r := by
        dsimp only [A]
        linarith
      exact hle
    · have hh := E.scalingFactor_pow_le_rpow_of_radius_bracket h2r hn₀ hn₁
      refine hg.trans ((mul_le_mul_of_nonneg_left hh hC₀.le).trans_eq ?_)
      rw [Real.mul_rpow (by norm_num) hr.le]
      change C₀ * (3 ^ |s| * (2 ^ s * r ^ s)) = C * r ^ s
      dsimp only [C]
      ring
  · let g := E.constCore 1
    have hg (y : CarpetPoints) : g.val y = 1 := rfl
    refine ⟨g, fun y _ ↦ hg y, fun y _ ↦ ?_, fun y ↦ ?_, ?_⟩
    · apply mem_ball.mpr
      have hdist := dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ y) (mem_univ x)
      have hAr : D < A * r := by
        have hh : (1 : ℝ) / 2 < r := by linarith [not_le.mp hr₁]
        have hA₀ := zero_lt_one.trans hA
        exact (show D ≤ A * (1 / 2) by dsimp only [A]; linarith).trans_lt
          (mul_lt_mul_of_pos_left hh hA₀)
      exact hdist.trans_lt hAr
    · rw [hg]
      exact ⟨zero_le_one, le_rfl⟩
    · have hE : E.energy (E.continuousCoreToDomain g) = 0 := by
        dsimp only [g]
        rw [E.continuousCoreToDomain_constCore]
        exact (E.zero_iff_constant _).mpr ⟨1, rfl⟩
      rw [hE, NNReal.coe_zero]
      exact mul_nonneg hC.le (Real.rpow_nonneg hr.le _)

/-- Volume-normalized upper cutoff energy, as in the capacity upper bound. -/
theorem exists_ball_capacity_cutoff_volume :
    ∃ A C : ℝ, 1 < A ∧ 0 < C ∧ ∀ (x : CarpetPoints) (r : ℝ), 0 < r → r ≤ 1 →
      ∃ g : E.continuousCore,
        (∀ y ∈ ball x (2 * r), g.val y = 1) ∧ tsupport g.val ⊆ ball x (A * r) ∧
        (∀ y, g.val y ∈ Icc (0 : ℝ) 1) ∧
        (E.energy (E.continuousCoreToDomain g) : ℝ) ≤
          C * carpetMeasure.real (ball x r) / r ^ E.walkDimension := by
  obtain ⟨A, C, hA, hC, hcut⟩ := E.exists_ball_capacity_cutoff
  obtain ⟨a, _, ha, _, hvol⟩ := exists_carpet_ball_volume_bounds
  refine ⟨A, C / a, hA, div_pos hC ha, fun x r hr hr₁ ↦ ?_⟩
  obtain ⟨g, hg1, hgs, hg01, hg⟩ := hcut x r hr
  refine ⟨g, hg1, hgs, hg01, hg.trans ?_⟩
  rw [Real.rpow_sub hr, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
  have hh := mul_le_mul_of_nonneg_left (hvol x r hr hr₁).1 (div_nonneg hC.le ha.le)
  rwa [← mul_assoc, div_mul_cancel₀ _ ha.ne'] at hh

end CarpetEnergy.SelfSimilarPEnergy
