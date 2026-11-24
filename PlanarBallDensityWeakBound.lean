import UpperDensityBallCover
import PlanarLowerDensity

/-!
# A weak estimate for planar upper ball averages
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 2200000 in
/-- A family of balls carrying at least a fixed density has a set of
centers of controlled Lebesgue measure. -/
theorem planar_volume_le_of_ball_density
    (μ : Measure PlanarCoordinates) {A : Set PlanarCoordinates} {M R : ℝ} (hM : 0 < M)
    (hball : ∀ x ∈ A, ∃ r ∈ Ioc 0 R, ENNReal.ofReal (M * r ^ (2 : ℕ)) ≤ μ (ball x r)) :
    volume A ≤ ENNReal.ofReal (100 / M) * μ univ := by
  classical
  have hrad (x : A) : ∃ r ∈ Ioc 0 R, ENNReal.ofReal (M * r ^ (2 : ℕ)) ≤ μ (ball x.val r) :=
    hball x.val x.property
  choose r hr hmass using hrad
  obtain ⟨S, _, hdisj, hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (univ : Set A) Subtype.val r R (fun a _ ↦ (hr a).2) 5 (by norm_num)
  let B (x : S) := ball x.val.val (r x.val)
  let L (x : S) := ball x.val.val (5 * r x.val)
  let : Countable S := (hdisj.countable_of_isOpen (fun _ _ ↦ isOpen_ball)
    (fun x _ ↦ ⟨x.val, mem_ball_self (hr x).1⟩)).to_subtype
  have hdisj' : Pairwise (Disjoint on B) := by
    intro a b hab
    exact hdisj a.property b.property (fun hx ↦ hab (Subtype.ext hx))
  have hA : A ⊆ ⋃ x : S, L x := by
    intro y hy
    obtain ⟨a, ha, hsub⟩ := hcover ⟨y, hy⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hsub (mem_ball_self (hr ⟨y, hy⟩).1)⟩
  have hcomparison (x : S) : volume (L x) ≤ ENNReal.ofReal (100 / M) * μ (B x) := by
    have hr₀ : 0 ≤ r x.val := (hr x.val).1.le
    rw [show L x = ball x.val.val (5 * r x.val) from rfl,
      planar_volume_ball _ (mul_nonneg (by norm_num) hr₀)]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (hmass x.val) bot_le)
    rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) hM.le)]
    apply ENNReal.ofReal_le_ofReal
    field_simp [hM.ne']
    ring_nf
    exact le_rfl
  calc
    _ ≤ volume (⋃ x : S, L x) := measure_mono hA
    _ ≤ ∑' x : S, volume (L x) := measure_iUnion_le _
    _ ≤ ∑' x : S, ENNReal.ofReal (100 / M) * μ (B x) := tsum_le_tsum hcomparison
    _ = ENNReal.ofReal (100 / M) * μ (⋃ x : S, B x) := by
      rw [ENNReal.tsum_mul_left, measure_iUnion hdisj' (fun _ ↦ isOpen_ball.measurableSet)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) bot_le

end CarpetEnergy
