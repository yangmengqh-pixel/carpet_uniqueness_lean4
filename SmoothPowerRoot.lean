import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Smooth approximations to the power root

The even regularization avoids the singular derivative at zero.
Its value and its derivative multiplied by the input are dominated
by the unregularized power.
-/

open Filter
open scoped Topology

namespace CarpetEnergy

noncomputable def smoothPowerRoot (α ε t : ℝ) : ℝ :=
  (t ^ 2 + ε ^ 2) ^ (α / 2) - (ε ^ 2) ^ (α / 2)

theorem smoothPowerRoot_zero (α ε : ℝ) : smoothPowerRoot α ε 0 = 0 := by
  simp [smoothPowerRoot]

theorem contDiff_smoothPowerRoot (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (smoothPowerRoot α ε) :=
  (((contDiff_id.pow 2).add contDiff_const).rpow_const_of_ne
    (fun t ↦ ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hε)))).sub contDiff_const

theorem deriv_smoothPowerRoot (α : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (smoothPowerRoot α ε) t = α * t * (t ^ 2 + ε ^ 2) ^ (α / 2 - 1) := by
  have ha : 0 < t ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hε)
  have hd := (((hasDerivAt_id t).pow 2).add_const (ε ^ 2)).rpow_const
    (p := α / 2) (Or.inl ha.ne')
  have hu := (hd.sub_const ((ε ^ 2) ^ (α / 2))).deriv
  change deriv (smoothPowerRoot α ε) t = _ at hu
  rw [hu]
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

private theorem sq_rpow_mul_sq {t α : ℝ} (ht : 0 < t) :
    (t ^ 2) ^ (α / 2 - 1) * t ^ 2 = t ^ α := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  push_cast
  ring

theorem smoothPowerRoot_nonneg {α ε t : ℝ} (hα : 0 ≤ α) :
    0 ≤ smoothPowerRoot α ε t := by
  unfold smoothPowerRoot
  exact sub_nonneg.mpr (Real.rpow_le_rpow (sq_nonneg ε)
    (le_add_of_nonneg_left (sq_nonneg t)) (by positivity))

theorem smoothPowerRoot_le_rpow {α ε t : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) (ht : 0 ≤ t) :
    smoothPowerRoot α ε t ≤ t ^ α := by
  unfold smoothPowerRoot
  have h := Real.rpow_add_le_add_rpow (sq_nonneg t) (sq_nonneg ε)
    (show 0 ≤ α / 2 by positivity) (show α / 2 ≤ 1 by linarith)
  have he : (t ^ 2) ^ (α / 2) = t ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    ring
  rw [he] at h
  linarith only [h]

theorem deriv_smoothPowerRoot_mul_le_rpow {α ε t : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hε : 0 < ε) (ht : 0 ≤ t) :
    |deriv (smoothPowerRoot α ε) t * t| ≤ α * t ^ α := by
  rw [deriv_smoothPowerRoot α hε]
  have ha : 0 ≤ (t ^ 2 + ε ^ 2) ^ (α / 2 - 1) := Real.rpow_nonneg (by positivity) _
  rw [abs_of_nonneg (by positivity)]
  rcases ht.eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact mul_nonneg hα (Real.rpow_nonneg (by norm_num) _)
  have hle := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos h)
    (le_add_of_nonneg_right (sq_nonneg ε)) (show α / 2 - 1 ≤ 0 by linarith)
  have h' := mul_le_mul_of_nonneg_right hle (sq_nonneg t)
  rw [sq_rpow_mul_sq h] at h'
  calc
    _ = α * ((t ^ 2 + ε ^ 2) ^ (α / 2 - 1) * t ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h' hα

theorem exists_deriv_smoothPowerRoot_bound {α ε : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ t, |deriv (smoothPowerRoot α ε) t| ≤ C := by
  let B := (ε ^ 2) ^ (α / 2 - 1)
  have hB : 0 ≤ B := Real.rpow_nonneg (sq_nonneg _) _
  refine ⟨α * (B + 1), by positivity, fun t ↦ ?_⟩
  have ha : 0 ≤ (t ^ 2 + ε ^ 2) ^ (α / 2 - 1) := Real.rpow_nonneg (by positivity) _
  rw [deriv_smoothPowerRoot α hε, abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg ha, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hα
  by_cases ht : |t| ≤ 1
  · have hle : (t ^ 2 + ε ^ 2) ^ (α / 2 - 1) ≤ B :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hε)
        (le_add_of_nonneg_left (sq_nonneg t)) (by linarith)
    exact (mul_le_mul ht hle ha zero_le_one).trans (by linarith)
  · have ht' : 1 ≤ |t| := le_of_not_ge ht
    have ht₀ : 0 < |t| := zero_lt_one.trans_le ht'
    have he : |t| ^ 2 = t ^ 2 := sq_abs t
    have hle : (t ^ 2 + ε ^ 2) ^ (α / 2 - 1) ≤ (|t| ^ 2) ^ (α / 2 - 1) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ht₀)
        (by rw [he]; exact le_add_of_nonneg_right (sq_nonneg _)) (by linarith)
    refine (mul_le_mul_of_nonneg_left hle (abs_nonneg _)).trans ?_
    have hp : |t| ^ α ≤ |t| := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht' hα₁
    have hh : |t| * (|t| ^ 2) ^ (α / 2 - 1) ≤ 1 := by
      apply le_of_mul_le_mul_right _ ht₀
      calc
        _ = (|t| ^ 2) ^ (α / 2 - 1) * |t| ^ 2 := by ring
        _ = |t| ^ α := sq_rpow_mul_sq ht₀
        _ ≤ _ := by rw [one_mul]; exact hp
    exact hh.trans (by linarith)

theorem tendsto_smoothPowerRoot {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ smoothPowerRoot α (ε n) t) atTop (𝓝 (t ^ α)) := by
  have he := hε.pow 2
  have hα₂ : 0 < α / 2 := by positivity
  have hl := ((tendsto_const_nhds (x := t ^ 2)).add he).rpow_const (Or.inr hα₂.le)
  have hr := he.rpow_const (Or.inr hα₂.le)
  have hh : (t ^ 2) ^ (α / 2) = t ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    ring
  simpa only [smoothPowerRoot, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
    Real.zero_rpow hα₂.ne', sub_zero, hh] using hl.sub hr

theorem tendsto_deriv_smoothPowerRoot_mul {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) {ε : ℕ → ℝ}
    (hε₀ : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ deriv (smoothPowerRoot α (ε n)) t * t) atTop (𝓝 (α * t ^ α)) := by
  rcases ht.eq_or_lt with h | ht'
  · simpa only [← h, mul_zero, Real.zero_rpow hα.ne'] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have hε₂ := hε.pow 2
  have hpos : 0 < t ^ 2 := sq_pos_of_pos ht'
  have hbase : Tendsto (fun n ↦ t ^ 2 + ε n ^ 2) atTop (𝓝 (t ^ 2)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      ((tendsto_const_nhds (x := t ^ 2)).add hε₂)
  have hpow := hbase.rpow_const (Or.inl hpos.ne' : t ^ 2 ≠ 0 ∨ 0 ≤ α / 2 - 1)
  have hlim := (hpow.mul_const (t ^ 2)).const_mul α
  rw [sq_rpow_mul_sq ht'] at hlim
  apply hlim.congr
  intro n
  rw [deriv_smoothPowerRoot α (hε₀ n)]
  ring

end CarpetEnergy
