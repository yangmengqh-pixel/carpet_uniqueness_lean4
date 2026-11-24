import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Ring

/-!
# Fixed points of cell renormalization

Cesàro means of bounded iterates of the cell sum admit a pointwise
cluster limit. The telescoping difference between a mean and its
renormalization tends to zero, so the limit satisfies the exact cell
identity.
-/

open Filter Function Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy

section FiniteSum

variable {X I : Type*} [Fintype I]

/-- Renormalization through a fixed finite family of maps. -/
noncomputable def renormalize (r : ℝ) (pull : I → X → X) (F : X → ℝ) (x : X) : ℝ :=
  r * ∑ i, F (pull i x)

/-- The mean of the initial iterates, including the zeroth iterate. -/
noncomputable def renormalizationMean (r : ℝ) (pull : I → X → X) (F : X → ℝ)
    (n : ℕ) (x : X) : ℝ :=
  (1 / ((n : ℝ) + 1)) * ∑ k ∈ Finset.range (n + 1), ((renormalize r pull)^[k]) F x

private theorem renormalizationMean_difference (r : ℝ) (pull : I → X → X)
    (F : X → ℝ) (n : ℕ) (x : X) :
    renormalize r pull (renormalizationMean r pull F n) x - renormalizationMean r pull F n x =
      (1 / ((n : ℝ) + 1)) * (((renormalize r pull)^[n + 1]) F x - F x) := by
  let H (k : ℕ) := ((renormalize r pull)^[k]) F
  let a : ℝ := 1 / ((n : ℝ) + 1)
  have h : renormalize r pull (renormalizationMean r pull F n) x =
      a * ∑ k ∈ Finset.range (n + 1), H (k + 1) x := by
    simp only [renormalize, renormalizationMean]
    change r * (∑ i, a * ∑ k ∈ Finset.range (n + 1), H k (pull i x)) = _
    rw [← Finset.mul_sum, mul_left_comm r a, Finset.sum_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact (congrFun (Function.iterate_succ_apply' (renormalize r pull) k F) x).symm
  rw [h, renormalizationMean, ← mul_sub]
  congr 1
  change (∑ k ∈ Finset.range (n + 1), H (k + 1) x) -
    (∑ k ∈ Finset.range (n + 1), H k x) = H (n + 1) x - H 0 x
  have hshift : (∑ k ∈ Finset.range (n + 1), H (k + 1) x) + H 0 x =
      ∑ k ∈ Finset.range (n + 2), H k x := by
    exact (Finset.sum_range_succ' (fun k ↦ H k x) (n + 1)).symm
  rw [show (∑ k ∈ Finset.range (n + 2), H k x) =
    (∑ k ∈ Finset.range (n + 1), H k x) + H (n + 1) x from
      Finset.sum_range_succ (fun k ↦ H k x) (n + 1)] at hshift
  linarith only [hshift]

theorem exists_renormalization_fixedPoint (r : ℝ) (pull : I → X → X) (F L U : X → ℝ)
    (hL : ∀ n x, L x ≤ ((renormalize r pull)^[n]) F x)
    (hU : ∀ n x, ((renormalize r pull)^[n]) F x ≤ U x) :
    ∃ (l : Filter ℕ) (G : X → ℝ), l.NeBot ∧ l ≤ atTop ∧
      (∀ x, L x ≤ G x ∧ G x ≤ U x) ∧
      (∀ x, Tendsto (fun n ↦ renormalizationMean r pull F n x) l (𝓝 (G x))) ∧
      renormalize r pull G = G := by
  let H (n : ℕ) := renormalizationMean r pull F n
  let K := Set.pi univ (fun x ↦ Icc (L x) (U x))
  have hK : IsCompact K := isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hH (n : ℕ) : H n ∈ K := by
    intro x _
    unfold H renormalizationMean
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have h₁ := Finset.sum_le_sum (s := Finset.range (n + 1)) fun k _ ↦ hL k x
    have h₂ := Finset.sum_le_sum (s := Finset.range (n + 1)) fun k _ ↦ hU k x
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h₁ h₂
    rw [one_div, ← div_eq_inv_mul]
    exact ⟨(le_div_iff₀ hn).mpr (by simpa only [mul_comm (L x)] using h₁),
      (div_le_iff₀ hn).mpr (by simpa only [mul_comm (U x)] using h₂)⟩
  obtain ⟨l, hl⟩ := exists_ultrafilter_le (atTop : Filter ℕ)
  obtain ⟨G, hG, ht⟩ := hK.ultrafilter_le_nhds' (l.map H)
    (Ultrafilter.mem_map.mpr (show H ⁻¹' K ∈ l from Eventually.of_forall hH))
  have hpoint (x : X) : Tendsto (fun n ↦ H n x) (l : Filter ℕ) (𝓝 (G x)) :=
    ((continuous_apply x).tendsto G).comp ht
  refine ⟨l, G, inferInstance, hl, fun x ↦ hG x (mem_univ _), hpoint, ?_⟩
  funext x
  have hdiff : Tendsto (fun n ↦ renormalize r pull (H n) x - H n x)
      (l : Filter ℕ) (𝓝 (renormalize r pull G x - G x)) := by
    unfold renormalize
    exact ((tendsto_finsetSum _ fun i _ ↦ hpoint (pull i x)).const_mul r).sub (hpoint x)
  have hzero : Tendsto (fun n ↦ renormalize r pull (H n) x - H n x) atTop (𝓝 0) := by
    let M := (U x - L x)
    have hε : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hupper : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) * M) atTop (𝓝 0) := by
      simpa only [zero_mul] using hε.mul_const M
    have hlower : Tendsto (fun n : ℕ ↦ -((1 / ((n : ℝ) + 1)) * M)) atTop (𝓝 0) := by
      simpa only [neg_zero] using hupper.neg
    have hb (n : ℕ) :
        -((1 / ((n : ℝ) + 1)) * M) ≤ renormalize r pull (H n) x - H n x ∧
          renormalize r pull (H n) x - H n x ≤ (1 / ((n : ℝ) + 1)) * M := by
      dsimp only [H]
      rw [renormalizationMean_difference, ← mul_neg]
      have hn : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      have h₁ := hL (n + 1) x
      have h₂ := hU (n + 1) x
      have h₃ := hL 0 x
      have h₄ := hU 0 x
      change L x ≤ F x at h₃
      change F x ≤ U x at h₄
      dsimp only [M]
      exact ⟨mul_le_mul_of_nonneg_left (by linarith) hn,
        mul_le_mul_of_nonneg_left (by linarith) hn⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
      (fun n ↦ (hb n).1) (fun n ↦ (hb n).2)
  exact sub_eq_zero.mp (tendsto_nhds_unique hdiff (hzero.mono_left hl))

end FiniteSum

end CarpetEnergy
