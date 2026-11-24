import CarpetCellNeighborhoods
import EnergyAdjacentCellMeans

/-!
# Comparing means in cell neighborhoods

Every diagonal touch can be replaced by two side steps through a cell
in the same neighborhood. Iterating the side estimate controls the
difference of the means by the neighborhood energy.
-/

open Function Set
open scoped BigOperators NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem abs_sub_rpow_triangle (hp : 1 ≤ p) (a b c : ℝ) :
    |a - c| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|a - b| ^ p + |b - c| ^ p) := by
  have h : |a - c| ≤ |a - b| + |b - c| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (a - b) (b - c)
  refine (Real.rpow_le_rpow (abs_nonneg _) h (zero_le_one.trans hp)).trans ?_
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    ⟨|a - b|, abs_nonneg _⟩ ⟨|b - c|, abs_nonneg _⟩ hp

private theorem exists_neighborhood_step_mean_gap :
    ∃ C > (0 : ℝ), ∀ (n k : ℕ) (f : E.domain) (w u v : Fin n → Fin 8),
      u ∈ cellNeighborhood w k → v ∈ gridNeighbors u →
      |E.wordMean (List.ofFn v) f - E.wordMean (List.ofFn u) f| ^ p ≤
        C * ∑ a ∈ cellNeighborhood w (k + 1), (E.energy (E.pullbackWord (List.ofFn a) f) : ℝ) := by
  classical
  obtain ⟨D, hD, h⟩ := E.exists_wordMean_gap_of_side_adjacent
  let Q := (2 : ℝ) ^ (p - 1)
  have hQ : 0 ≤ Q := Real.rpow_nonneg (by norm_num) _
  refine ⟨2 * D + Q * (4 * D) + 1, by positivity, fun n k f w u v hu hv ↦ ?_⟩
  let m (a : Fin n → Fin 8) := E.wordMean (List.ofFn a) f
  let e (a : Fin n → Fin 8) : ℝ := E.energy (E.pullbackWord (List.ofFn a) f)
  let A := cellNeighborhood w (k + 1)
  let S := ∑ a ∈ A, e a
  have hS : 0 ≤ S := Finset.sum_nonneg fun a _ ↦ NNReal.coe_nonneg _
  have hA (a : Fin n → Fin 8) (ha : a ∈ A) : e a ≤ S :=
    Finset.single_le_sum (fun x _ ↦ NNReal.coe_nonneg _) ha
  have huA : u ∈ A := cellNeighborhood_subset_succ w hu
  have hvA : v ∈ A := mem_cellNeighborhood_succ.mpr
    ⟨u, hu, (gridNear_iff_inter_wordMap_nonempty (by simp)).mp (mem_gridNeighbors.mp hv)⟩
  have hside (a b : Fin n → Fin 8) (ha : a ∈ A) (hb : b ∈ A)
      (hs : GridSideNeighbor (List.ofFn a) (List.ofFn b)) :
      |m a - m b| ^ p ≤ 2 * D * S := by
    obtain ⟨j, hfixed, hstep⟩ := hs
    have he : |m a - m b| ^ p ≤ D * (e a + e b) := by
      rcases hstep with hs | hs
      · exact h f (List.ofFn a) (List.ofFn b) j (by simp) hs hfixed.symm
      · have hg := h f (List.ofFn b) (List.ofFn a) j (by simp) hs hfixed
        simpa only [m, e, abs_sub_comm (E.wordMean (List.ofFn b) f), add_comm (e b)] using hg
    exact he.trans (by
      have hh : e a + e b ≤ 2 * S := by linarith [hA a ha, hA b hb]
      have h' := mul_le_mul_of_nonneg_left hh hD.le
      nlinarith [h'])
  have hNear := mem_gridNeighbors.mp hv
  obtain hEq | hSide | ⟨z, hz, h1, h2⟩ := eq_or_gridSideNeighbor_or_via (by simp) hNear
  · have he := List.ofFn_injective hEq
    subst v
    rw [sub_self, abs_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt_p).ne']
    exact mul_nonneg (by positivity) hS
  · rw [abs_sub_comm]
    exact (hside u v huA hvA hSide).trans
      (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hQ hD.le]) hS)
  · have hz' : z.length = n := hz.trans List.length_ofFn
    obtain ⟨a, ha⟩ : ∃ a : Fin n → Fin 8, z = List.ofFn a := by
      subst n
      exact ⟨z.get, (List.ofFn_get _).symm⟩
    rw [ha] at h1 h2
    have haA : a ∈ A := mem_cellNeighborhood_succ.mpr
      ⟨u, hu, (gridNear_iff_inter_wordMap_nonempty (by simp)).mp (gridNear_of_sideNeighbor h1)⟩
    rw [abs_sub_comm]
    calc
      |m u - m v| ^ p ≤ Q * (|m u - m a| ^ p + |m a - m v| ^ p) :=
        abs_sub_rpow_triangle E.one_lt_p.le _ _ _
      _ ≤ Q * ((2 * D * S) + (2 * D * S)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hside u a huA haA h1) (hside a v haA hvA h2)) hQ
      _ ≤ _ := by
        have hn : 0 ≤ (2 * D + 1) * S := mul_nonneg (by positivity) hS
        nlinarith [hn]

/-- The uniform mean comparison (4.10) on each fixed-radius cell neighborhood. -/
theorem exists_neighborhood_wordMean_gap (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (f : E.domain) (w v : Fin n → Fin 8), v ∈ cellNeighborhood w k →
      |E.wordMean (List.ofFn w) f - E.wordMean (List.ofFn v) f| ^ p ≤
        C * ∑ a ∈ cellNeighborhood w k, (E.energy (E.pullbackWord (List.ofFn a) f) : ℝ) := by
  classical
  obtain ⟨D, hD, hstep⟩ := E.exists_neighborhood_step_mean_gap
  let Q := (2 : ℝ) ^ (p - 1)
  have hQ : 0 < Q := Real.rpow_pos_of_pos (by norm_num) _
  induction k with
  | zero =>
    refine ⟨1, one_pos, fun n f w v hv ↦ ?_⟩
    have h : v = w := Finset.mem_singleton.mp hv
    subst v
    rw [sub_self, abs_zero, Real.zero_rpow (zero_lt_one.trans E.one_lt_p).ne', one_mul]
    exact Finset.sum_nonneg fun a _ ↦ NNReal.coe_nonneg _
  | succ k ih =>
    obtain ⟨C, hC, hgap⟩ := ih
    refine ⟨Q * (C + D), mul_pos hQ (add_pos hC hD), fun n f w v hv ↦ ?_⟩
    obtain ⟨u, hu, hNear⟩ := mem_cellNeighborhood_succ.mp hv
    have hv' : v ∈ gridNeighbors u :=
      mem_gridNeighbors.mpr ((gridNear_iff_inter_wordMap_nonempty (by simp)).2 hNear)
    let m (a : Fin n → Fin 8) := E.wordMean (List.ofFn a) f
    let e (a : Fin n → Fin 8) : ℝ := E.energy (E.pullbackWord (List.ofFn a) f)
    let S := ∑ a ∈ cellNeighborhood w k.succ, e a
    have hsum : (∑ a ∈ cellNeighborhood w k, e a) ≤ S :=
      Finset.sum_le_sum_of_subset_of_nonneg (cellNeighborhood_subset_succ w) (fun a _ _ ↦ NNReal.coe_nonneg _)
    have hu' : |m w - m u| ^ p ≤ C * S :=
      (hgap n f w u hu).trans (mul_le_mul_of_nonneg_left hsum hC.le)
    have hv'' : |m v - m u| ^ p ≤ D * S := hstep n k f w u v hu hv'
    calc
      |m w - m v| ^ p ≤ Q * (|m w - m u| ^ p + |m u - m v| ^ p) :=
        abs_sub_rpow_triangle E.one_lt_p.le _ _ _
      _ ≤ Q * (C * S + D * S) :=
        mul_le_mul_of_nonneg_left (add_le_add hu' (by rwa [abs_sub_comm])) hQ.le
      _ = _ := by ring

end CarpetEnergy.SelfSimilarPEnergy
