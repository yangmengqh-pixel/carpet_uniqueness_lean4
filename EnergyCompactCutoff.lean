import EnergyFoldingAmplification
import CarpetCrossingCapacity
import Mathlib.Topology.UrysohnsLemma

/-!
# Finite-energy cutoffs for a closed set inside an open set
-/

open Set

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Regularity and scalar truncation give an exact cutoff between a
closed subset and the complement of an open neighborhood. -/
theorem exists_core_cutoff {U V : Set CarpetPoints} (hU : IsOpen U) (hV : IsClosed V)
    (hVU : V ⊆ U) : ∃ χ : E.continuousCore,
      (∀ x ∉ U, χ.val x = 0) ∧ (∀ x ∈ V, χ.val x = 1) ∧
        (∀ x, χ.val x ∈ Icc (0 : ℝ) 1) := by
  have hd : Disjoint Uᶜ V := Set.disjoint_left.mpr (fun {_} hx hy ↦ hx (hVU hy))
  obtain ⟨u, hu0, hu1, _⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl hV hd
  obtain ⟨v, hv, hclose⟩ := E.regular_sup u (1 / 3) (by norm_num)
  let φ (t : ℝ) := min (max (t - 1 / 3) 0) (1 / 3)
  have hshift : LipschitzWith 1 (fun t : ℝ ↦ t - 1 / 3) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro a b
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
    rw [show a - 1 / 3 - (b - 1 / 3) = a - b by ring]
  have hφ : LipschitzWith 1 φ := (hshift.max_const 0).min_const _
  obtain ⟨w, hw, he, _⟩ := E.exists_continuous_comp_energy_le_mul v hv hφ
  let χ : E.continuousCore := (3 : ℝ) • (⟨w, hw⟩ : E.continuousCore)
  have hχ (x : CarpetPoints) : χ.val x = 3 * φ (v x) := by
    change 3 * w x = _
    rw [he x]
  have habs (x : CarpetPoints) : |v x - u x| < 1 / 3 := by
    rw [← Real.norm_eq_abs]
    exact ((v - u).norm_coe_le_norm x).trans_lt hclose
  refine ⟨χ, ?_, ?_, ?_⟩
  · intro x hx
    have h0 : u x = 0 := hu0 hx
    have h := habs x
    rw [h0, sub_zero, abs_lt] at h
    have hv0 : v x - 1 / 3 ≤ 0 := sub_nonpos.mpr h.2.le
    rw [hχ]
    dsimp only [φ]
    rw [max_eq_right hv0, min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 3), mul_zero]
  · intro x hx
    have h1 : u x = 1 := hu1 hx
    have h := habs x
    rw [h1, abs_lt] at h
    have hv1 : 1 / 3 ≤ v x - 1 / 3 := by linarith only [h.1]
    rw [hχ]
    dsimp only [φ]
    rw [min_eq_right (hv1.trans (le_max_left _ _))]
    norm_num
  · intro x
    rw [hχ]
    refine ⟨mul_nonneg (by norm_num) (le_min (le_max_right _ _) (by norm_num)), ?_⟩
    have h : φ (v x) ≤ 1 / 3 := min_le_right _ _
    linarith only [h]

end CarpetEnergy.SelfSimilarPEnergy
