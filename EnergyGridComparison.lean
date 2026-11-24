import CarpetGridNeighbors
import EnergyAdjacentCells
import EnergyComparison

/-!
# The discrete energy of same-level cell averages

A side neighbor is controlled by the spectral-gap estimate on a pair of
profiles. A corner neighbor is controlled through a common side neighbor.
The number of terms that can use a given cell is uniformly bounded.
-/

open Function MeasureTheory Set
open scoped BigOperators NNReal

namespace CarpetEnergy

/-- The level-n grid neighbors of a word, including the word itself. -/
noncomputable def gridNeighbors {n : ℕ} (w : Fin n → Fin 8) : Finset (Fin n → Fin 8) := by
  classical
  exact Finset.univ.filter fun v ↦ GridNear (List.ofFn w) (List.ofFn v)

theorem mem_gridNeighbors {n : ℕ} {w v : Fin n → Fin 8} :
    v ∈ gridNeighbors w ↔ GridNear (List.ofFn w) (List.ofFn v) := by
  classical
  simp [gridNeighbors]

theorem gridNeighbors_card_le {n : ℕ} (w : Fin n → Fin 8) : (gridNeighbors w).card ≤ 9 := by
  classical
  let N := {v : Fin n → Fin 8 // v ∈ gridNeighbors w}
  have hn (v : N) (j : Fin 2) := (mem_gridNeighbors.mp v.property) j
  let F (v : N) (j : Fin 2) : Fin 3 := ⟨
    gridCoordinate (List.ofFn v.val) j + 1 - gridCoordinate (List.ofFn w) j, by
    obtain ⟨h₁, h₂⟩ := hn v j
    omega⟩
  have hf : Injective F := by
    intro u v he
    apply Subtype.ext
    apply List.ofFn_injective
    apply gridCoordinate_injective_of_length (by rw [List.length_ofFn, List.length_ofFn])
    intro j
    have h := congrArg (fun g : Fin 2 → Fin 3 ↦ (g j).val) he
    change gridCoordinate (List.ofFn u.val) j + 1 - gridCoordinate (List.ofFn w) j =
      gridCoordinate (List.ofFn v.val) j + 1 - gridCoordinate (List.ofFn w) j at h
    have h₁ := (hn u j).1
    have h₂ := (hn v j).1
    omega
  have h := Fintype.card_le_of_injective F hf
  simpa only [N, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, Nat.reducePow] using h

private theorem abs_sub_rpow_le_sum {p : ℝ} (hp : 0 ≤ p) (a b c : ℝ) :
    |a - c| ^ p ≤ (2 : ℝ) ^ p * (|a - b| ^ p + |b - c| ^ p) := by
  have hab : 0 ≤ |a - b| := abs_nonneg _
  have hbc : 0 ≤ |b - c| := abs_nonneg _
  let M := max |a - b| |b - c|
  have h₀ : 0 ≤ M := hab.trans (le_max_left _ _)
  have h₁ : |a - c| ≤ 2 * M := by
    calc
      _ = |(a - b) + (b - c)| := by rw [sub_add_sub_cancel]
      _ ≤ |a - b| + |b - c| := abs_add_le _ _
      _ ≤ M + M := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = _ := (two_mul _).symm
  calc
    _ ≤ (2 * M) ^ p := Real.rpow_le_rpow (abs_nonneg _) h₁ hp
    _ = 2 ^ p * M ^ p := Real.mul_rpow (by norm_num) h₀
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total |a - b| |b - c| with h | h
      · change (max |a - b| |b - c|) ^ p ≤ _
        rw [max_eq_right h]
        exact le_add_of_nonneg_left (Real.rpow_nonneg hab _)
      · change (max |a - b| |b - c|) ^ p ≤ _
        rw [max_eq_left h]
        exact le_add_of_nonneg_right (Real.rpow_nonneg hbc _)

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The mean of the pullback of a continuous function to a word cell. -/
noncomputable def continuousWordMean (f : C(CarpetPoints, ℝ)) (w : List (Fin 8)) : ℝ :=
  ∫ x, f (wordMap w x) ∂carpetMeasure

private theorem exists_mean_gap_of_grid_sideNeighbor :
    ∃ C > (0 : ℝ), ∀ (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain)
      (w v : List (Fin 8)), w.length = v.length → GridSideNeighbor w v →
      |continuousWordMean f w - continuousWordMean f v| ^ p ≤
        C * ((E.energy (E.pullbackWord w ⟨continuousLp p f, hf⟩) : ℝ) +
          (E.energy (E.pullbackWord v ⟨continuousLp p f, hf⟩) : ℝ)) := by
  obtain ⟨C, hC, h⟩ := E.exists_mean_gap_of_adjacent_words
  refine ⟨C, hC, fun f hf w v hl hg ↦ ?_⟩
  obtain ⟨j, hj, he | he⟩ := hg
  · exact h f hf w v j hl he hj.symm
  · rw [abs_sub_comm, add_comm]
    exact h f hf v w j hl.symm he hj

private theorem exists_ofFn_of_length {n : ℕ} (w : List (Fin 8)) (h : w.length = n) :
    ∃ v : Fin n → Fin 8, w = List.ofFn v := by
  subst n
  exact ⟨w.get, (List.ofFn_get _).symm⟩

private theorem gridNeighbor_sum_swap {n : ℕ} (e : (Fin n → Fin 8) → ℝ) :
    (∑ w, ∑ v ∈ gridNeighbors w, e v) = ∑ v, ∑ _ ∈ gridNeighbors v, e v := by
  classical
  simp_rw [gridNeighbors, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : GridNear (List.ofFn w) (List.ofFn v)
  · rw [ite_eq_left h, ite_eq_left (gridNear_symm h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (gridNear_symm h'))]

/-- The rescaled graph energy of continuous cell averages is bounded above
by the self-similar energy. The bound is uniform in the cell level. -/
theorem exists_gridMean_energy_le :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain),
      E.scalingFactor ^ n * (∑ w : Fin n → Fin 8, ∑ v ∈ gridNeighbors w,
        |continuousWordMean f (List.ofFn w) - continuousWordMean f (List.ofFn v)| ^ p) ≤
        C * (E.energy ⟨continuousLp p f, hf⟩ : ℝ) := by
  classical
  obtain ⟨C, hC, hside⟩ := E.exists_mean_gap_of_grid_sideNeighbor
  have hp := zero_lt_one.trans E.one_lt_p
  let D : ℝ := 4 * 2 ^ p * C
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨81 * D, by positivity, ?_⟩
  intro n f hf
  let g : E.domain := ⟨continuousLp p f, hf⟩
  let e (w : Fin n → Fin 8) := (E.energy (E.pullbackWord (List.ofFn w) g) : ℝ)
  let m (w : Fin n → Fin 8) := continuousWordMean f (List.ofFn w)
  let R (w : Fin n → Fin 8) : ℝ := ∑ v ∈ gridNeighbors w, e v
  have he (w : Fin n → Fin 8) : 0 ≤ e w := NNReal.coe_nonneg _
  have hR (w : Fin n → Fin 8) : 0 ≤ R w := Finset.sum_nonneg (fun v _ ↦ he v)
  have individually {w v : Fin n → Fin 8} (hv : v ∈ gridNeighbors w) : e v ≤ R w :=
    Finset.single_le_sum (fun v _ ↦ he v) hv
  have pointwise (w v : Fin n → Fin 8) (hv : v ∈ gridNeighbors w) :
      |m w - m v| ^ p ≤ D * R w := by
    have hw₀ : w ∈ gridNeighbors w := mem_gridNeighbors.mpr (gridNear_refl _)
    have hw_energy := individually hw₀
    have hv_energy := individually hv
    have hlen : (List.ofFn w).length = (List.ofFn v).length := by rw [List.length_ofFn, List.length_ofFn]
    have hlarge : 1 ≤ (2 : ℝ) ^ p := (Real.one_lt_rpow (by norm_num) hp).le
    have hside' (u v : Fin n → Fin 8) (h : GridSideNeighbor (List.ofFn u) (List.ofFn v)) :
        |m u - m v| ^ p ≤ C * (e u + e v) := by
      exact hside f hf _ _ (by rw [List.length_ofFn, List.length_ofFn]) h
    rcases eq_or_gridSideNeighbor_or_via hlen (mem_gridNeighbors.mp hv) with h | h | ⟨u, hu, hw_u, hu_v⟩
    · have hwv := List.ofFn_injective h
      rw [congrArg m hwv, sub_self, abs_zero, Real.zero_rpow hp.ne']
      exact mul_nonneg hD.le (hR w)
    · refine (hside' w v h).trans ?_
      have hsum := mul_le_mul_of_nonneg_left (add_le_add hw_energy hv_energy) hC.le
      have hd : 2 * C ≤ D := by
        dsimp only [D]
        exact mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ 4 * 2 ^ p) hC.le
      calc
        _ ≤ C * (R w + R w) := hsum
        _ = (2 * C) * R w := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hd (hR w)
    · have hu' : u.length = n := hu.trans List.length_ofFn
      obtain ⟨z, rfl⟩ := exists_ofFn_of_length u hu'
      have hz : e z ≤ R w := individually (mem_gridNeighbors.mpr (gridNear_of_sideNeighbor hw_u))
      have h₁ := (hside' w z hw_u).trans (mul_le_mul_of_nonneg_left (add_le_add hw_energy hz) hC.le)
      have h₂ := (hside' z v hu_v).trans (mul_le_mul_of_nonneg_left (add_le_add hz hv_energy) hC.le)
      calc
        _ ≤ 2 ^ p * (|m w - m z| ^ p + |m z - m v| ^ p) := abs_sub_rpow_le_sum hp.le _ _ _
        _ ≤ 2 ^ p * (C * (R w + R w) + C * (R w + R w)) :=
          mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)
        _ = _ := by dsimp only [D]; ring
  have h9 (w : Fin n → Fin 8) :
      (∑ v ∈ gridNeighbors w, |m w - m v| ^ p) ≤ 9 * (D * R w) := by
    calc
      _ ≤ ∑ _ ∈ gridNeighbors w, D * R w := Finset.sum_le_sum fun v hv ↦ pointwise w v hv
      _ = ((gridNeighbors w).card : ℝ) * (D * R w) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast gridNeighbors_card_le w)
        (mul_nonneg hD.le (hR w))
  have hR9 : (∑ w, R w) ≤ 9 * ∑ v, e v := by
    unfold R
    rw [gridNeighbor_sum_swap, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast gridNeighbors_card_le v) (he v)
  have hsum : (∑ w, ∑ v ∈ gridNeighbors w, |m w - m v| ^ p) ≤ (81 * D) * ∑ v, e v := by
    calc
      _ ≤ ∑ w, 9 * (D * R w) := Finset.sum_le_sum fun w _ ↦ h9 w
      _ = (9 * D) * ∑ w, R w := by
        simp only [Finset.mul_sum, mul_assoc]
      _ ≤ (9 * D) * (9 * ∑ v, e v) := mul_le_mul_of_nonneg_left hR9 (by positivity)
      _ = _ := by ring
  have hρ := E.isScalingFactor_scalingFactor.1
  change E.scalingFactor ^ n * (∑ w, ∑ v ∈ gridNeighbors w, |m w - m v| ^ p) ≤ _
  calc
    _ ≤ E.scalingFactor ^ n * ((81 * D) * ∑ v, e v) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg hρ.le n)
    _ = (81 * D) * (E.scalingFactor ^ n * ∑ v, e v) := by ring
    _ = _ := by rw [← E.energy_eq_sum_words n g]

end SelfSimilarPEnergy
end CarpetEnergy
