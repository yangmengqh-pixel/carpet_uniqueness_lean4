import EnergyPatchCutoffTransport
import EnergyComparison

/-!
# Uniform energy bounds for cell-neighborhood cutoffs
-/

open Filter Function MeasureTheory Set
open scoped BigOperators

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 2850000 in
/-- At every level, a cutoff of a fixed cell-neighborhood radius
has energy bounded by the level renormalization times a fixed constant. -/
theorem exists_uniform_neighborhood_cutoff (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8),
      ∃ g : E.continuousCore,
        (∀ x ∉ wordCellUnion (cellNeighborhood w (k + 1)), g.val x = 0) ∧
        (∀ x ∈ wordCellUnion (cellNeighborhood w k), g.val x = 1) ∧
        (∀ x, g.val x ∈ Icc (0 : ℝ) 1) ∧
        (E.energy (E.continuousCoreToDomain g) : ℝ) ≤ C * E.scalingFactor ^ n := by
  classical
  let W := Σ n : ℕ, Fin n → Fin 8
  let shape (a : W) := neighborhoodShape a.2 (k + 2)
  let S := range shape
  let : Fintype S := Fintype.ofFinite _
  let a (s : S) : W := s.property.choose
  have ha (s : S) : shape (a s) = s.val := s.property.choose_spec
  have hcut (s : S) : ∃ χ : E.continuousCore,
      (∀ x ∉ wordNeighborhoodOpen (a s).2 (k + 1), χ.val x = 0) ∧
      (∀ x ∈ wordCellUnion (cellNeighborhood (a s).2 k), χ.val x = 1) ∧
      (∀ x, χ.val x ∈ Icc (0 : ℝ) 1) :=
    E.exists_core_cutoff (isOpen_wordNeighborhoodOpen (a s).2 _) (isClosed_wordCellUnion _)
      (wordCellUnion_neighborhood_subset_open_succ (a s).2)
  choose χ hχ0 hχ1 hχ01 using hcut
  let e (s : S) (v : Fin (a s).1 → Fin 8) :=
    (E.energy (E.pullbackWord (List.ofFn v) (E.continuousCoreToDomain (χ s))) : ℝ)
  let T := ∑ s : S, ∑ v, e s v
  have he (s : S) (v : Fin (a s).1 → Fin 8) : 0 ≤ e s v := NNReal.coe_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg (fun s _ ↦ Finset.sum_nonneg (fun v _ ↦ he s v))
  let N : ℝ := ((2 * (k + 2) + 1) ^ 2 : ℕ)
  let C := 1 + N * T
  have hC : 0 < C := add_pos_of_pos_of_nonneg one_pos (mul_nonneg (Nat.cast_nonneg _) hT)
  refine ⟨C, hC, fun n w ↦ ?_⟩
  let s : S := ⟨shape ⟨n, w⟩, mem_range_self _⟩
  have hs : neighborhoodShape w (k + 2) = neighborhoodShape (a s).2 (k + 2) := (ha s).symm
  obtain ⟨g, hg0, hg1, hg01, hg, hzero⟩ := E.exists_transported_neighborhood_cutoff w (a s).2 hs
    (χ s) (hχ0 s) (hχ1 s) (hχ01 s)
  refine ⟨g, hg0, hg1, hg01, ?_⟩
  rw [E.energy_eq_sum_words n, mul_comm C]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg E.isScalingFactor_scalingFactor.1.le _)
  let A := cellNeighborhood w (k + 2)
  let eg (v : Fin n → Fin 8) :=
    (E.energy (E.pullbackWord (List.ofFn v) (E.continuousCoreToDomain g)) : ℝ)
  have he' (v : Fin n → Fin 8) (hv : v ∈ A) : eg v ≤ T := by
    let v' := (neighborhoodEquiv w (a s).2 hs ⟨v, hv⟩).val
    have hq : eg v = e s v' := by
      dsimp only [eg, e, v']
      rw [← E.continuousCoreToDomain_wordPullbackCore, hg ⟨v, hv⟩,
        E.continuousCoreToDomain_wordPullbackCore]
    rw [hq]
    exact (Finset.single_le_sum (f := e s) (fun b _ ↦ he s b) (Finset.mem_univ v')).trans
      (Finset.single_le_sum (f := fun t ↦ ∑ b, e t b)
        (fun t _ ↦ Finset.sum_nonneg (fun b _ ↦ he t b)) (Finset.mem_univ s))
  have hzer (v : Fin n → Fin 8) (hv : v ∉ A) : eg v = 0 := by
    have h0 : E.energy 0 = 0 := (E.zero_iff_constant 0).mpr ⟨0, by
      apply Lp.ext
      exact (Lp.coeFn_zero _ _ _).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure 0).symm⟩
    dsimp only [eg]
    rw [← E.continuousCoreToDomain_wordPullbackCore, hzero v hv, map_zero, h0, NNReal.coe_zero]
  have hs' := Finset.sum_subset (f := eg) (Finset.subset_univ A) (fun v _ hv ↦ hzer v hv)
  change ∑ v, eg v ≤ C
  rw [← hs']
  calc
    _ ≤ ∑ _ ∈ A, T := Finset.sum_le_sum he'
    _ = (A.card : ℝ) * T := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * T := mul_le_mul_of_nonneg_right (by
      dsimp only [A, N]
      exact_mod_cast card_cellNeighborhood_le w (k + 2)) hT
    _ ≤ C := le_add_of_nonneg_left zero_le_one

end CarpetEnergy.SelfSimilarPEnergy
