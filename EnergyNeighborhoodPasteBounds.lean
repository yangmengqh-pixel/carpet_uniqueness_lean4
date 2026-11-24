import EnergyNeighborhoodPasting
import EnergyComparison

/-!
# Graph bounds for pasted neighborhood profiles
-/

open MeasureTheory Set
open scoped BigOperators

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1000000 in
theorem exists_graph_bound_of_cellwise_paste {n r : ℕ} (w : Fin n → Fin 8)
    (k : E.continuousCore) {B : ℝ} (hB : 0 ≤ B) :
    ∃ R : ℝ, ∀ (P : {a // a ∈ cellNeighborhood w r} → E.continuousCore) (g : E.continuousCore),
      (∀ a, E.rootSeminorm (E.continuousCoreToDomain (P a)) ≤ B ∧ ‖(P a).val‖ ≤ B) →
      (∀ a : {a // a ∈ cellNeighborhood w r},
        E.wordPullbackCore (List.ofFn a.val) g =
          E.mulCore (E.wordPullbackCore (List.ofFn a.val) k) (P a)) →
      (∀ v ∉ cellNeighborhood w r, E.wordPullbackCore (List.ofFn v) g = 0) →
      E.graphSeminorm (E.continuousCoreToDomain g) ≤ R := by
  classical
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp := zero_lt_one.trans E.one_lt_p
  let L := ‖k.val‖ * B
  let K := ∑ a : Fin n → Fin 8,
    E.rootSeminorm (E.continuousCoreToDomain (E.wordPullbackCore (List.ofFn a) k))
  let S := (‖k.val‖ + B) * (K + B)
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ ↦ apply_nonneg _ _)
  have hS : 0 ≤ S := mul_nonneg (add_nonneg (norm_nonneg _) hB) (add_nonneg hK hB)
  let W := E.scalingFactor ^ n * ((Fintype.card (Fin n → Fin 8) : ℝ) * S ^ p)
  refine ⟨(W + L ^ p) ^ p⁻¹, ?_⟩
  intro P g hP hg hg0
  have hκ (a : Fin n → Fin 8) : ‖(E.wordPullbackCore (List.ofFn a) k).val‖ ≤ ‖k.val‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    rw [E.wordPullbackCore_apply]
    exact k.val.norm_coe_le_norm _
  have hκroot (a : Fin n → Fin 8) :
      E.rootSeminorm (E.continuousCoreToDomain (E.wordPullbackCore (List.ofFn a) k)) ≤ K :=
    Finset.single_le_sum
      (f := fun b ↦ E.rootSeminorm (E.continuousCoreToDomain (E.wordPullbackCore (List.ofFn b) k)))
      (fun _ _ ↦ apply_nonneg E.rootSeminorm _) (Finset.mem_univ a)
  have hb (a : Fin n → Fin 8) :
      E.rootSeminorm (E.continuousCoreToDomain (E.wordPullbackCore (List.ofFn a) g)) ≤ S := by
    by_cases ha : a ∈ cellNeighborhood w r
    · rw [hg ⟨a, ha⟩]
      let k' := E.wordPullbackCore (List.ofFn a) k
      let f' := P ⟨a, ha⟩
      have h' : E.rootSeminorm (E.continuousCoreToDomain f') ≤ B ∧ ‖f'.val‖ ≤ B := hP ⟨a, ha⟩
      have he := E.rootSeminorm_mulCore_le k' f'
      exact he.trans (mul_le_mul (add_le_add (hκ a) h'.2)
        (add_le_add (hκroot a) h'.1) (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
        (add_nonneg (norm_nonneg _) hB))
    · rw [hg0 a ha, map_zero, map_zero]
      exact hS
  have hEn : (E.energy (E.continuousCoreToDomain g) : ℝ) ≤ W := by
    rw [E.energy_eq_sum_words n]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg E.isScalingFactor_scalingFactor.1.le _)
    calc
      _ ≤ ∑ _ : Fin n → Fin 8, S ^ p := by
        apply Finset.sum_le_sum
        intro a _
        have he := Real.rpow_le_rpow (apply_nonneg E.rootSeminorm _) (hb a) hp.le
        rw [E.rootSeminorm_apply, Real.rpow_inv_rpow (NNReal.coe_nonneg _) hp.ne',
          E.continuousCoreToDomain_wordPullbackCore] at he
        exact he
      _ = _ := by simp
  have hL : ‖(E.continuousCoreToDomain g : CarpetLp p)‖ ≤ L := by
    have hL0 : 0 ≤ L := mul_nonneg (norm_nonneg _) hB
    apply norm_carpetLp_le_of_ae_bound _ hL0
    change ∀ᵐ x ∂carpetMeasure, ‖continuousLp p g.val x‖ ≤ L
    filter_upwards [continuousLp_ae_eq p g.val] with x hx
    rw [hx]
    obtain ⟨a, y, rfl⟩ := exists_wordMap_range n x
    rw [← E.wordPullbackCore_apply]
    by_cases ha : a ∈ cellNeighborhood w r
    · rw [hg ⟨a, ha⟩, E.mulCore_apply, norm_mul]
      exact mul_le_mul (((E.wordPullbackCore (List.ofFn a) k).val.norm_coe_le_norm y).trans (hκ a))
        (((P ⟨a, ha⟩).val.norm_coe_le_norm y).trans (hP ⟨a, ha⟩).2)
        (norm_nonneg _) (norm_nonneg _)
    · rw [hg0 a ha]
      change ‖(0 : ℝ)‖ ≤ L
      rw [norm_zero]
      exact hL0
  rw [E.graphSeminorm_apply, energyGraphNorm]
  exact Real.rpow_le_rpow
    (add_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
    (add_le_add hEn (Real.rpow_le_rpow (norm_nonneg _) hL hp.le)) (inv_nonneg.mpr hp.le)

theorem exists_graph_bound_of_neighborhood_paste {n r : ℕ} (w : Fin n → Fin 8)
    (k : E.continuousCore) {B : ℝ} (hB : 0 ≤ B) :
    ∃ R : ℝ, ∀ {m : ℕ} (u : Fin m → Fin 8)
      (h : neighborhoodShape w r = neighborhoodShape u r) (f g : E.continuousCore),
      (∀ a : {a // a ∈ cellNeighborhood u r},
        let z := E.wordPullbackCore (List.ofFn a.val) f
        E.rootSeminorm (E.continuousCoreToDomain z) ≤ B ∧ ‖z.val‖ ≤ B) →
      (∀ a : {a // a ∈ cellNeighborhood w r},
        E.wordPullbackCore (List.ofFn a.val) g =
          E.mulCore (E.wordPullbackCore (List.ofFn a.val) k)
            (E.wordPullbackCore (List.ofFn (neighborhoodEquiv w u h a).val) f)) →
      (∀ v ∉ cellNeighborhood w r, E.wordPullbackCore (List.ofFn v) g = 0) →
      E.graphSeminorm (E.continuousCoreToDomain g) ≤ R := by
  obtain ⟨R, hR⟩ := E.exists_graph_bound_of_cellwise_paste w k hB
  refine ⟨R, ?_⟩
  intro m u h f g hf hg hzero
  exact hR (fun a ↦ E.wordPullbackCore (List.ofFn (neighborhoodEquiv w u h a).val) f)
    g (fun a ↦ hf (neighborhoodEquiv w u h a)) hg hzero

end CarpetEnergy.SelfSimilarPEnergy
