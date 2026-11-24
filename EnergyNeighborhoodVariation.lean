import EnergyNeighborhoodPasting
import EnergyCompactCutoff
import EnergyClippedHarmonic

/-!
# Transferring harmonicity between equal-shape neighborhoods
-/

open Set
open scoped BigOperators

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem wordPullbackCore_add (c : List (Fin 8)) (f g : E.continuousCore) :
    E.wordPullbackCore c (f + g) = E.wordPullbackCore c f + E.wordPullbackCore c g := by
  apply Subtype.ext
  ext x
  rfl

/-- The sum of cell energy differences on a neighborhood accounts for
the entire variation when all other cell tests vanish. -/
private theorem normalized_energy_variation_eq_sum {n : ℕ} (s : Finset (Fin n → Fin 8))
    (f v : E.domain) (hv : ∀ a ∉ s, E.pullbackWord (List.ofFn a) v = 0) :
    (E.energy (f + v) : ℝ) - (E.energy f : ℝ) =
      E.scalingFactor ^ n * ∑ a ∈ s,
        ((E.energy (E.pullbackWord (List.ofFn a) (f + v)) : ℝ) -
          (E.energy (E.pullbackWord (List.ofFn a) f) : ℝ)) := by
  rw [E.energy_eq_sum_words n (f + v), E.energy_eq_sum_words n f, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ s)
  intro a _ ha
  rw [E.pullbackWord_add, hv a ha, add_zero, sub_self]

private theorem pullbackCore_eq_zero_of_vanishes {n r : ℕ} {w a : Fin n → Fin 8}
    (v : E.continuousCore) (hv : ∀ x ∉ wordNeighborhoodOpen w r, v.val x = 0)
    (ha : a ∉ cellNeighborhood w r) : E.wordPullbackCore (List.ofFn a) v = 0 := by
  apply Subtype.ext
  ext x
  exact hv _ (wordMap_notMem_wordNeighborhoodOpen ha x)

private theorem exists_neighborhood_test_cutoff {n : ℕ} (w : Fin n → Fin 8) :
    ∃ k : E.continuousCore, (∀ x ∉ wordNeighborhoodOpen w 3, k.val x = 0) ∧
      (∀ x ∈ wordCellUnion (cellNeighborhood w 1), k.val x = 1) := by
  have hsub : wordCellUnion (cellNeighborhood w 1) ⊆ wordNeighborhoodOpen w 3 := by
    refine Subset.trans ?_ (wordCellUnion_neighborhood_subset_open_succ (r := 2) w)
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    obtain ⟨ha1, ha⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨cellNeighborhood_mono w (by decide) ha1, ha⟩⟩
  obtain ⟨k, hk, hk1, _⟩ := E.exists_core_cutoff (isOpen_wordNeighborhoodOpen w 3)
    (isClosed_wordCellUnion _) hsub
  exact ⟨k, hk, hk1⟩

set_option maxHeartbeats 1500000 in
/-- A paste of a source harmonic profile is harmonic in the open
first neighborhood, provided the paste agrees with the corresponding
source profiles on its first-neighborhood cells. -/
theorem isHarmonicOn_of_neighborhood_pullbacks_domain {n m : ℕ} (w : Fin n → Fin 8)
    (u : Fin m → Fin 8) (h : neighborhoodShape w 3 = neighborhoodShape u 3)
    (f : E.domain) (g : E.continuousCore) (hf : E.IsInteriorHarmonic f)
    (hinterior : wordCellUnion (cellNeighborhood u 3) ⊆ carpetOuterBoundaryᶜ)
    (hmatching : ∀ a : {a // a ∈ cellNeighborhood w 3}, a.val ∈ cellNeighborhood w 1 →
      E.pullbackWord (List.ofFn a.val) (E.continuousCoreToDomain g) =
        E.pullbackWord (List.ofFn (neighborhoodEquiv w u h a).val) f) :
    E.IsHarmonicOn (wordNeighborhoodOpen w 1) g := by
  classical
  intro v hv
  obtain ⟨k, hk, hk1⟩ := E.exists_neighborhood_test_cutoff u
  obtain ⟨t, ht, ht0⟩ := E.exists_neighborhood_paste u w h.symm v k hk
  have ht' (a : {a // a ∈ cellNeighborhood w 3}) :
      E.wordPullbackCore (List.ofFn (neighborhoodEquiv w u h a).val) t =
        E.wordPullbackCore (List.ofFn a.val) v := by
    let b := neighborhoodEquiv w u h a
    have hb := ht b
    rw [neighborhoodEquiv_inverse_apply] at hb
    rw [hb]
    apply Subtype.ext
    ext x
    rw [E.mulCore_apply]
    by_cases ha : a.val ∈ cellNeighborhood w 1
    · have hb1 := neighborhoodEquiv_mem_cellNeighborhood w u h (by decide : 1 ≤ 3) a ha
      rw [E.wordPullbackCore_apply, hk1 _ (mem_iUnion.mpr ⟨b.val, mem_iUnion.mpr
        ⟨hb1, mem_range_self x⟩⟩), one_mul]
    · have hza := E.pullbackCore_eq_zero_of_vanishes v hv ha
      rw [hza]
      change _ * (0 : ℝ) = 0
      exact mul_zero _
  have htTrace : ∀ x ∈ carpetOuterBoundary, t.val x = 0 := by
    intro x hx
    obtain ⟨a, y, rfl⟩ := exists_wordMap_range m x
    have ha : a ∉ cellNeighborhood u 3 := by
      intro ha
      exact hinterior (mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, mem_range_self y⟩⟩) hx
    have hzero := congrArg (fun t : E.continuousCore ↦ t.val y) (ht0 a ha)
    exact hzero
  have hfv := hf t.val t.property htTrace
  let G := E.continuousCoreToDomain g
  let V := E.continuousCoreToDomain v
  let T := E.continuousCoreToDomain t
  have hdT (a : {a // a ∈ cellNeighborhood w 3}) :
      E.pullbackWord (List.ofFn (neighborhoodEquiv w u h a).val) T =
        E.pullbackWord (List.ofFn a.val) V := by
    simpa only [E.continuousCoreToDomain_wordPullbackCore] using
      congrArg E.continuousCoreToDomain (ht' a)
  let Δ {q : ℕ} (z s : E.domain) (a : Fin q → Fin 8) : ℝ :=
    (E.energy (E.pullbackWord (List.ofFn a) (z + s)) : ℝ) -
      (E.energy (E.pullbackWord (List.ofFn a) z) : ℝ)
  have hcell (a : {a // a ∈ cellNeighborhood w 3}) :
      Δ G V a.val = Δ f T (neighborhoodEquiv w u h a).val := by
    dsimp only [Δ]
    rw [E.pullbackWord_add, E.pullbackWord_add, hdT a]
    by_cases ha : a.val ∈ cellNeighborhood w 1
    · rw [hmatching a ha]
    · have hz : E.pullbackWord (List.ofFn a.val) V = 0 := by
        rw [← E.continuousCoreToDomain_wordPullbackCore, E.pullbackCore_eq_zero_of_vanishes v hv ha, map_zero]
      rw [hz, add_zero, add_zero, sub_self, sub_self]
  have hsum : (∑ a ∈ cellNeighborhood w 3, Δ G V a) =
      ∑ a ∈ cellNeighborhood u 3, Δ f T a := by
    calc
      _ = ∑ a : {a // a ∈ cellNeighborhood w 3}, Δ G V a.val :=
        Finset.sum_subtype (cellNeighborhood w 3) (fun _ ↦ Iff.rfl) (Δ G V)
      _ = ∑ a : {a // a ∈ cellNeighborhood u 3}, Δ f T a.val :=
        Fintype.sum_equiv (neighborhoodEquiv w u h) _ _ hcell
      _ = _ := (Finset.sum_subtype (cellNeighborhood u 3) (fun _ ↦ Iff.rfl) (Δ f T)).symm
  have hT (a : Fin m → Fin 8) (ha : a ∉ cellNeighborhood u 3) :
      E.pullbackWord (List.ofFn a) T = 0 := by
    rw [← E.continuousCoreToDomain_wordPullbackCore, ht0 a ha, map_zero]
  have hs := E.normalized_energy_variation_eq_sum (cellNeighborhood u 3) f T hT
  have hsrc : 0 ≤ ∑ a ∈ cellNeighborhood u 3, Δ f T a := by
    have hprod : 0 ≤ E.scalingFactor ^ m * ∑ a ∈ cellNeighborhood u 3, Δ f T a := by
      rw [← hs]
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr hfv)
    exact nonneg_of_mul_nonneg_right hprod (pow_pos E.isScalingFactor_scalingFactor.1 _)
  have hv0 (a : Fin n → Fin 8) (ha : a ∉ cellNeighborhood w 3) :
      E.pullbackWord (List.ofFn a) V = 0 := by
    simpa only [E.continuousCoreToDomain_wordPullbackCore, map_zero] using
      congrArg E.continuousCoreToDomain
        (E.pullbackCore_eq_zero_of_vanishes v hv (fun ha' ↦ ha (cellNeighborhood_mono w (by decide) ha')))
  have hd := E.normalized_energy_variation_eq_sum (cellNeighborhood w 3) G V hv0
  rw [map_add]
  change E.energy G ≤ E.energy (G + V)
  apply NNReal.coe_le_coe.mp
  apply sub_nonneg.mp
  rw [hd]
  change 0 ≤ E.scalingFactor ^ n * ∑ a ∈ cellNeighborhood w 3, Δ G V a
  exact mul_nonneg (pow_nonneg E.isScalingFactor_scalingFactor.1.le _) (by rwa [hsum])

theorem isHarmonicOn_of_neighborhood_pullbacks {n m : ℕ} (w : Fin n → Fin 8)
    (u : Fin m → Fin 8) (h : neighborhoodShape w 3 = neighborhoodShape u 3)
    (f g : E.continuousCore) (hf : E.IsInteriorHarmonic (E.continuousCoreToDomain f))
    (hinterior : wordCellUnion (cellNeighborhood u 3) ⊆ carpetOuterBoundaryᶜ)
    (hmatching : ∀ a : {a // a ∈ cellNeighborhood w 3}, a.val ∈ cellNeighborhood w 1 →
      E.wordPullbackCore (List.ofFn a.val) g =
        E.wordPullbackCore (List.ofFn (neighborhoodEquiv w u h a).val) f) :
    E.IsHarmonicOn (wordNeighborhoodOpen w 1) g := by
  apply E.isHarmonicOn_of_neighborhood_pullbacks_domain w u h _ g hf hinterior
  intro a ha
  simpa only [E.continuousCoreToDomain_wordPullbackCore] using
    congrArg E.continuousCoreToDomain (hmatching a ha)

end CarpetEnergy.SelfSimilarPEnergy
