import EnergyNeighborhoodPoincare
import EnergyCellHarmonicReplacement
import CarpetNeighborhoodRescaling

/-!
# Poincaré inequality with zero exterior values

One more neighborhood step reaches an exterior cell whenever the
original neighborhood is proper. Its zero mean provides an anchor for
the neighborhood Poincaré estimate.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

theorem cellNeighborhood_subset_add {n a b : ℕ} {u w : Fin n → Fin 8}
    (h : w ∈ cellNeighborhood u a) : cellNeighborhood w b ⊆ cellNeighborhood u (a + b) := by
  induction b with
  | zero =>
    intro x hx
    simpa only [Finset.mem_singleton.mp hx, Nat.add_zero] using h
  | succ b ih =>
    intro x hx
    obtain ⟨v, hv, hnear⟩ := mem_cellNeighborhood_succ.mp hx
    exact mem_cellNeighborhood_succ.mpr ⟨v, ih hv, hnear⟩

theorem exists_exterior_mem_cellNeighborhood_succ {n k : ℕ} (w : Fin n → Fin 8)
    (h : cellNeighborhood w k ≠ Finset.univ) :
    ∃ u ∈ cellNeighborhood w (k + 1), u ∉ cellNeighborhood w k := by
  classical
  by_contra! hn
  have he : cellNeighborhood w (k + 1) = cellNeighborhood w k :=
    Finset.Subset.antisymm hn (cellNeighborhood_subset_succ w)
  let S := wordCellUnion (cellNeighborhood w k)
  have hs : S = wordNeighborhoodOpen w (k + 1) := le_antisymm
    (wordCellUnion_neighborhood_subset_open_succ w) (by
      simpa only [he] using wordNeighborhoodOpen_subset (r := k + 1) w)
  have hS : IsClopen S := ⟨isClosed_wordCellUnion _, hs ▸ isOpen_wordNeighborhoodOpen w (k + 1)⟩
  have heq := hS.eq_univ ⟨_, mem_iUnion.2 ⟨w, mem_iUnion.2
    ⟨self_mem_cellNeighborhood w k, mem_range_self (bottomPoint 0)⟩⟩⟩
  have hall : ∀ v : Fin n → Fin 8, v ∈ cellNeighborhood w k := by
    intro v
    by_contra hv
    have hv' : v ∉ cellNeighborhood w (k + 1) := by rwa [he]
    have hmem : wordMap (List.ofFn v) (bottomPoint 0) ∈ wordNeighborhoodOpen w (k + 1) := by
      rw [← hs, heq]
      exact mem_univ _
    exact (wordMap_notMem_wordNeighborhoodOpen hv' _) hmem
  exact h (Finset.eq_univ_iff_forall.mpr hall)

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Lemma 4.4 with an almost-everywhere zero condition on every exterior
cell, and a constant uniform at each fixed neighborhood radius. -/
theorem exists_poincare_of_zero_exterior_neighborhood (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8),
      cellNeighborhood w k ≠ Finset.univ → ∀ f : E.domain,
        (∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w k)ᶜ),
          (f : CarpetLp p) x = 0) →
        ‖(f : CarpetLp p)‖ ^ p ≤ C * (8 * E.scalingFactor)⁻¹ ^ n *
          E.cellUnionEnergy (cellNeighborhood w k) f := by
  classical
  obtain ⟨C, hC, hpi⟩ := E.exists_neighborhood_poincare ((k + 1) + k)
  refine ⟨C, hC, fun n w hproper f hf ↦ ?_⟩
  let S := cellNeighborhood w k
  obtain ⟨u, hu, huS⟩ := exists_exterior_mem_cellNeighborhood_succ w hproper
  let T := cellNeighborhood u ((k + 1) + k)
  have hST : S ⊆ T := cellNeighborhood_subset_add (mem_cellNeighborhood_symm hu)
  let z : E.domain := ⟨constantLp p 0, E.constant_mem 0⟩
  change (f : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion Sᶜ)] (fun _ ↦ (0 : ℝ)) at hf
  have hfz : (f : CarpetLp p) =ᵐ[carpetMeasure.restrict (wordCellUnion Sᶜ)] (z : CarpetLp p) :=
    hf.trans ((Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (0 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)).symm
  have hcell (v : Fin n → Fin 8) (hv : v ∉ S) :
      E.pullbackWord (List.ofFn v) f = E.pullbackWord (List.ofFn v) z := by
    apply E.pullbackWord_eq_of_ae_eq_on_cell
    refine hfz.filter_mono (ae_mono (Measure.restrict_mono ?_ le_rfl))
    intro x hx
    exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨Finset.mem_compl.mpr hv, hx⟩⟩
  have hz (v : Fin n → Fin 8) :
      (E.pullbackWord (List.ofFn v) z : CarpetLp p) =ᵐ[carpetMeasure] (fun _ ↦ (0 : ℝ)) :=
    (E.pullbackWord_isLpPullback (List.ofFn v) z).trans
      ((quasiMeasurePreserving_wordMap (List.ofFn v)).ae_eq_comp
        (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure 0))
  have he (v : Fin n → Fin 8) (hv : v ∉ S) : E.energy (E.pullbackWord (List.ofFn v) f) = 0 := by
    apply (E.zero_iff_constant _).mpr
    refine ⟨0, Lp.ext ?_⟩
    rw [hcell v hv]
    exact (hz v).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (0 : ℝ)).symm
  have hm : E.wordMean (List.ofFn u) f = 0 := by
    unfold wordMean
    rw [hcell u huS, integral_congr_ae (hz u), integral_zero]
  have hsum : (∑ v ∈ T, (E.energy (E.pullbackWord (List.ofFn v) f) : ℝ)) =
      ∑ v ∈ S, (E.energy (E.pullbackWord (List.ofFn v) f) : ℝ) := by
    symm
    apply Finset.sum_subset hST
    intro v _ hv
    rw [he v hv, NNReal.coe_zero]
  have hp := zero_lt_one.trans E.one_lt_p
  have hInt : Integrable (fun x ↦ |(f : CarpetLp p) x| ^ p) carpetMeasure := by
    have hh := (Lp.memLp (f : CarpetLp p)).integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using hh
  have hzero : ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion T)ᶜ, |(f : CarpetLp p) x| ^ p = 0 := by
    have hsub : (wordCellUnion T)ᶜ ⊆ wordCellUnion Sᶜ := by
      intro x hx
      obtain ⟨v, hv⟩ := exists_wordMap_range n x
      have hvS : v ∉ S := fun h ↦ hx (mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hST h, hv⟩⟩)
      exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨Finset.mem_compl.mpr hvS, hv⟩⟩
    filter_upwards [hf.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))] with x hx
    rw [hx, abs_zero, Real.zero_rpow hp.ne']
  have hsplit := integral_add_compl (measurableSet_wordCellUnion T) hInt
  rw [integral_congr_ae hzero, integral_zero, add_zero, integral_abs_rpow_eq_norm_rpow hp] at hsplit
  have hbound := hpi n u f
  rw [hm, hsum] at hbound
  simp only [sub_zero] at hbound
  rw [← hsplit]
  refine hbound.trans_eq ?_
  unfold cellUnionEnergy
  rw [mul_inv, mul_pow]
  have hρ : E.scalingFactor ≠ 0 := E.isScalingFactor_scalingFactor.1.ne'
  let B := ∑ v ∈ S, (E.energy (E.pullbackWord (List.ofFn v) f) : ℝ)
  change C * (8 : ℝ)⁻¹ ^ n * B =
    C * ((8 : ℝ)⁻¹ ^ n * E.scalingFactor⁻¹ ^ n) * (E.scalingFactor ^ n * B)
  calc
    _ = C * (8 : ℝ)⁻¹ ^ n * B * (E.scalingFactor⁻¹ ^ n * E.scalingFactor ^ n) := by
      rw [← mul_pow, inv_mul_cancel₀ hρ, one_pow, mul_one]
    _ = _ := by ring

end SelfSimilarPEnergy

end CarpetEnergy
