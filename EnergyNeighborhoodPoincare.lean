import EnergyNeighborhoodMeans
import CarpetNeighborhoodMass
import CarpetCellAverages
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Neighborhood Poincaré estimates

The single-cell Poincaré estimate and the neighbor mean comparison
control the integral of the centered profile on the full neighborhood.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

theorem measure_restrict_wordCellUnion_eq_sum {n : ℕ} (μ : Measure CarpetPoints)
    (hμ : μ (carpetCellBoundary n) = 0) (S : Finset (Fin n → Fin 8)) :
    μ.restrict (wordCellUnion S) = ∑ w ∈ S, μ.restrict (range (wordMap (List.ofFn w))) := by
  ext A hA
  rw [Measure.restrict_apply hA, inter_comm A, measure_wordCellUnion_inter μ hμ S hA]
  simp only [FunLike.coe_sum, Finset.sum_apply, Measure.restrict_apply hA, inter_comm A]

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem integrable_abs_sub_const_rpow (hp : 0 < p) (f : CarpetLp p) (a : ℝ) :
    Integrable (fun x ↦ |f x - a| ^ p) carpetMeasure := by
  let g := f - constantLp p a
  have hg := (Lp.memLp g).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at hg
  apply hg.congr
  filter_upwards [Lp.coeFn_sub f (constantLp p a), Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a]
    with x hx ha
  change ‖g x‖ ^ p = _
  have hx' : g x = f x - constantLp p a x := hx
  have ha' : constantLp p a x = a := ha
  rw [hx', ha', Real.norm_eq_abs]

theorem abs_sub_rpow_le {p : ℝ} (hp : 1 ≤ p) (a b c : ℝ) :
    |a - c| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|a - b| ^ p + |b - c| ^ p) := by
  have he := abs_add_le (a - b) (b - c)
  rw [sub_add_sub_cancel] at he
  refine (Real.rpow_le_rpow (abs_nonneg _) he (zero_le_one.trans hp)).trans ?_
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    ⟨|a - b|, abs_nonneg _⟩ ⟨|b - c|, abs_nonneg _⟩ hp

set_option maxHeartbeats 1900000 in
/-- The oscillation in (4.11), with a uniform constant for every fixed
radius of the cell neighborhood. -/
theorem exists_neighborhood_poincare (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8) (f : E.domain),
      (∫ x in wordCellUnion (cellNeighborhood w k), |(f : CarpetLp p) x - E.wordMean (List.ofFn w) f| ^ p
        ∂carpetMeasure) ≤ C * ((8 : ℝ)⁻¹) ^ n *
          ∑ v ∈ cellNeighborhood w k, (E.energy (E.pullbackWord (List.ofFn v) f) : ℝ) := by
  obtain ⟨A, hA, hPI⟩ := E.exists_cell_poincare
  obtain ⟨B, hB, hMean⟩ := E.exists_neighborhood_wordMean_gap k
  let Q := (2 : ℝ) ^ (p - 1)
  have hQ : 0 < Q := Real.rpow_pos_of_pos (by norm_num) _
  let N := (2 * k + 1) ^ 2
  let C := Q * (A + (N : ℝ) * B)
  use C, mul_pos hQ (add_pos_of_pos_of_nonneg hA (mul_nonneg (Nat.cast_nonneg _) hB.le))
  intro n w f
  let S := cellNeighborhood w k
  let r := ((8 : ℝ)⁻¹) ^ n
  let m (u : Fin n → Fin 8) := E.wordMean (List.ofFn u) f
  let e (u : Fin n → Fin 8) := (E.energy (E.pullbackWord (List.ofFn u) f) : ℝ)
  let L := ∑ u ∈ S, e u
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ ↦ NNReal.coe_nonneg _)
  have hr : 0 ≤ r := by positivity
  have hm (u : Fin n → Fin 8) (hu : u ∈ S) : |m u - m w| ^ p ≤ B * L := by
    rw [abs_sub_comm (m u)]
    exact hMean n f w u hu
  have hcell (u : Fin n → Fin 8) (hu : u ∈ S) :
      (∫ x in range (wordMap (List.ofFn u)), |(f : CarpetLp p) x - m w| ^ p ∂carpetMeasure) ≤
        Q * (A * r * e u + r * (B * L)) := by
    let V := range (wordMap (List.ofFn u))
    have hInt : Integrable (fun x ↦ |(f : CarpetLp p) x - m u| ^ p) (carpetMeasure.restrict V) :=
      (integrable_abs_sub_const_rpow (zero_lt_one.trans E.one_lt_p) (f : CarpetLp p) (m u)).restrict
    have hfInt : Integrable (fun x ↦ |(f : CarpetLp p) x - m w| ^ p) (carpetMeasure.restrict V) :=
      (integrable_abs_sub_const_rpow (zero_lt_one.trans E.one_lt_p) (f : CarpetLp p) (m w)).restrict
    have h := integral_mono hfInt ((hInt.add (integrable_const _)).const_mul Q)
      (fun x ↦ abs_sub_rpow_le E.one_lt_p.le _ (m u) (m w))
    change (∫ x in V, |(f : CarpetLp p) x - m w| ^ p ∂carpetMeasure) ≤
      ∫ x in V, Q * (|(f : CarpetLp p) x - m u| ^ p + |m u - m w| ^ p) ∂carpetMeasure at h
    rw [integral_const_mul, integral_add hInt (integrable_const _), integral_const,
      Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
    have hmass : (carpetMeasure V).toReal = r := by
      dsimp only [V, r]
      rw [carpetMeasure_range_wordMap, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, List.length_ofFn]
    rw [hmass, smul_eq_mul] at h
    have hp (v : Fin n → Fin 8) :
        (∫ x in range (wordMap (List.ofFn v)), |(f : CarpetLp p) x - m v| ^ p ∂carpetMeasure) ≤
          A * r * e v := by
      have h := hPI (List.ofFn v) f
      rw [List.length_ofFn] at h
      exact h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (hp u) (mul_le_mul_of_nonneg_left (hm u hu) hr)) hQ.le)
  have hS : (S.card : ℝ) ≤ N := by exact_mod_cast card_cellNeighborhood_le w k
  have hInt : Integrable (fun x ↦ |(f : CarpetLp p) x - m w| ^ p) carpetMeasure :=
    integrable_abs_sub_const_rpow (zero_lt_one.trans E.one_lt_p) (f : CarpetLp p) (m w)
  change (∫ x in wordCellUnion S, |(f : CarpetLp p) x - m w| ^ p ∂carpetMeasure) ≤ C * r * L
  rw [measure_restrict_wordCellUnion_eq_sum carpetMeasure (carpetMeasure_carpetCellBoundary_eq_zero n),
    integral_finsetSum_measure (fun _ _ ↦ hInt.restrict)]
  calc
    _ ≤ ∑ u ∈ S, Q * (A * r * e u + r * (B * L)) := Finset.sum_le_sum hcell
    _ = Q * (A * r * L + (S.card : ℝ) * (r * (B * L))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * r * L := by
      have hh := mul_le_mul_of_nonneg_right hS (mul_nonneg hr (mul_nonneg hB.le hL))
      dsimp only [C]
      exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl hh) hQ.le).trans_eq (by ring)

end SelfSimilarPEnergy

end CarpetEnergy
