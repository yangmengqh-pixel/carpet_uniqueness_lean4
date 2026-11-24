import EnergyBufferedHarmonicBound
import EnergyNeighborhoodOscillation
import EssentialOscillationIteration

/-!
# Iterated Harnack bounds in nested neighborhoods

Starting two fixed scale steps inside an interior neighborhood
gives an initial bound. Successive finer neighborhoods contract
the essential range to one value at the center.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

def harmonicOscillationLevel (n L k : ℕ) : ℕ := (n + L) + L + L * k

noncomputable def harmonicOscillationNeighborhood (n L : ℕ) (x : CarpetPoints) (k : ℕ) :
    Set CarpetPoints :=
  wordCellUnion (cellNeighborhood (centerWord (harmonicOscillationLevel n L k) x) 2)

noncomputable def harnackOscillationFactor (H : ℝ) : ℝ :=
  max ((H - 1) / (H + 1)) (1 / 2)

theorem harnackOscillationFactor_nonneg (H : ℝ) : 0 ≤ harnackOscillationFactor H :=
  (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (le_max_right _ _)

theorem harnackOscillationFactor_lt_one {H : ℝ} (hH : 1 ≤ H) : harnackOscillationFactor H < 1 := by
  apply max_lt
  · apply (div_lt_iff₀ (by linarith : 0 < H + 1)).mpr
    linarith
  · norm_num

theorem carpetMeasure_wordCellUnion_cellNeighborhood_ne_zero {n k : ℕ} (w : Fin n → Fin 8) :
    carpetMeasure (wordCellUnion (cellNeighborhood w k)) ≠ 0 := by
  have hs : range (wordMap (List.ofFn w)) ⊆ wordCellUnion (cellNeighborhood w k) :=
    fun _ hx ↦ mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨self_mem_cellNeighborhood w k, hx⟩⟩
  have hle := measure_mono (μ := carpetMeasure) hs
  rw [carpetMeasure_range_wordMap] at hle
  exact ne_of_gt ((pos_iff_ne_zero.mpr (pow_ne_zero _
    (ENNReal.inv_ne_zero.mpr (by simp)))).trans_le hle)

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 2900000 in
/-- Conditional on Harnack, the essential value intervals in the
successive cell neighborhoods have geometrically shrinking widths. -/
theorem exists_harmonic_essential_interval_cascade {H : ℝ} (hH : 1 ≤ H)
    (hHar : E.HasNeighborhoodHarnack H)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ))) :
    ∃ L : ℕ, 0 < L ∧ ∃ C > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8),
      Disjoint (wordCellUnion (cellNeighborhood w 3)) carpetOuterBoundary →
      ∀ f : E.domain, E.IsInteriorHarmonic f →
        let m := E.wordMean (List.ofFn w) f
        let R := C * ((E.scalingFactor ^ n)⁻¹ * E.cellUnionEnergy (cellNeighborhood w 3) f) ^ p⁻¹
        ∀ x ∈ wordCellUnion (cellNeighborhood w 2),
          let μ (k : ℕ) := carpetMeasure.restrict (harmonicOscillationNeighborhood n L x k)
          let a (k : ℕ) := essInf (f : CarpetLp p) (μ k)
          let b (k : ℕ) := essSup (f : CarpetLp p) (μ k)
          (∀ k, ∀ᵐ y ∂μ k, (f : CarpetLp p) y ∈ Icc (a k) (b k)) ∧
          (∀ k, m - R ≤ a k ∧ b k ≤ m + R) ∧
          (∀ k, b k - a k ≤ harnackOscillationFactor H ^ k * (2 * R)) ∧
          ∃! z : ℝ, ∀ k, z ∈ Icc (a k) (b k) := by
  obtain ⟨L, hL₀, hL⟩ := exists_uniform_wordNeighborhood_stride
  obtain ⟨C, hC, hbound⟩ := E.exists_centered_bound_on_buffered_fine_neighborhood hH hHar hG L
  refine ⟨L, hL₀, C, hC, fun n w hw f hf ↦ ?_⟩
  intro m R x hx
  let W := wordCellUnion (cellNeighborhood w 3)
  let Q := centerWord (n + L) x
  have hFine : wordCellUnion (cellNeighborhood Q 3) ⊆ W := by
    refine (fine_wordNeighborhood_subset_open_succ (k := 2) (j := 3) w Q hx
      (mem_centerWord (n + L) x) ?_).trans (wordNeighborhoodOpen_subset w)
    norm_num
    exact hL n
  let S (k : ℕ) := harmonicOscillationNeighborhood n L x k
  let T (k : ℕ) := wordCellUnion (cellNeighborhood (centerWord (harmonicOscillationLevel n L k) x) 3)
  have hST (k : ℕ) : S k ⊆ T k := wordCellUnion_mono (cellNeighborhood_subset_succ _)
  have hfirst : T 0 ⊆ wordCellUnion (cellNeighborhood Q 2) := by
    change wordCellUnion (cellNeighborhood (centerWord ((n + L) + L) x) 3) ⊆ _
    exact fine_centerWord_neighborhood_subset (n + L) L x (hL (n + L))
  have hstep (k : ℕ) : T (k + 1) ⊆ S k := by
    have he : harmonicOscillationLevel n L (k + 1) = harmonicOscillationLevel n L k + L := by
      simp only [harmonicOscillationLevel, Nat.mul_succ, add_assoc]
    change wordCellUnion (cellNeighborhood (centerWord (harmonicOscillationLevel n L (k + 1)) x) 3) ⊆
      wordCellUnion (cellNeighborhood (centerWord (harmonicOscillationLevel n L k) x) 2)
    rw [he]
    exact fine_centerWord_neighborhood_subset (harmonicOscillationLevel n L k) L x
      (hL (harmonicOscillationLevel n L k))
  have hW (k : ℕ) : T k ⊆ W := by
    induction k with
    | zero => exact hfirst.trans ((wordCellUnion_mono (cellNeighborhood_subset_succ Q)).trans hFine)
    | succ k ih => exact (hstep k).trans ((hST k).trans ih)
  let μ (k : ℕ) := carpetMeasure.restrict (S k)
  have hμ : Antitone μ := antitone_nat_of_succ_le fun k ↦
    Measure.restrict_mono ((hST (k + 1)).trans (hstep k)) le_rfl
  have hμ₀ (k : ℕ) : μ k ≠ 0 := by
    intro he
    have hm := congrArg (fun ν : Measure CarpetPoints ↦ ν univ) he
    change (carpetMeasure.restrict (S k)) univ = 0 at hm
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hm
    exact carpetMeasure_wordCellUnion_cellNeighborhood_ne_zero _ hm
  have hbounded : ∀ᵐ y ∂μ 0, (f : CarpetLp p) y ∈ Icc (m - R) (m + R) := by
    have hh := hbound n w Q hw hFine f hf
    filter_upwards [hh.filter_mono (ae_mono (Measure.restrict_mono ((hST 0).trans hfirst) le_rfl))]
      with y hy
    have hb := abs_le.mp hy
    exact ⟨by linarith only [hb.1], by linarith only [hb.2]⟩
  let δ := harnackOscillationFactor H
  have hOsc (k : ℕ) (a b : ℝ) (hb : ∀ᵐ y ∂μ k, (f : CarpetLp p) y ∈ Icc a b) :
      essSup (f : CarpetLp p) (μ (k + 1)) - essInf (f : CarpetLp p) (μ (k + 1)) ≤ δ * (b - a) := by
    let z := centerWord (harmonicOscillationLevel n L (k + 1)) x
    have hz : Disjoint (T (k + 1)) carpetOuterBoundary := hw.mono_left (hW (k + 1))
    have hmin := IsInteriorHarmonic.minimizesWithExterior_wordCells E (cellNeighborhood z 3) hz hf
    have hh := E.neighborhood_essOsc_le_of_harnack hH hHar z hz f hmin
      (hb.filter_mono (ae_mono (Measure.restrict_mono (hstep k) le_rfl)))
    have hwidth : 0 ≤ b - a := by
      let : NeZero (μ k) := ⟨hμ₀ k⟩
      obtain ⟨_, hy⟩ := hb.exists
      exact sub_nonneg.mpr (hy.1.trans hy.2)
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hwidth)
  obtain ⟨hae, hwid, huniq⟩ := existsUnique_mem_essential_intervals_of_oscillation_iteration
    μ hμ hμ₀ (f : CarpetLp p) (harnackOscillationFactor_nonneg H)
    (harnackOscillationFactor_lt_one hH) hbounded hOsc
  refine ⟨hae, ?_, ?_, huniq⟩
  · intro k
    let : NeZero (μ k) := ⟨hμ₀ k⟩
    have hh := ae_interval_between_essBounds
      (hbounded.filter_mono (ae_mono (hμ (Nat.zero_le k))))
    exact ⟨hh.2.1, hh.2.2.1⟩
  · intro k
    exact (hwid k).trans_eq (by ring)

end SelfSimilarPEnergy

end CarpetEnergy
