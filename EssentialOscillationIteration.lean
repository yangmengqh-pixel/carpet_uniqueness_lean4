import EssentialOscillation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact

/-!
# Iterating essential oscillation bounds

Nested positive-measure regions give nested essential range
intervals. A fixed contraction factor makes their intersection a
singleton and gives a quantitative bound on every interval's width.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace CarpetEnergy

theorem ae_interval_between_essBounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [NeZero μ] {f : X → ℝ} {a b : ℝ}
    (h : ∀ᵐ x ∂μ, f x ∈ Icc a b) :
    (∀ᵐ x ∂μ, f x ∈ Icc (essInf f μ) (essSup f μ)) ∧
      a ≤ essInf f μ ∧ essSup f μ ≤ b ∧ essInf f μ ≤ essSup f μ := by
  have hl : IsBoundedUnder (· ≥ ·) (ae μ) f := ⟨a, h.mono fun _ hx ↦ hx.1⟩
  have hu : IsBoundedUnder (· ≤ ·) (ae μ) f := ⟨b, h.mono fun _ hx ↦ hx.2⟩
  have hlow := ae_essInf_le (f := f) (μ := μ) hl
  have hhigh := ae_le_essSup (f := f) (μ := μ) hu
  have hb : ∀ᵐ x ∂μ, f x ∈ Icc (essInf f μ) (essSup f μ) := hlow.and hhigh
  obtain ⟨_, hx⟩ := hb.exists
  exact ⟨hb, le_essInf_of_ae_le a (h.mono fun _ hx ↦ hx.1) hu.isCoboundedUnder_flip,
    essSup_le_of_ae_le b (h.mono fun _ hx ↦ hx.2) hl.isCoboundedUnder_flip, hx.1.trans hx.2⟩

set_option maxHeartbeats 1300000 in
theorem existsUnique_mem_essential_intervals_of_oscillation_iteration
    {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X)
    (hμ : Antitone μ) (hμ₀ : ∀ n, μ n ≠ 0) (f : X → ℝ)
    {a b δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (h : ∀ᵐ x ∂μ 0, f x ∈ Icc a b)
    (hstep : ∀ (n : ℕ) (l r : ℝ), (∀ᵐ x ∂μ n, f x ∈ Icc l r) →
      essSup f (μ (n + 1)) - essInf f (μ (n + 1)) ≤ δ * (r - l)) :
    (∀ n, ∀ᵐ x ∂μ n, f x ∈ Icc (essInf f (μ n)) (essSup f (μ n))) ∧
      (∀ n, essSup f (μ n) - essInf f (μ n) ≤ δ ^ n * (b - a)) ∧
      ∃! z : ℝ, ∀ n, z ∈ Icc (essInf f (μ n)) (essSup f (μ n)) := by
  let L (n : ℕ) := essInf f (μ n)
  let U (n : ℕ) := essSup f (μ n)
  let S (n : ℕ) := Icc (L n) (U n)
  have hbounds (n : ℕ) :
      (∀ᵐ x ∂μ n, f x ∈ S n) ∧ a ≤ L n ∧ U n ≤ b ∧ L n ≤ U n := by
    let : NeZero (μ n) := ⟨hμ₀ n⟩
    exact ae_interval_between_essBounds (h.filter_mono (ae_mono (hμ (Nat.zero_le n))))
  have hwidth (n : ℕ) : U n - L n ≤ δ ^ n * (b - a) := by
    induction n with
    | zero =>
      rw [pow_zero, one_mul]
      linarith only [(hbounds 0).2.1, (hbounds 0).2.2.1]
    | succ n ih =>
      have h := hstep n (L n) (U n) (hbounds n).1
      exact (h.trans (mul_le_mul_of_nonneg_left ih hδ₀)).trans_eq (by rw [pow_succ]; ring)
  refine ⟨fun n ↦ (hbounds n).1, hwidth, ?_⟩
  have hS : Antitone S := by
    intro n m hnm
    let : NeZero (μ m) := ⟨hμ₀ m⟩
    have hn := (hbounds n).1.filter_mono (ae_mono (hμ hnm))
    have hm := ae_interval_between_essBounds hn
    exact Icc_subset_Icc hm.2.1 hm.2.2.1
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
    (fun n ↦ hS (Nat.le_succ n)) (fun n ↦ nonempty_Icc.mpr (hbounds n).2.2.2) isCompact_Icc
      (fun _ ↦ isClosed_Icc)
  refine ⟨z, fun n ↦ mem_iInter.mp hz n, fun y hy ↦ ?_⟩
  have hle (n : ℕ) : |y - z| ≤ δ ^ n * (b - a) := by
    have hz' := mem_iInter.mp hz n
    refine (abs_le.mpr ⟨?_, ?_⟩).trans (hwidth n)
    · linarith only [(hy n).1, hz'.2]
    · linarith only [(hy n).2, hz'.1]
  have hzero : Tendsto (fun n ↦ δ ^ n * (b - a)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hδ₀ hδ₁).mul_const (b - a)
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds hzero (Eventually.of_forall hle)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

end CarpetEnergy
