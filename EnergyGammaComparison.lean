import EnergyGammaCompactness
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Γ-limits of weakly monotone energies

When the energy at an earlier level is at most a fixed multiple of the
energy at every later level, the supremum functional agrees up to this
factor with every subsequential Γ-limit. In particular, both have the
same finite-energy domain.
-/

open Filter Function Set TopologicalSpace
open scoped ENNReal Topology

namespace CarpetEnergy

variable {X : Type*} [TopologicalSpace X]

theorem IsGammaLimit.le_iSup {Fₙ : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞}
    (hF : IsGammaLimit Fₙ F) (x : X) : F x ≤ ⨆ n, Fₙ n x := by
  apply le_of_forall_lt
  intro a ha
  obtain ⟨b, hab, hb⟩ := exists_between ha
  obtain ⟨U, hU, hlow⟩ := hF.lower x b hb
  obtain ⟨n, hn⟩ := hlow.exists
  exact (hab.trans_le (hn x (mem_of_mem_nhds hU))).trans_le (_root_.le_iSup (fun n ↦ Fₙ n x) n)

theorem IsGammaLimit.le_of_eventually_le_mul {Fₙ : ℕ → X → ℝ≥0∞} {F G : X → ℝ≥0∞}
    (hF : IsGammaLimit Fₙ F) (hG : LowerSemicontinuous G) (C : ℝ≥0∞) (htop : C ≠ ∞)
    (h : ∀ᶠ n in atTop, ∀ x, G x ≤ C * Fₙ n x) (x : X) :
    G x ≤ C * F x := by
  by_cases hzero : C = 0
  · obtain ⟨n, hn⟩ := h.exists
    simpa only [hzero, zero_mul] using hn x
  by_contra! hx
  have hdiv : F x < G x / C := ENNReal.lt_div_iff_mul_lt (Or.inl hzero) (Or.inl htop) |>.2 (by simpa [mul_comm] using hx)
  obtain ⟨a, hxa, ha⟩ := exists_between hdiv
  have hCa : C * a < G x := by
    have := (ENNReal.lt_div_iff_mul_lt (Or.inl hzero) (Or.inl htop)).1 ha
    simpa only [mul_comm] using this
  have hU := hG x (C * a) hCa
  obtain ⟨n, hn, z, hz, hlt⟩ := (h.and (hF.recovery x {z | C * a < G z} hU a hxa)).exists
  exact hz.not_ge ((hn z).trans (by gcongr))

/-- Comparison with the supremum of all levels under weak monotonicity. -/
theorem IsGammaLimit.iSup_le_mul_of_weakMonotone {Fₙ : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞}
    {j : ℕ → ℕ} (hj : StrictMono j) (hF : IsGammaLimit (fun n ↦ Fₙ (j n)) F)
    (hsc : ∀ n, LowerSemicontinuous (Fₙ n)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ n k, n ≤ k → ∀ x, Fₙ n x ≤ C * Fₙ k x) (x : X) :
    (⨆ n, Fₙ n x) ≤ C * F x := by
  apply iSup_le
  intro n
  exact hF.le_of_eventually_le_mul (hsc n) C hC
    ((hj.tendsto_atTop.eventually_ge_atTop n).mono fun k hk ↦ h n (j k) hk) x


/-- At every strict energy threshold, one can choose a recovery sequence
along a further sequence of indices tending to infinity. -/
theorem IsGammaLimit.exists_tendsto_of_lt {Y : Type*} [PseudoMetricSpace Y]
    {Fₙ : ℕ → Y → ℝ≥0∞} {F : Y → ℝ≥0∞}
    (hF : IsGammaLimit Fₙ F) (x : Y) {a : ℝ≥0∞} (ha : F x < a) :
    ∃ (k : ℕ → ℕ) (u : ℕ → Y), Tendsto k atTop atTop ∧
      Tendsto u atTop (𝓝 x) ∧ ∀ n, Fₙ (k n) (u n) < a := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hh (n : ℕ) : ∃ k ≥ n, ∃ u ∈ Metric.ball x (ε n), Fₙ k u < a := by
    exact ((eventually_ge_atTop n).and
      (hF.recovery x _ (Metric.ball_mem_nhds x (hε n)) a ha)).exists
  choose k hkn u hu henergy using hh
  refine ⟨k, u, ?_, ?_, henergy⟩
  · exact tendsto_atTop.2 fun b ↦ (eventually_ge_atTop b).mono fun n hn ↦ hn.trans (hkn n)
  · apply Metric.tendsto_nhds.2
    intro δ hδ
    filter_upwards [hlim.eventually_lt_const hδ] with n hn
    exact (Metric.mem_ball.mp (hu n)).trans hn

end CarpetEnergy
