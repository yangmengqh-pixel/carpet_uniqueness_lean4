import EnergyGammaComparison
import Mathlib.Order.Filter.Finite

/-!
# Finite families in a Γ-limit

A finite family of functions admits synchronized recovery at the same
discrete levels. Compactness of the extended nonnegative energy values
and the Γ-lower bound pass finite mixed inequalities to the limit.
-/

open Filter Function Set
open scoped ENNReal Topology

namespace CarpetEnergy

section Recovery

variable {X I : Type*} [PseudoMetricSpace X] [Finite I]

theorem IsGammaLimit.exists_finite_recovery_sequence {Fₙ : ℕ → X → ℝ≥0∞}
    {F : X → ℝ≥0∞} (hF : IsGammaLimit Fₙ F) (f : I → X)
    (hf : ∀ i, F (f i) < ∞) :
    ∃ (k : ℕ → ℕ) (u : ℕ → I → X), Tendsto k atTop atTop ∧
      Tendsto u atTop (𝓝 f) ∧
      Tendsto (fun n i ↦ Fₙ (k n) (u n i)) atTop (𝓝 fun i ↦ F (f i)) := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεlim' : Tendsto (fun n ↦ ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hεlim
    change Tendsto (fun n ↦ ENNReal.ofReal (ε n)) atTop (𝓝 (ENNReal.ofReal 0)) at h
    rwa [ENNReal.ofReal_zero] at h
  have hh (n : ℕ) : ∃ k ≥ n, ∀ i, ∃ z ∈ Metric.ball (f i) (ε n),
      Fₙ k z < F (f i) + ENNReal.ofReal (ε n) := by
    have he : ∀ᶠ k in atTop, ∀ i, ∃ z ∈ Metric.ball (f i) (ε n),
        Fₙ k z < F (f i) + ENNReal.ofReal (ε n) := by
      apply Filter.eventually_all.mpr
      intro i
      exact hF.recovery (f i) _ (Metric.ball_mem_nhds _ (hε n)) _
        (ENNReal.lt_add_right (hf i).ne (ENNReal.ofReal_pos.mpr (hε n)).ne')
    exact ((eventually_ge_atTop n).and he).exists
  choose k hkn u hu henergy using hh
  have hk : Tendsto k atTop atTop :=
    tendsto_atTop.2 fun a ↦ (eventually_ge_atTop a).mono fun n hn ↦ hn.trans (hkn n)
  have hlim (i : I) : Tendsto (fun n ↦ u n i) atTop (𝓝 (f i)) := by
    apply Metric.tendsto_nhds.2
    intro δ hδ
    filter_upwards [hεlim.eventually_lt_const hδ] with n hn
    exact (Metric.mem_ball.mp (hu n i)).trans hn
  refine ⟨k, u, hk, tendsto_pi_nhds.2 hlim, tendsto_pi_nhds.2 fun i ↦ ?_⟩
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨b, hab, hb⟩ := exists_between ha
    obtain ⟨U, hU, hlo⟩ := hF.lower (f i) b hb
    filter_upwards [hk.eventually hlo, hlim i hU] with n hn hu
    exact hab.trans_le (hn _ hu)
  · intro a ha
    have ht : Tendsto (fun n ↦ F (f i) + ENNReal.ofReal (ε n)) atTop (𝓝 (F (f i))) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := F (f i))).add hεlim'
    filter_upwards [ht.eventually_lt_const ha] with n hn
    exact (henergy n i).trans hn

end Recovery

section Contraction

variable {X I O : Type*} [PseudoMetricSpace X] [Finite I] [Finite O]

/-- A mixed inequality with finite input energy passes through a Γ-limit
if its transformations converge along convergent recovery sequences. -/
theorem IsGammaLimit.finite_contraction_of_approximate {Fₙ : ℕ → X → ℝ≥0∞}
    {F : X → ℝ≥0∞} (hF : IsGammaLimit Fₙ F)
    (P : (I → ℝ≥0∞) → ℝ≥0∞) (Q : (O → ℝ≥0∞) → ℝ≥0∞)
    (hP : Continuous P) (hQ : Continuous Q) (hQmono : Monotone Q)
    (Gₙ : ℕ → (I → X) → O → X) (G : (I → X) → O → X)
    (hG : ∀ (k : ℕ → ℕ) (u : ℕ → I → X) (f : I → X),
      Tendsto k atTop atTop → Tendsto u atTop (𝓝 f) →
      Tendsto (fun n ↦ Gₙ (k n) (u n)) atTop (𝓝 (G f)))
    (h : ∀ n f, Q (fun i ↦ Fₙ n (Gₙ n f i)) ≤ P (fun i ↦ Fₙ n (f i)))
    (f : I → X) (hf : ∀ i, F (f i) < ∞) :
    Q (fun i ↦ F (G f i)) ≤ P (fun i ↦ F (f i)) := by
  obtain ⟨k, u, hk, hu, hR⟩ := hF.exists_finite_recovery_sequence f hf
  let s (n : ℕ) (i : O) := Fₙ (k n) (Gₙ (k n) (u n) i)
  obtain ⟨b, _, j, hj, hb⟩ := (isCompact_univ : IsCompact (univ : Set (O → ℝ≥0∞))).tendsto_subseq
    (x := s) (fun _ ↦ mem_univ _)
  have hlim (i : O) : F (G f i) ≤ b i := by
    apply le_of_forall_lt
    intro c hc
    obtain ⟨d, hcd, hd⟩ := exists_between hc
    obtain ⟨U, hU, hlow⟩ := hF.lower (G f i) d hd
    have hU' := ((continuous_apply i).tendsto (G f)).comp ((hG k u f hk hu).comp hj.tendsto_atTop)
    have hbound : ∀ᶠ n in atTop, d ≤ s (j n) i := by
      filter_upwards [(hk.comp hj.tendsto_atTop).eventually hlow, hU' hU] with n hn hm
      exact hn _ hm
    have hb' := ((continuous_apply i).tendsto b).comp hb
    exact hcd.trans_le (le_of_tendsto_of_tendsto tendsto_const_nhds hb' hbound)
  apply (hQmono hlim).trans
  exact le_of_tendsto_of_tendsto ((hQ.tendsto b).comp hb)
    ((hP.tendsto _).comp (hR.comp hj.tendsto_atTop))
    (Eventually.of_forall fun n ↦ h (k (j n)) (u (j n)))

end Contraction

end CarpetEnergy
