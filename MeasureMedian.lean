import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Medians of bounded real functions

A median is the infimum of the thresholds whose lower closed level set has
at least half of the probability. Continuity from above and below controls
the two strict tails even when the measure has atoms.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

/-- A bounded measurable real function has a threshold with at most half
the probability in each strict tail. -/
theorem exists_median_of_bounded {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    {lo hi : ℝ} (hlo : ∀ x, lo ≤ f x) (hhi : ∀ x, f x ≤ hi) :
    ∃ m : ℝ, μ {x | f x < m} ≤ 2⁻¹ ∧ μ {x | m < f x} ≤ 2⁻¹ := by
  let F (r : ℝ) := {x | f x ≤ r}
  have hmF (r : ℝ) : MeasurableSet (F r) := measurableSet_le hf measurable_const
  have hF : Monotone F := fun _ _ h _ hx ↦ hx.trans h
  let S : Set ℝ := {r | (2 : ℝ≥0∞)⁻¹ ≤ μ (F r)}
  have hS : S.Nonempty := ⟨hi, by
    change (2 : ℝ≥0∞)⁻¹ ≤ μ (F hi)
    rw [show F hi = univ from eq_univ_of_forall hhi, measure_univ]
    norm_num⟩
  have hSb : BddBelow S := ⟨lo, by
    intro r hr
    by_contra! h
    have he : F r = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx ↦ h.not_ge ((hlo x).trans hx)
    change (2 : ℝ≥0∞)⁻¹ ≤ μ (F r) at hr
    rw [he, measure_empty] at hr
    exact (by norm_num : (0 : ℝ≥0∞) < 2⁻¹).not_ge hr⟩
  let m := sInf S
  have hlarge {r : ℝ} (hr : m < r) : r ∈ S := by
    obtain ⟨s, hs, hsr⟩ := exists_lt_of_csInf_lt hS hr
    exact hs.trans (measure_mono (hF hsr.le))
  have hsmall {r : ℝ} (hr : r < m) : μ (F r) ≤ 2⁻¹ := by
    have hn : r ∉ S := fun hs ↦ hr.not_ge (csInf_le hSb hs)
    exact (lt_of_not_ge hn).le
  let d (n : ℕ) := (1 : ℝ) / (n + 1)
  have hd (n : ℕ) : 0 < d n := by dsimp only [d]; positivity
  have hdmono : Antitone d := by
    intro n k h
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ h)
  have hU : (⋃ n, F (m - d n)) = {x | f x < m} := by
    ext x
    rw [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      change f x ≤ m - d n at hn
      change f x < m
      linarith [hd n]
    · intro hx
      change f x < m at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      refine ⟨n, ?_⟩
      change f x ≤ m - d n
      change d n < m - f x at hn
      linarith
  have hI : (⋂ n, F (m + d n)) = F m := by
    ext x
    rw [mem_iInter]
    constructor
    · intro hx
      change f x ≤ m
      by_contra hh
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (lt_of_not_ge hh))
      have hxn : f x ≤ m + d n := hx n
      change d n < f x - m at hn
      linarith
    · intro hx n
      exact hx.trans (le_add_of_nonneg_right (hd n).le)
  have hleft : μ {x | f x < m} ≤ 2⁻¹ := by
    rw [← hU, Monotone.measure_iUnion (fun n k h ↦ hF (sub_le_sub_left (hdmono h) m))]
    exact iSup_le fun n ↦ hsmall (by linarith [hd n])
  have hright : (2 : ℝ≥0∞)⁻¹ ≤ μ (F m) := by
    rw [← hI, Antitone.measure_iInter (fun n k h ↦ hF (add_le_add (le_refl m) (hdmono h)))
      (fun n ↦ (hmF (m + d n)).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun n ↦ hlarge (by linarith [hd n])
  refine ⟨m, hleft, ?_⟩
  rw [show {x | m < f x} = (F m)ᶜ from Set.ext fun x ↦ by
    change m < f x ↔ ¬ f x ≤ m
    exact not_le.symm,
    measure_compl (hmF m) (measure_ne_top _ _), measure_univ]
  exact (tsub_le_tsub_left hright 1).trans (by norm_num)

end CarpetEnergy
