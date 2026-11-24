import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Subsequence compactness for nonnegative Γ-limits

The local infima over a countable basis take values in a compact
countable product. A convergent subsequence of this product supplies
both the local lower bound and the recovery cuts for the Γ-limit.
-/

open Filter Function Set TopologicalSpace
open scoped ENNReal Topology

namespace CarpetEnergy

variable {X : Type*} [TopologicalSpace X]

/-- Local lower and recovery bounds for Γ-convergence. In a first-countable
space these are the respective sequential lower and recovery conditions. -/
structure IsGammaLimit (Fₙ : ℕ → X → ℝ≥0∞) (F : X → ℝ≥0∞) : Prop where
  lower : ∀ x a, a < F x → ∃ U ∈ 𝓝 x, ∀ᶠ n in atTop, ∀ z ∈ U, a ≤ Fₙ n z
  recovery : ∀ x U, U ∈ 𝓝 x → ∀ a, F x < a → ∀ᶠ n in atTop, ∃ z ∈ U, Fₙ n z < a

/-- The Γ-compactness step used for the rescaled discrete energies in
Murugan and Shimizu's Theorem 6.22. -/
theorem exists_gammaLimit_subseq [SecondCountableTopology X] (Fₙ : ℕ → X → ℝ≥0∞) :
    ∃ (j : ℕ → ℕ) (F : X → ℝ≥0∞), StrictMono j ∧ IsGammaLimit (fun n ↦ Fₙ (j n)) F := by
  obtain ⟨B, hB, _, hbasis⟩ := exists_countable_basis X
  let I : Type _ := B
  have : Countable I := hB.to_subtype
  let b (n : ℕ) (U : I) := ⨅ z : U.val, Fₙ n z.val
  obtain ⟨ℓ, _, j, hj, hlim⟩ := (isCompact_univ : IsCompact (univ : Set (I → ℝ≥0∞))).tendsto_subseq
    (x := b) (fun _ ↦ mem_univ _)
  let F (x : X) := ⨆ U : {U : I // x ∈ U.val}, ℓ U.val
  have hl (U : I) : Tendsto (fun n ↦ b (j n) U) atTop (𝓝 (ℓ U)) :=
    ((continuous_apply U).tendsto ℓ).comp hlim
  refine ⟨j, F, hj, ⟨?_, ?_⟩⟩
  · intro x a ha
    obtain ⟨U, hU⟩ := lt_iSup_iff.mp ha
    refine ⟨U.val.val, (hbasis.isOpen U.val.property).mem_nhds U.property, ?_⟩
    filter_upwards [(hl U.val).eventually_const_lt hU] with n hn z hz
    exact hn.le.trans (iInf_le (fun t : U.val.val ↦ Fₙ (j n) t.val) ⟨z, hz⟩)
  · intro x U hU a ha
    obtain ⟨V, hV, hxV, hVU⟩ := hbasis.mem_nhds_iff.mp hU
    let v : I := ⟨V, hV⟩
    have h := (le_iSup (fun W : {W : I // x ∈ W.val} ↦ ℓ W.val) ⟨v, hxV⟩).trans_lt ha
    filter_upwards [(hl v).eventually_lt_const h] with n hn
    obtain ⟨z, hz⟩ := iInf_lt_iff.mp hn
    exact ⟨z.val, hVU z.property, hz⟩

/-- A continuous operation decreasing each approximating functional
decreases its Γ-limit. -/
theorem IsGammaLimit.apply_le_of_apply_le {Fₙ : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞}
    (hF : IsGammaLimit Fₙ F) {g : X → X} (hg : Continuous g)
    (h : ∀ n x, Fₙ n (g x) ≤ Fₙ n x) (x : X) : F (g x) ≤ F x := by
  by_contra! hlt
  obtain ⟨a, hx, ha⟩ := exists_between hlt
  obtain ⟨U, hU, hlow⟩ := hF.lower (g x) a ha
  have hpre : g ⁻¹' U ∈ 𝓝 x := (hg.tendsto x) hU
  obtain ⟨n, hl, z, hz, hhigh⟩ := (hlow.and (hF.recovery x (g ⁻¹' U) hpre a hx)).exists
  exact hhigh.not_ge ((hl (g z) hz).trans (h n z))

theorem IsGammaLimit.lowerSemicontinuous {Fₙ : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞}
    (hF : IsGammaLimit Fₙ F) : LowerSemicontinuous F := by
  intro x a ha
  obtain ⟨b, hab, hb⟩ := exists_between ha
  obtain ⟨U, hU, hlow⟩ := hF.lower x b hb
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  filter_upwards [hV.mem_nhds hxV] with y hy
  have hle : b ≤ F y := by
    by_contra! h
    have hyU := mem_of_superset (hV.mem_nhds hy) hVU
    obtain ⟨n, hn, z, hz, hhigh⟩ := (hlow.and (hF.recovery y U hyU b h)).exists
    exact hhigh.not_ge (hn z hz)
  exact hab.trans_le hle

/-- The sequential lower inequality follows from the local Γ condition. -/
theorem IsGammaLimit.eventually_le_of_tendsto {Fₙ : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞}
    (hF : IsGammaLimit Fₙ F) {x : X} {f : ℕ → X} (hf : Tendsto f atTop (𝓝 x))
    {a : ℝ≥0∞} (ha : a < F x) :
    ∀ᶠ n in atTop, a ≤ Fₙ n (f n) := by
  obtain ⟨U, hU, hl⟩ := hF.lower x a ha
  filter_upwards [hl, hf hU] with n hn hfn
  exact hn (f n) hfn

/-- Approximate transformations may depend on the discrete level. The
local recovery bound passes an energy contraction through such a transformation
if it converges uniformly on sufficiently small neighborhoods of the datum. -/
theorem IsGammaLimit.apply_le_of_approximate_contraction
    {Fₙ : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞} (hF : IsGammaLimit Fₙ F)
    (gₙ : ℕ → X → X) (g : X → X)
    (hconv : ∀ x U, U ∈ 𝓝 (g x) → ∃ V ∈ 𝓝 x, ∀ᶠ n in atTop, MapsTo (gₙ n) V U)
    (h : ∀ n x, Fₙ n (gₙ n x) ≤ Fₙ n x) (x : X) : F (g x) ≤ F x := by
  by_contra! hlt
  obtain ⟨a, hx, ha⟩ := exists_between hlt
  obtain ⟨U, hU, hlow⟩ := hF.lower (g x) a ha
  obtain ⟨V, hV, hUV⟩ := hconv x U hU
  obtain ⟨n, hl, hm, z, hz, hhigh⟩ := (hlow.and (hUV.and (hF.recovery x V hV a hx))).exists
  exact hhigh.not_ge ((hl (gₙ n z) (hm hz)).trans (h n z))

end CarpetEnergy
