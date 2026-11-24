import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Bounded convex approximation in uniformly convex Banach spaces

The intersection argument below gives the closed-convex-tail form of bounded
approximation. It uses the modulus of uniform convexity directly.
-/

open Filter Function Metric Set
open scoped Topology

namespace CarpetEnergy

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [UniformConvexSpace X] [CompleteSpace X]

/-- A decreasing sequence of nonempty bounded closed convex sets has a common point. -/
theorem exists_mem_antitone_closed_convex (C : ℕ → Set X) (hmono : Antitone C)
    (hclosed : ∀ n, IsClosed (C n)) (hconv : ∀ n, Convex ℝ (C n))
    (hne : ∀ n, (C n).Nonempty) {R : ℝ} (hb : ∀ x ∈ C 0, ‖x‖ ≤ R) :
    ∃ x, ∀ n, x ∈ C n := by
  classical
  let d (n : ℕ) := sInf (norm '' C n)
  have hbelow (n : ℕ) : BddBelow (norm '' C n) :=
    ⟨0, fun _ ⟨x, _, hx⟩ ↦ hx ▸ norm_nonneg x⟩
  have hd_nonneg (n : ℕ) : 0 ≤ d n :=
    le_csInf ((hne n).image norm) fun _ ⟨x, _, hx⟩ ↦ hx ▸ norm_nonneg x
  have hd_le (n : ℕ) (x : X) (hx : x ∈ C n) : d n ≤ ‖x‖ :=
    csInf_le (hbelow n) (mem_image_of_mem _ hx)
  have hmono_d : Monotone d := by
    intro m n hmn
    exact le_csInf ((hne n).image norm) fun _ ⟨x, hx, hxeq⟩ ↦
      hxeq ▸ hd_le m x (hmono hmn hx)
  have hbdd : BddAbove (range d) := by
    refine ⟨R, ?_⟩
    rintro _ ⟨n, rfl⟩
    obtain ⟨x, hx⟩ := hne n
    exact (hd_le n x hx).trans (hb x (hmono (Nat.zero_le n) hx))
  let a := ⨆ n, d n
  have hdlim : Tendsto d atTop (𝓝 a) := tendsto_atTop_ciSup hmono_d hbdd
  have hda (n : ℕ) : d n ≤ a := le_ciSup hbdd n
  have ha : 0 ≤ a := (hd_nonneg 0).trans (hda 0)
  let err (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have herr : Tendsto err atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hchoose (n : ℕ) : ∃ x ∈ C n, ‖x‖ < d n + err n := by
    have ht : d n < d n + err n := lt_add_of_pos_right _ (by dsimp [err]; positivity)
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((hne n).image norm) ht
    exact ⟨x, hx, hlt⟩
  choose x hx hxnorm using hchoose
  have hc : CauchySeq x := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    by_cases hzero : a = 0
    · obtain ⟨N, hN⟩ := eventually_atTop.mp (herr.eventually_lt_const (half_pos hε))
      refine ⟨N, fun m hm n hn ↦ ?_⟩
      have hm' : ‖x m‖ < ε / 2 := (hxnorm m).trans
        (show d m + err m < ε / 2 by linarith [hda m, hN m hm])
      have hn' : ‖x n‖ < ε / 2 := (hxnorm n).trans
        (show d n + err n < ε / 2 by linarith [hda n, hN n hn])
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans_lt (by linarith)
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
      obtain ⟨δ, hδ, hmod⟩ := exists_forall_closed_ball_dist_add_le_two_sub X
        (div_pos hε (by linarith : 0 < a + 1))
      let η := min 1 (δ * a / 8)
      have hη : 0 < η := lt_min one_pos (by positivity)
      have hη₁ : η ≤ 1 := min_le_left _ _
      have hηδ : η ≤ δ * a / 8 := min_le_right _ _
      let r := a + η
      have hr : 0 < r := add_pos hap hη
      have hlarge : ∀ᶠ n in atTop, a - η < d n :=
        hdlim.eventually_const_lt (sub_lt_self a hη)
      obtain ⟨N, hN⟩ := eventually_atTop.mp
        ((herr.eventually_lt_const hη).and hlarge)
      refine ⟨N, fun m hm n hn ↦ ?_⟩
      have hm' : ‖x m‖ ≤ r := (hxnorm m).le.trans
        (add_le_add (hda m) (hN m hm).1.le)
      have hn' : ‖x n‖ ≤ r := (hxnorm n).le.trans
        (add_le_add (hda n) (hN n hn).1.le)
      by_contra! hdist
      rw [dist_eq_norm] at hdist
      have hnormScale (z : X) : ‖r⁻¹ • z‖ = ‖z‖ / r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le),
          div_eq_mul_inv, mul_comm]
      have hmScale : ‖r⁻¹ • x m‖ ≤ 1 := by rw [hnormScale, div_le_one hr]; exact hm'
      have hnScale : ‖r⁻¹ • x n‖ ≤ 1 := by rw [hnormScale, div_le_one hr]; exact hn'
      have hdistScale : ε / (a + 1) ≤ ‖r⁻¹ • x m - r⁻¹ • x n‖ := by
        rw [← smul_sub, hnormScale]
        exact div_le_div₀ (norm_nonneg _) hdist hr (add_le_add_right hη₁ a)
      have hsum := hmod hmScale hnScale hdistScale
      rw [← smul_add, hnormScale, div_le_iff₀ hr] at hsum
      let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
      have hmid := (hconv N).midpoint_mem (hmono hm (hx m)) (hmono hn (hx n))
      have hl := hd_le N _ hmid
      rw [midpoint_eq_smul_add, norm_smul, Real.norm_eq_abs, invOf_eq_inv] at hl
      norm_num at hl
      have hδa : δ * a ≤ δ * r := mul_le_mul_of_nonneg_left (by dsimp [r]; linarith) hδ.le
      dsimp only [r] at hsum hδa
      linarith [(hN N le_rfl).2]
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨z, fun n ↦ (hclosed n).mem_of_tendsto hz ?_⟩
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hmono hm (hx m)

variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A bounded sequence whose images converge has a preimage of the limit in every
closed convex hull of its tails. -/
theorem exists_mem_closed_convex_tails_of_bounded_tendsto
    (T : X →L[ℝ] Y) {u : ℕ → X} {y : Y} {R : ℝ}
    (hb : ∀ n, ‖u n‖ ≤ R) (hy : Tendsto (fun n ↦ T (u n)) atTop (𝓝 y)) :
    ∃ x, T x = y ∧ ∀ n, x ∈ closure (convexHull ℝ (u '' Ici n)) := by
  let C (n : ℕ) := closure (convexHull ℝ (u '' Ici n))
  have hC (n : ℕ) : u n ∈ C n :=
    subset_closure (subset_convexHull ℝ _ (mem_image_of_mem _ (mem_Ici.mpr le_rfl)))
  have hball : C 0 ⊆ closedBall 0 R := by
    apply closure_minimal _ isClosed_closedBall
    apply convexHull_min _ (convex_closedBall 0 R)
    rintro _ ⟨n, _, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hb n)
  have hB (z : X) (hz : z ∈ C 0) : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp (hball hz)
  obtain ⟨x, hx⟩ := exists_mem_antitone_closed_convex C
    (fun m n hmn ↦ closure_mono (convexHull_mono (image_mono (Ici_subset_Ici.mpr hmn))))
    (fun _ ↦ isClosed_closure) (fun _ ↦ (convex_convexHull ℝ _).closure)
    (fun n ↦ ⟨u n, hC n⟩) hB
  refine ⟨x, ?_, hx⟩
  apply dist_le_zero.mp
  by_contra! hdist
  let ε := dist (T x) y / 2
  have hε : 0 < ε := half_pos hdist
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hy.eventually (ball_mem_nhds y hε))
  have htail : C N ⊆ T ⁻¹' closedBall y ε := by
    apply closure_minimal _ (isClosed_closedBall.preimage T.continuous)
    apply convexHull_min _ ((convex_closedBall y ε).linear_preimage T.toLinearMap)
    rintro _ ⟨n, hn, rfl⟩
    exact ball_subset_closedBall (hN n hn)
  have h := mem_closedBall.mp (htail (hx N))
  dsimp only [ε] at h
  linarith

/-- A uniformly convex Banach space that injects continuously and linearly into a
second-countable normed space is separable. -/
theorem separableSpace_of_injective_continuousLinearMap [SecondCountableTopology Y]
    (T : X →L[ℝ] Y) (hT : Function.Injective T) : TopologicalSpace.SeparableSpace X := by
  let A (n : ℕ) : Set Y := T '' closedBall (0 : X) (n : ℝ)
  obtain ⟨s, hs, hcount, hdense⟩ : ∃ s : ℕ → Set Y,
      (∀ n, s n ⊆ A n) ∧ (∀ n, (s n).Countable) ∧ (∀ n, A n ⊆ closure (s n)) := by
    choose s hc hs hd using fun n : ℕ ↦ TopologicalSpace.exists_countable_dense_subset (A n)
    exact ⟨s, hs, hc, hd⟩
  let S : Set X := ⋃ n, T ⁻¹' s n
  let V := Submodule.span ℝ S
  have hS : S.Countable := countable_iUnion fun n ↦ (hcount n).preimage hT
  apply TopologicalSpace.isSeparable_univ_iff.mp
  apply (hS.isSeparable.span.closure : TopologicalSpace.IsSeparable (closure (V : Set X))).mono
  intro x _
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  have hx : T x ∈ closure (s n) :=
    hdense n ⟨x, mem_closedBall_zero_iff.mpr hn, rfl⟩
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  choose u hu heq using fun k ↦ hs n (hv k)
  have hu' : ∀ k, ‖u k‖ ≤ (n : ℝ) := fun k ↦ mem_closedBall_zero_iff.mp (hu k)
  have hlim' : Tendsto (fun k ↦ T (u k)) atTop (𝓝 (T x)) := by
    simpa only [heq] using hlim
  obtain ⟨z, hz, htail⟩ := exists_mem_closed_convex_tails_of_bounded_tendsto T hu' hlim'
  rw [← hT hz]
  apply closure_mono _ (htail 0)
  apply convexHull_min _ V.convex
  rintro _ ⟨k, _, rfl⟩
  exact Submodule.subset_span (mem_iUnion.mpr ⟨n, by
    change T (u k) ∈ s n
    rw [heq k]
    exact hv k⟩)

end CarpetEnergy
