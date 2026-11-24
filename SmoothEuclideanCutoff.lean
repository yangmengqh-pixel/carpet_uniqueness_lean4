import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth cutoffs around compact sets

A finite family of bump functions covers the compact set. Taking one
minus the product of their complements gives a smooth function equal
to one on that set.
-/

open Function Metric Set
open scoped BigOperators

namespace CarpetEnergy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [HasContDiffBump V]

theorem exists_smooth_cutoff_compact {K U : Set V} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ φ : V → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧
      support φ ⊆ U ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ EqOn φ (fun _ ↦ 1) K := by
  classical
  have hball (x : K) : ∃ r > (0 : ℝ), Metric.ball x.val r ⊆ U :=
    Metric.isOpen_iff.mp hU x.val (hKU x.property)
  choose r hr hrU using hball
  let bump (x : K) : ContDiffBump x.val :=
    ⟨r x / 2, r x, half_pos (hr x), half_lt_self (hr x)⟩
  let B (x : K) := Metric.ball x.val (r x / 2)
  have hcover : K ⊆ ⋃ x : K, B x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hr ⟨x, hx⟩))⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover B (fun _ ↦ isOpen_ball) hcover
  let φ (y : V) := 1 - ∏ x ∈ s, (1 - bump x y)
  have hprod (y : V) : 0 ≤ ∏ x ∈ s, (1 - bump x y) ∧ ∏ x ∈ s, (1 - bump x y) ≤ 1 := by
    refine ⟨Finset.prod_nonneg (fun x _ ↦ sub_nonneg.mpr (bump x).le_one), ?_⟩
    exact Finset.prod_le_one₀ (fun x _ ↦ sub_nonneg.mpr (bump x).le_one)
      (fun x _ ↦ sub_le_self _ (bump x).nonneg)
  have hsupp : support φ ⊆ ⋃ x ∈ s, support (bump x : V → ℝ) := by
    intro y hy
    by_contra h
    have hz (x : K) (hx : x ∈ s) : bump x y = 0 := by
      contrapose! h
      exact mem_iUnion₂.mpr ⟨x, hx, h⟩
    have hp : (∏ x ∈ s, (1 - bump x y)) = 1 := Finset.prod_eq_one (fun x hx ↦ by rw [hz x hx, sub_zero])
    exact hy (by simp only [φ, hp, sub_self])
  have hts : support φ ⊆ ⋃ x ∈ s, tsupport (bump x : V → ℝ) :=
    hsupp.trans (iUnion₂_mono fun x _ ↦ subset_tsupport _)
  have hcompact : IsCompact (⋃ x ∈ s, tsupport (bump x : V → ℝ)) :=
    s.finite_toSet.isCompact_biUnion (fun x _ ↦ (bump x).hasCompactSupport)
  refine ⟨φ, ?_, HasCompactSupport.of_support_subset_isCompact hcompact hts, ?_, ?_, ?_⟩
  · exact contDiff_const.sub (contDiff_prod fun x _ ↦ contDiff_const.sub (bump x).contDiff)
  · refine hsupp.trans (iUnion₂_subset fun x _ ↦ ?_)
    rw [(bump x).support_eq]
    exact hrU x
  · intro y
    have h := hprod y
    exact ⟨sub_nonneg.mpr h.2, sub_le_self _ h.1⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (hs hy)
    have hBump : bump x y = 1 := (bump x).one_of_mem_closedBall (ball_subset_closedBall hxy)
    have he : (∏ x ∈ s, (1 - bump x y)) = 0 :=
      Finset.prod_eq_zero hx (by rw [hBump, sub_self])
    show φ y = 1
    simp only [φ, he, sub_zero]

end CarpetEnergy
