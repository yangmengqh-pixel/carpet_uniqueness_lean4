import CarpetMeasure
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Chaining almost-everywhere inequalities on a finite open cover
-/

open Filter Function MeasureTheory Set

namespace CarpetEnergy

variable {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]

private def openCoverGraph (B : ι → Set X) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (B i ∩ B j).Nonempty
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, inter_comm _ _ ▸ h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

omit [MeasurableSpace X] in
private theorem openCoverGraph_reachable (B : ι → Set X) (hB : ∀ i, IsOpen (B i))
    {W : Set X} (hW : IsPreconnected W) (hcov : W ⊆ ⋃ i, B i)
    (hmeet : ∀ i, (W ∩ B i).Nonempty) (i j : ι) :
    (openCoverGraph B).Reachable i j := by
  let G := openCoverGraph B
  by_contra hj
  let S := ⋃ k : {k // G.Reachable i k}, B k.val
  let T := ⋃ k : {k // ¬ G.Reachable i k}, B k.val
  have hS : B i ⊆ S := subset_iUnion (fun k : {k // G.Reachable i k} ↦ B k.val)
    ⟨i, SimpleGraph.Reachable.refl i⟩
  have hT : B j ⊆ T := subset_iUnion (fun k : {k // ¬ G.Reachable i k} ↦ B k.val) ⟨j, hj⟩
  have hcover : W ⊆ S ∪ T := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hx)
    by_cases hr : G.Reachable i k
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k, hr⟩, hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hr⟩, hk⟩)
  obtain ⟨x, _, hxS, hxT⟩ := hW S T (isOpen_iUnion fun _ ↦ hB _) (isOpen_iUnion fun _ ↦ hB _)
    hcover ((hmeet i).mono (inter_subset_inter_right _ hS))
    ((hmeet j).mono (inter_subset_inter_right _ hT))
  obtain ⟨u, hu⟩ := mem_iUnion.mp hxS
  obtain ⟨v, hv⟩ := mem_iUnion.mp hxT
  have hne : u.val ≠ v.val := fun he ↦ v.property (he ▸ u.property)
  exact v.property (u.property.trans (SimpleGraph.Adj.reachable
    (show G.Adj u.val v.val from ⟨hne, ⟨x, hu, hv⟩⟩)))

private theorem openCoverGraph_walk_pair_le {μ : Measure X} [μ.IsOpenPosMeasure]
    (B : ι → Set X) (hB : ∀ i, IsOpen (B i)) (f : X → ℝ) {H : ℝ} (hH : 1 ≤ H)
    (hlocal : ∀ i, ∀ᵐ x ∂μ.restrict (B i), ∀ᵐ y ∂μ.restrict (B i), f x ≤ H * f y)
    {i j : ι} (w : (openCoverGraph B).Walk i j) :
    ∀ᵐ x ∂μ.restrict (B i), ∀ᵐ y ∂μ.restrict (B j), f x ≤ H ^ (w.length + 1) * f y := by
  induction w with
  | nil => simpa only [SimpleGraph.Walk.length_nil, zero_add, pow_one] using hlocal _
  | @cons i j k hadj w ih =>
    have hne : (B i ∩ B j).Nonempty := hadj.2
    let ν := μ.restrict (B i ∩ B j)
    have hν : ν ≠ 0 := by
      intro hz
      have hh : ν univ = μ (B i ∩ B j) := by simp [ν]
      rw [hz] at hh
      simp only [FunLike.coe_zero, Pi.zero_apply] at hh
      exact ((hB i).inter (hB j)).measure_pos μ hne |>.ne' hh.symm
    let : NeBot (ae ν) := ae_neBot.mpr hν
    have hleft : ν ≤ μ.restrict (B i) := Measure.restrict_mono inter_subset_left le_rfl
    have hright : ν ≤ μ.restrict (B j) := Measure.restrict_mono inter_subset_right le_rfl
    filter_upwards [hlocal i] with x hx
    obtain ⟨y, hxy, hy⟩ := ((hx.filter_mono (ae_mono hleft)).and (ih.filter_mono (ae_mono hright))).exists
    filter_upwards [hy] with z hz
    calc
      f x ≤ H * f y := hxy
      _ ≤ H * (H ^ (w.length + 1) * f z) := mul_le_mul_of_nonneg_left hz (zero_le_one.trans hH)
      _ = _ := by
        rw [SimpleGraph.Walk.length_cons, pow_succ H (w.length + 1)]
        ring

set_option maxHeartbeats 2400000 in
/-- Local pairwise comparisons on a finite open cover of a preconnected
set imply a global pairwise comparison, with at most one factor per ball. -/
theorem ae_pair_le_of_finite_openCover [Fintype ι] {μ : Measure X} [μ.IsOpenPosMeasure]
    (B : ι → Set X) (hB : ∀ i, IsOpen (B i)) {W : Set X}
    (hW : IsPreconnected W) (hcov : W ⊆ ⋃ i, B i) (hmeet : ∀ i, (W ∩ B i).Nonempty)
    (f : X → ℝ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) {H : ℝ} (hH : 1 ≤ H)
    (hlocal : ∀ i, ∀ᵐ x ∂μ.restrict (B i), ∀ᵐ y ∂μ.restrict (B i), f x ≤ H * f y) :
    ∀ᵐ x ∂μ.restrict W, ∀ᵐ y ∂μ.restrict W, f x ≤ H ^ Fintype.card ι * f y := by
  classical
  have hpairs (i j : ι) :
      ∀ᵐ x ∂μ.restrict (B i), ∀ᵐ y ∂μ.restrict (B j), f x ≤ H ^ Fintype.card ι * f y := by
    obtain ⟨w⟩ := openCoverGraph_reachable B hB hW hcov hmeet i j
    let w' := (w.toPath : (openCoverGraph B).Walk i j)
    have hlen := w.toPath.nodup_support.length_le_card
    change w'.support.length ≤ _ at hlen
    rw [SimpleGraph.Walk.length_support] at hlen
    have hh := openCoverGraph_walk_pair_le B hB f hH hlocal w'
    filter_upwards [hh] with x hx
    filter_upwards [hx, ae_restrict_of_ae (s := B j) hf] with y hy hy₀
    exact hy.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH hlen) hy₀)
  have htotal : ∀ᵐ x ∂μ.restrict (⋃ i, B i), ∀ᵐ y ∂μ.restrict (⋃ i, B i),
      f x ≤ H ^ Fintype.card ι * f y := by
    apply (ae_restrict_iUnion_iff B _).mpr
    intro i
    filter_upwards [ae_all_iff.mpr (hpairs i)] with x hx
    exact (ae_restrict_iUnion_iff B _).mpr hx
  have hmono : ae (μ.restrict W) ≤ ae (μ.restrict (⋃ i, B i)) :=
    ae_mono (Measure.restrict_mono hcov le_rfl)
  exact (htotal.filter_mono hmono).mono fun _ hx ↦ hx.filter_mono hmono

end CarpetEnergy
