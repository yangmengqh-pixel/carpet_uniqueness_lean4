import AddressMeasureComparison

/-!
# First crossings on the address space

The cylinders where the conditional fraction of a set first reaches a
threshold are disjoint, and their union covers the set up to measure zero.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CarpetEnergy

/-- Initial address tuples with their length. -/
abbrev FiniteAddress := Σ n : ℕ, Fin n → Fin 8

/-- Cylinders where the fraction of `A` reaches `δ` and no shorter prefix has reached it. -/
def firstCrossingAddresses (μ : Measure Addresses) (A : Set Addresses) (δ : ℝ≥0) :
    Set FiniteAddress :=
  {w | (δ : ℝ≥0∞) * μ (addressCylinder w.2) ≤ μ (A ∩ addressCylinder w.2) ∧
    ∀ s ∈ addressCylinder w.2, ∀ m < w.1,
      μ (A ∩ addressCylinder (addressPrefix m s)) < (δ : ℝ≥0∞) *
        μ (addressCylinder (addressPrefix m s))}

private theorem addressPrefix_eq_of_mem_same_cylinder {s t : Addresses} {n : ℕ} {w : Fin n → Fin 8}
    (hs : s ∈ addressCylinder w) (ht : t ∈ addressCylinder w) {m : ℕ} (hm : m ≤ n) :
    addressPrefix m s = addressPrefix m t := by
  change addressPrefix n s = w at hs
  change addressPrefix n t = w at ht
  funext i
  exact congrFun (hs.trans ht.symm) (Fin.castLE hm i)

theorem pairwise_disjoint_firstCrossingAddresses
    (μ : Measure Addresses) (A : Set Addresses) (δ : ℝ≥0) :
    Pairwise fun v w : firstCrossingAddresses μ A δ ↦
      Disjoint (addressCylinder v.val.2) (addressCylinder w.val.2) := by
  intro a b hab
  apply disjoint_left.mpr
  intro s ha hb
  have hA := a.property
  have hB := b.property
  rcases lt_trichotomy a.val.1 b.val.1 with h | h | h
  · have h₁ := hB.2 s hb a.val.1 h
    have ha' : addressPrefix a.val.1 s = a.val.2 := ha
    rw [ha'] at h₁
    exact h₁.not_ge hA.1
  · obtain ⟨⟨n, v⟩, hva⟩ := a
    obtain ⟨⟨m, w⟩, hwb⟩ := b
    change n = m at h
    subst m
    have hva' : addressPrefix n s = v := ha
    have hwb' : addressPrefix n s = w := hb
    exact hab (Subtype.ext (congrArg (Sigma.mk n) (hva'.symm.trans hwb')))
  · have h₁ := hA.2 s ha b.val.1 h
    have hb' : addressPrefix b.val.1 s = b.val.2 := hb
    rw [hb'] at h₁
    exact h₁.not_ge hB.1

private theorem mem_iUnion_firstCrossing_of_exists
    (μ : Measure Addresses) (A : Set Addresses) (δ : ℝ≥0) (s : Addresses)
    (h : ∃ n : ℕ, (δ : ℝ≥0∞) * μ (addressCylinder (addressPrefix n s)) ≤
      μ (A ∩ addressCylinder (addressPrefix n s))) :
    s ∈ ⋃ w : firstCrossingAddresses μ A δ, addressCylinder w.val.2 := by
  classical
  let n := Nat.find h
  let v : FiniteAddress := ⟨n, addressPrefix n s⟩
  have hs : s ∈ addressCylinder v.2 := rfl
  have hv : v ∈ firstCrossingAddresses μ A δ := by
    refine ⟨Nat.find_spec h, ?_⟩
    intro t ht m hm
    have heq := addressPrefix_eq_of_mem_same_cylinder hs ht hm.le
    rw [← heq]
    exact lt_of_not_ge (Nat.find_min h hm)
  exact mem_iUnion.mpr ⟨⟨v, hv⟩, hs⟩

/-- A set is covered almost everywhere by its first-crossing cylinders. -/
theorem measure_sdiff_firstCrossingAddresses_eq_zero (μ : Measure Addresses) [IsFiniteMeasure μ]
    {A : Set Addresses} {δ : ℝ≥0} (hδ : δ < 1) :
    μ (A \ ⋃ w : firstCrossingAddresses μ A δ, addressCylinder w.val.2) = 0 := by
  by_contra hnull
  let U := ⋃ w : firstCrossingAddresses μ A δ, addressCylinder w.val.2
  obtain ⟨n, v, hv⟩ := exists_addressCylinder_large_fraction μ hnull hδ
  have hsub : addressCylinder v ⊆ U := by
    intro s hs
    change addressPrefix n s = v at hs
    apply mem_iUnion_firstCrossing_of_exists
    refine ⟨n, ?_⟩
    rw [hs]
    exact hv.le.trans (measure_mono (inter_subset_inter_left _ sdiff_subset))
  have he : (A \ U) ∩ addressCylinder v = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun _ hx ↦ hx.1.2 (hsub hx.2)
  rw [he, measure_empty] at hv
  exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ _ from bot_le)) hv

end CarpetEnergy
