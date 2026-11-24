import CarpetGoodCells
import CarpetCellProjections
import AddressStopping

/-!
# Stopping among prescribed good cells

After deleting all cell boundaries, intersecting cells of different
levels are nested. First eligible cells therefore give a countable
disjoint cover of a compact set. This permits high-density selection
when the eligible levels can vary from point to point.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CarpetEnergy

/-- A word cell with all level boundaries removed. -/
noncomputable def cleanWordCell (w : FiniteAddress) : Set CarpetPoints :=
  range (wordMap (List.ofFn w.2)) \ carpetAllCellBoundaries

theorem measurableSet_cleanWordCell (w : FiniteAddress) :
    MeasurableSet (cleanWordCell w) :=
  (measurableEmbedding_wordMap _).measurableSet_range.diff measurableSet_carpetAllCellBoundaries

private theorem addressPrefix_eq_of_coding_mem_clean {s : Addresses} {w : FiniteAddress}
    (hs : coding s ∈ cleanWordCell w) : addressPrefix w.1 s = w.2 := by
  by_contra h
  have hb := inter_word_subset_cellBoundary h ⟨coding_mem_range_prefix _ s, hs.1⟩
  exact hs.2 (mem_iUnion.mpr ⟨w.1, hb⟩)

private theorem cleanWordCell_subset_of_nonempty_inter {w v : FiniteAddress} (h : w.1 ≤ v.1)
    (hn : (cleanWordCell w ∩ cleanWordCell v).Nonempty) :
    cleanWordCell v ⊆ cleanWordCell w := by
  obtain ⟨x, hxw, hxv⟩ := hn
  obtain ⟨s, rfl⟩ := surjective_coding x
  have hsw := addressPrefix_eq_of_coding_mem_clean hxw
  have hsv := addressPrefix_eq_of_coding_mem_clean hxv
  intro y hy
  obtain ⟨t, rfl⟩ := surjective_coding y
  have htv := addressPrefix_eq_of_coding_mem_clean hy
  have hh : addressPrefix w.1 t = addressPrefix w.1 s := by
    funext i
    exact congrFun (htv.trans hsv.symm) (Fin.castLE h i)
  exact ⟨(hh.trans hsw) ▸ coding_mem_range_prefix _ t, hy.2⟩

private theorem eq_of_same_level_of_nonempty_inter {w v : FiniteAddress} (h : w.1 = v.1)
    (hn : (cleanWordCell w ∩ cleanWordCell v).Nonempty) : w = v := by
  obtain ⟨x, hxw, hxv⟩ := hn
  obtain ⟨s, rfl⟩ := surjective_coding x
  obtain ⟨n, w⟩ := w
  obtain ⟨m, v⟩ := v
  change n = m at h
  subst m
  exact congrArg (Sigma.mk n)
    ((addressPrefix_eq_of_coding_mem_clean hxw).symm.trans (addressPrefix_eq_of_coding_mem_clean hxv))

private def FirstEligibleCells (P : FiniteAddress → Prop) : Set FiniteAddress :=
  {w | P w ∧ ∀ v, v.1 < w.1 → P v → Disjoint (cleanWordCell v) (cleanWordCell w)}

private theorem pairwise_disjoint_firstEligibleCells (P : FiniteAddress → Prop) :
    Pairwise (Disjoint on (fun w : FirstEligibleCells P ↦ cleanWordCell w.val)) := by
  intro u v hne
  rcases lt_trichotomy u.val.1 v.val.1 with h | h | h
  · exact v.property.2 u.val h u.property.1
  · by_contra hn
    have he := eq_of_same_level_of_nonempty_inter h (not_disjoint_iff_nonempty_inter.mp hn)
    exact hne (Subtype.ext he)
  · exact (u.property.2 v.val h v.property.1).symm

private theorem mem_iUnion_firstEligibleCells_of_exists (P : FiniteAddress → Prop) (x : CarpetPoints)
    (hx : ∃ w : FiniteAddress, P w ∧ x ∈ cleanWordCell w) :
    x ∈ ⋃ w : FirstEligibleCells P, cleanWordCell w.val := by
  classical
  have h : ∃ n : ℕ, ∃ w : Fin n → Fin 8, P ⟨n, w⟩ ∧ x ∈ cleanWordCell ⟨n, w⟩ := by
    obtain ⟨⟨n, w⟩, hw⟩ := hx
    exact ⟨n, w, hw⟩
  let n := Nat.find h
  obtain ⟨w, hw, hxw⟩ := Nat.find_spec h
  have he : (⟨n, w⟩ : FiniteAddress) ∈ FirstEligibleCells P := by
    refine ⟨hw, ?_⟩
    intro v hv hP
    by_contra hd
    have hsub := cleanWordCell_subset_of_nonempty_inter hv.le (not_disjoint_iff_nonempty_inter.mp hd)
    exact Nat.find_min h hv ⟨v.2, hP, hsub hxw⟩
  exact mem_iUnion.mpr ⟨⟨⟨n, w⟩, he⟩, hxw⟩

/-- If every point of a positive-measure set lies in arbitrarily fine good
cells, one such positive-mass cell has arbitrarily small relative mass
outside the set. The choice can require any lower bound on the level. -/
theorem exists_good_cell_with_small_complement (ν : Measure CarpetPoints) [IsFiniteMeasure ν]
    [ν.OuterRegular] [ν.InnerRegularCompactLTTop]
    (hnull : ν carpetAllCellBoundaries = 0)
    (B : Set CarpetPoints) (hB : MeasurableSet B) (hpos : 0 < ν B)
    (G : FiniteAddress → Prop)
    (hgood : ∀ x ∈ B, ∀ N : ℕ, ∃ w : FiniteAddress, N ≤ w.1 ∧ G w ∧ x ∈ cleanWordCell w)
    (δ : ℝ≥0∞) (hδ : 0 < δ) (M : ℕ) :
    ∃ w : FiniteAddress, M ≤ w.1 ∧ G w ∧
      0 < ν (range (wordMap (List.ofFn w.2))) ∧
      ν (range (wordMap (List.ofFn w.2)) ∩ Bᶜ) ≤ δ * ν (range (wordMap (List.ofFn w.2))) := by
  classical
  obtain ⟨C, hCB, hC, hCpos⟩ :=
    hB.exists_lt_isCompact_of_ne_top (measure_ne_top ν B) hpos
  obtain ⟨U, hBU, hU, hsmall⟩ := hB.exists_isOpen_sdiff_lt (measure_ne_top ν B)
    (ENNReal.mul_pos hδ.ne' hCpos.ne').ne'
  obtain ⟨r, hr, hrU⟩ := hC.exists_thickening_subset_open hU (hCB.trans hBU)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (tendsto_wordMap_radius.eventually_lt_const hr)
  let N := max M N₀
  have hN : M ≤ N := le_max_left _ _
  have hrange (n : ℕ) (hn : N ≤ n) :
      (1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints) < r :=
    hN₀ n ((le_max_right M N₀).trans hn)
  let P (w : FiniteAddress) := N ≤ w.1 ∧ G w ∧ (cleanWordCell w ∩ C).Nonempty
  let I := FirstEligibleCells P
  let K (w : I) := cleanWordCell w.val
  have hcover : C ⊆ ⋃ w : I, K w := by
    intro x hx
    obtain ⟨w, hw, hwG, hxw⟩ := hgood x (hCB hx) N
    exact mem_iUnion_firstEligibleCells_of_exists P x ⟨w, ⟨hw, hwG, x, hxw, hx⟩, hxw⟩
  have hKU (w : I) : K w ⊆ U := by
    obtain ⟨x, hx, hxc⟩ := w.property.1.2.2
    intro y hy
    apply hrU
    apply mem_thickening_iff.mpr
    refine ⟨x, hxc, ?_⟩
    exact (wordMap_dist_le w.val.1 w.val.2 hy.1 hx.1).trans_lt (hrange w.val.1 w.property.1.1)
  have hd : Pairwise (Disjoint on K) := pairwise_disjoint_firstEligibleCells P
  have hmeas (w : I) : MeasurableSet (K w) := measurableSet_cleanWordCell w.val
  have hlow : ν C ≤ ∑' w : I, ν (K w) := by
    rw [← measure_iUnion hd hmeas]
    exact measure_mono hcover
  have hupper : (∑' w : I, ν (K w ∩ Bᶜ)) ≤ ν (U \ B) := by
    rw [← measure_iUnion (fun w v h ↦ (hd h).mono inter_subset_left inter_subset_left)
      (fun w ↦ (hmeas w).inter hB.compl)]
    apply measure_mono
    intro x hx
    obtain ⟨w, hxw, hxb⟩ := mem_iUnion.mp hx
    exact ⟨hKU w hxw, hxb⟩
  have hsel : ∃ w : I, 0 < ν (K w) ∧ ν (K w ∩ Bᶜ) ≤ δ * ν (K w) := by
    by_contra! h
    have hl (w : I) : δ * ν (K w) ≤ ν (K w ∩ Bᶜ) := by
      by_cases hz : ν (K w) = 0
      · simp [hz]
      · exact (h w (pos_iff_ne_zero.mpr hz)).le
    have hh := (mul_le_mul' le_rfl hlow : δ * ν C ≤ δ * ∑' w : I, ν (K w))
    rw [← ENNReal.tsum_mul_left] at hh
    exact hsmall.2.not_ge (hh.trans ((tsum_le_tsum hl).trans hupper))
  obtain ⟨w, hpos', hratio⟩ := hsel
  have hz : ν (K w) = ν (range (wordMap (List.ofFn w.val.2))) := measure_sdiff_null hnull
  have hz' : ν (K w ∩ Bᶜ) = ν (range (wordMap (List.ofFn w.val.2)) ∩ Bᶜ) := by
    exact (show K w ∩ Bᶜ = (range (wordMap (List.ofFn w.val.2)) ∩ Bᶜ) \ carpetAllCellBoundaries
      from by ext x; simp only [K, cleanWordCell, mem_inter_iff, Set.mem_sdiff]; tauto) ▸ measure_sdiff_null hnull
  rw [hz] at hpos' hratio
  rw [hz'] at hratio
  exact ⟨w.val, hN.trans w.property.1.1, w.property.1.2.1, hpos', hratio⟩

end CarpetEnergy
