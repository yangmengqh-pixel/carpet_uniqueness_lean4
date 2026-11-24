import CarpetSymmetry
import InvariantDensity
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Regular

/-!
# The normalized measure on the carpet

Push forward the uniform product probability on addresses by the coding map.
-/

open Filter Function Metric Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace CarpetEnergy

instance : CompactSpace CarpetPoints := isCompact_iff_compactSpace.mp carpet.isCompact

private noncomputable def digitMeasure : Measure (Fin 8) := uniformOn univ

private instance : IsProbabilityMeasure digitMeasure :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn (univ : Set (Fin 8))))

private theorem digitMeasure_singleton (i : Fin 8) : digitMeasure {i} = (8 : ℝ≥0∞)⁻¹ := by
  have h := uniformOn_apply_finset (s := (Finset.univ : Finset (Fin 8))) (t := {i})
  rw [Finset.coe_univ, Finset.coe_singleton, Finset.univ_inter, Finset.card_singleton,
    Finset.card_univ, Fintype.card_fin, Nat.cast_one, div_eq_mul_inv, one_mul] at h
  exact h

/-- The fair product probability measure on infinite addresses. -/
noncomputable def addressMeasure : Measure Addresses :=
  Measure.infinitePi fun _ ↦ digitMeasure

instance : IsProbabilityMeasure addressMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ ↦ digitMeasure))

private theorem measurable_prepend (i : Fin 8) : Measurable (prepend i) := by
  apply Measurable.of_eval
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

open scoped Classical in
private theorem prepend_preimage_box (i : Fin 8) (s : Finset ℕ) (t : ℕ → Set (Fin 8)) :
    prepend i ⁻¹' Set.pi (↑s) t =
      if 0 ∈ s → i ∈ t 0 then
        Set.pi (↑((s.erase 0).image Nat.pred)) (fun n ↦ t (n + 1))
      else ∅ := by
  classical
  have hmem (n : ℕ) : n ∈ (s.erase 0).image Nat.pred ↔ n + 1 ∈ s := by
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨j, ⟨hj, hjs⟩, h⟩
      cases j with
      | zero => contradiction
      | succ j =>
        have h' : j = n := h
        exact h' ▸ hjs
    · intro h
      exact ⟨n + 1, ⟨Nat.succ_ne_zero n, h⟩, rfl⟩
  ext a
  simp only [mem_preimage, Set.mem_pi, Finset.mem_coe]
  by_cases hi : 0 ∈ s → i ∈ t 0
  · simp only [ite_eq_left hi, Set.mem_pi, Finset.mem_coe, hmem]
    constructor
    · exact fun h n hn ↦ h (n + 1) hn
    · intro h n hn
      cases n with
      | zero => exact hi hn
      | succ n => exact h n hn
  · simp only [ite_eq_right hi, mem_empty_iff_false, iff_false]
    exact fun h ↦ hi (h 0)

private theorem shifted_box_mass (s : Finset ℕ) (t : ℕ → Set (Fin 8))
    (ht : ∀ n, MeasurableSet (t n)) :
    addressMeasure (Set.pi (↑((s.erase 0).image Nat.pred)) (fun n ↦ t (n + 1))) =
      ∏ n ∈ s.erase 0, digitMeasure (t n) := by
  rw [addressMeasure, Measure.infinitePi_pi _ (fun n _ ↦ ht _)]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro n hn
    have hn₀ := (Finset.mem_erase.mp hn).1
    have h : n.pred + 1 = n := Nat.succ_pred_eq_of_ne_zero hn₀
    rw [h]
  · intro a ha b hb hab
    have ha₀ := (Finset.mem_erase.mp ha).1
    have hb₀ := (Finset.mem_erase.mp hb).1
    exact (Nat.succ_pred_eq_of_ne_zero ha₀).symm.trans
      ((congrArg Nat.succ hab).trans (Nat.succ_pred_eq_of_ne_zero hb₀))

private theorem addressMeasure_eq_sum_prepend :
    addressMeasure = Measure.sum (fun i : Fin 8 ↦ (8 : ℝ≥0∞)⁻¹ •
      addressMeasure.map (prepend i)) := by
  symm
  apply Measure.eq_infinitePi (fun _ ↦ digitMeasure)
  intro s t ht
  classical
  have hbox : MeasurableSet (Set.pi (↑s) t) := .pi s.countable_toSet (fun i _ ↦ ht i)
  rw [Measure.sum_apply _ hbox, tsum_fintype]
  simp only [smul_apply, smul_eq_mul, Measure.map_apply (measurable_prepend _) hbox,
    prepend_preimage_box]
  let b := ∏ n ∈ s.erase 0, digitMeasure (t n)
  have hm := shifted_box_mass s t ht
  change addressMeasure _ = b at hm
  simp_rw [apply_ite addressMeasure, hm, measure_empty, mul_ite, mul_zero]
  have hsum : ∑ i : Fin 8, (if i ∈ t 0 then (8 : ℝ≥0∞)⁻¹ else 0) = digitMeasure (t 0) := by
    conv_rhs => rw [← Measure.sum_smul_dirac digitMeasure]
    simp only [Measure.sum_apply _ (ht 0), tsum_fintype, smul_apply, smul_eq_mul,
      digitMeasure_singleton, Measure.dirac_apply' _ (ht 0), Set.indicator_apply, Pi.one_apply,
      mul_ite, mul_one, mul_zero]
  by_cases hz : 0 ∈ s
  · have hcond (i : Fin 8) : (0 ∈ s → i ∈ t 0) ↔ i ∈ t 0 := ⟨fun h ↦ h hz, fun h _ ↦ h⟩
    simp only [hcond]
    calc
      _ = (∑ i : Fin 8, (if i ∈ t 0 then (8 : ℝ≥0∞)⁻¹ else 0)) * b := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = _ := hsum ▸ Finset.mul_prod_erase s (fun n ↦ digitMeasure (t n)) hz
  · simp only [hz, false_implies, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    simp [b, Finset.erase_eq_of_notMem hz]

/-- The pushforward of the fair product measure under the coding map. -/
noncomputable def carpetMeasure : Measure CarpetPoints := addressMeasure.map coding

private theorem measurable_coding : Measurable coding := continuous_coding.measurable

instance : IsProbabilityMeasure carpetMeasure :=
  inferInstanceAs (IsProbabilityMeasure (addressMeasure.map coding))

theorem carpetMeasure_eq_sum_cells :
    carpetMeasure = Measure.sum (fun i : Fin 8 ↦ (8 : ℝ≥0∞)⁻¹ •
      carpetMeasure.map (cellMap i)) := by
  conv_lhs => rw [carpetMeasure, addressMeasure_eq_sum_prepend]
  rw [Measure.map_sum measurable_coding.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul _ measurable_coding.aemeasurable, Measure.map_map measurable_coding
    (measurable_prepend i), carpetMeasure,
    Measure.map_map (measurableEmbedding_cellMap i).measurable measurable_coding]
  exact congrArg (fun f : Addresses → CarpetPoints ↦ (8 : ℝ≥0∞)⁻¹ • addressMeasure.map f)
    (funext (coding_prepend i))

private def coordinateLevel (j : Fin 2) (t : ℝ) : Set CarpetPoints :=
  {x | (x : Plane) j = t}

private theorem measurableSet_coordinateLevel (j : Fin 2) (t : ℝ) :
    MeasurableSet (coordinateLevel j t) :=
  ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) j).comp continuous_subtypeVal).measurable
    (measurableSet_singleton t)

private theorem preimage_coordinateLevel (i : Fin 8) (j : Fin 2) (t : ℝ) :
    cellMap i ⁻¹' coordinateLevel j t = coordinateLevel j (3 * t - 2 * cellCenter i j) := by
  ext x
  change cellSimilarity i (x : Plane) j = t ↔ _
  rw [cellSimilarity_coord]
  change _ ↔ (x : Plane) j = 3 * t - 2 * cellCenter i j
  constructor <;> intro h <;> linarith

private theorem exists_empty_preimage_coordinateLevel (j : Fin 2) (t : ℝ) :
    ∃ i, cellMap i ⁻¹' coordinateLevel j t = ∅ := by
  have h0 : cellCenter (0 : Fin 8) j = 0 := by
    fin_cases j <;> norm_num [cellCenter, WithLp.toLp, Fin.reduceFinMk]
  have h4 : cellCenter (4 : Fin 8) j = 1 := by
    fin_cases j <;> norm_num [cellCenter, WithLp.toLp, Fin.reduceFinMk]
  by_cases ht : t ≤ 1 / 3
  · refine ⟨4, eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_⟩
    rw [preimage_coordinateLevel] at hx
    have h : (x : Plane) j = 3 * t - 2 * cellCenter 4 j := hx
    linarith [(carpet_coord_mem_Icc x j).1, h4]
  · refine ⟨0, eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_⟩
    rw [preimage_coordinateLevel] at hx
    have h : (x : Plane) j = 3 * t - 2 * cellCenter 0 j := hx
    linarith [(carpet_coord_mem_Icc x j).2, h0]

private theorem carpetMeasure_coordinateLevel_le (n : ℕ) (j : Fin 2) (t : ℝ) :
    carpetMeasure (coordinateLevel j t) ≤ ((7 : ℝ≥0∞) / 8) ^ n := by
  induction n generalizing t with
  | zero => simpa only [pow_zero] using prob_le_one (μ := carpetMeasure)
  | succ n ih =>
    classical
    obtain ⟨k, hk⟩ := exists_empty_preimage_coordinateLevel j t
    nth_rw 1 [carpetMeasure_eq_sum_cells]
    rw [Measure.sum_apply _ (measurableSet_coordinateLevel j t), tsum_fintype]
    simp only [smul_apply, smul_eq_mul, (measurableEmbedding_cellMap _).map_apply]
    let b (i : Fin 8) := (8 : ℝ≥0∞)⁻¹ * carpetMeasure (cellMap i ⁻¹' coordinateLevel j t)
    change ∑ i, b i ≤ _
    have hbk : b k = 0 := by simp [b, hk]
    rw [← Finset.sum_erase_add _ b (Finset.mem_univ k), hbk, add_zero]
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin 8)).erase k,
          (8 : ℝ≥0∞)⁻¹ * ((7 : ℝ≥0∞) / 8) ^ n := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [b]
        rw [preimage_coordinateLevel]
        gcongr
        exact ih _
      _ = _ := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, pow_succ']
        simp only [Nat.reduceSub, Nat.cast_ofNat, div_eq_mul_inv]

/-- The measure gives zero mass to every horizontal or vertical line. -/
theorem carpetMeasure_coordinateLevel (j : Fin 2) (t : ℝ) :
    carpetMeasure {x | (x : Plane) j = t} = 0 := by
  apply nonpos_iff_eq_zero.mp
  have h' : (7 : ℝ≥0∞) / 8 < 1 := by
    rw [ENNReal.div_lt_iff (by simp) (by simp), one_mul]
    norm_num
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h')
  exact Eventually.of_forall (fun n ↦ carpetMeasure_coordinateLevel_le n j t)

/-- Each first-level pushforward is absolutely continuous with respect to the
carpet measure. -/
theorem map_cellMap_absolutelyContinuous (i : Fin 8) :
    carpetMeasure.map (cellMap i) ≪ carpetMeasure := by
  conv_rhs => rw [carpetMeasure_eq_sum_cells]
  exact Measure.absolutelyContinuous_sum_right i
    (Measure.absolutelyContinuous_smul (by norm_num))

private theorem measure_inter_range_cellMap_eq_zero {i k : Fin 8} (hik : i ≠ k) :
    carpetMeasure (range (cellMap i) ∩ range (cellMap k)) = 0 := by
  have hne : cellDigit i ≠ cellDigit k := fun h ↦ hik (cellDigit_injective h)
  obtain ⟨j, hj⟩ : ∃ j, cellDigit i j ≠ cellDigit k j := by
    by_contra! h
    exact hne (funext h)
  have hbound (l : Fin 8) (x : CarpetPoints) :
      ((cellDigit l j : ℕ) : ℝ) ≤ 3 * ((cellMap l x : CarpetPoints) : Plane) j ∧
        3 * ((cellMap l x : CarpetPoints) : Plane) j ≤ ((cellDigit l j : ℕ) : ℝ) + 1 := by
    change _ ≤ 3 * cellSimilarity l x j ∧ 3 * cellSimilarity l x j ≤ _
    rw [cellSimilarity_coord, cellDigit_cast]
    exact ⟨by linarith [(carpet_coord_mem_Icc x j).1], by linarith [(carpet_coord_mem_Icc x j).2]⟩
  rcases lt_or_gt_of_ne hj with hlt | hlt
  · apply measure_mono_null ?_ (carpetMeasure_coordinateLevel j ((((cellDigit i j : ℕ) : ℝ) + 1) / 3))
    rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hi := hbound i x
    have hk := hbound k y
    rw [hx] at hi
    rw [hy] at hk
    have hgapN : (cellDigit i j : ℕ) + 1 ≤ (cellDigit k j : ℕ) := Nat.succ_le_of_lt hlt
    have hgap : ((cellDigit i j : ℕ) : ℝ) + 1 ≤ ((cellDigit k j : ℕ) : ℝ) := by
      exact_mod_cast hgapN
    change (z : Plane) j = _
    linarith [hi.2, hk.1]
  · apply measure_mono_null ?_ (carpetMeasure_coordinateLevel j ((((cellDigit k j : ℕ) : ℝ) + 1) / 3))
    rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hi := hbound i x
    have hk := hbound k y
    rw [hx] at hi
    rw [hy] at hk
    have hgapN : (cellDigit k j : ℕ) + 1 ≤ (cellDigit i j : ℕ) := Nat.succ_le_of_lt hlt
    have hgap : ((cellDigit k j : ℕ) : ℝ) + 1 ≤ ((cellDigit i j : ℕ) : ℝ) := by
      exact_mod_cast hgapN
    change (z : Plane) j = _
    linarith [hi.1, hk.2]

theorem carpetMeasure_restrict_cellMap (i : Fin 8) :
    carpetMeasure.restrict (range (cellMap i)) =
      (8 : ℝ≥0∞)⁻¹ • carpetMeasure.map (cellMap i) := by
  conv_lhs => rw [carpetMeasure_eq_sum_cells]
  apply restrict_eq_smul_map_of_null_overlaps cellMap measurableEmbedding_cellMap
  intro j hj
  have hpre : cellMap j ⁻¹' (range (cellMap i) ∩ range (cellMap j)) =
      cellMap j ⁻¹' range (cellMap i) := by rw [preimage_inter, preimage_range, inter_univ]
  rw [← hpre, ← (measurableEmbedding_cellMap j).map_apply]
  exact map_cellMap_absolutelyContinuous j (measure_inter_range_cellMap_eq_zero (Ne.symm hj))

/-- Scaling on measurable subsets under a first-level cell embedding. -/
theorem carpetMeasure_image_cellMap (i : Fin 8) {A : Set CarpetPoints} (hA : MeasurableSet A) :
    carpetMeasure (cellMap i '' A) = (8 : ℝ≥0∞)⁻¹ * carpetMeasure A := by
  have h := congrArg (fun ν : Measure CarpetPoints ↦ ν (cellMap i '' A))
    (carpetMeasure_restrict_cellMap i)
  rw [Measure.restrict_apply ((measurableEmbedding_cellMap i).measurableSet_image.mpr hA),
    inter_eq_left.mpr (image_subset_range _ _), smul_apply, smul_eq_mul,
    (measurableEmbedding_cellMap i).map_apply, preimage_image_eq _ (injective_cellMap i)] at h
  exact h

/-- The manuscript's normalization for a cell of any finite level. -/
theorem carpetMeasure_range_wordMap (w : List (Fin 8)) :
    carpetMeasure (range (wordMap w)) = ((8 : ℝ≥0∞)⁻¹) ^ w.length := by
  induction w with
  | nil => simp [wordMap, measure_univ]
  | cons i w ih =>
    rw [wordMap, range_comp, carpetMeasure_image_cellMap _
      (measurableEmbedding_wordMap w).measurableSet_range, ih, List.length_cons, pow_succ']

theorem dist_wordMap (w : List (Fin 8)) (x y : CarpetPoints) :
    dist (wordMap w x) (wordMap w y) = (1 / 3 : ℝ) ^ w.length * dist x y := by
  induction w with
  | nil => simp [wordMap]
  | cons i w ih =>
    change dist (cellSimilarity i (wordMap w x)) (cellSimilarity i (wordMap w y)) = _
    have h : dist (wordMap w x : Plane) (wordMap w y : Plane) = _ := ih
    rw [dist_cellSimilarity, h, List.length_cons, pow_succ', mul_assoc]

theorem exists_wordMap_range (n : ℕ) (x : CarpetPoints) :
    ∃ w : Fin n → Fin 8, x ∈ range (wordMap (List.ofFn w)) := by
  induction n generalizing x with
  | zero => exact ⟨Fin.elim0, x, rfl⟩
  | succ n ih =>
    obtain ⟨i, y, hy, hxy⟩ := mem_iUnion.mp (carpet_eq_iUnion.le x.property)
    let yK : CarpetPoints := ⟨y, hy⟩
    obtain ⟨w, z, hz⟩ := ih yK
    refine ⟨Fin.cons i w, z, ?_⟩
    rw [List.ofFn_cons]
    exact (congrArg (cellMap i) hz).trans (Subtype.ext hxy)

theorem wordMap_dist_le (n : ℕ) (w : Fin n → Fin 8) {x y : CarpetPoints}
    (hx : x ∈ range (wordMap (List.ofFn w))) (hy : y ∈ range (wordMap (List.ofFn w))) :
    dist x y ≤ (1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints) := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  rw [dist_wordMap, List.length_ofFn]
  exact mul_le_mul_of_nonneg_left
    (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x') (mem_univ y')) (by positivity)

theorem tendsto_wordMap_radius :
    Tendsto (fun n : ℕ ↦ (1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints)) atTop (𝓝 0) := by
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num)
      (by norm_num)).mul_const (diam (univ : Set CarpetPoints))

/-- Every nonempty open set has positive carpet measure. -/
instance : carpetMeasure.IsOpenPosMeasure where
  open_pos U hU hne := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨n, hn⟩ := (tendsto_wordMap_radius.eventually_lt_const hε).exists
    obtain ⟨w, hw⟩ := exists_wordMap_range n x
    have hsubset : range (wordMap (List.ofFn w)) ⊆ U := fun y hy ↦ hball
      (mem_ball.mpr ((wordMap_dist_le n w hy hw).trans_lt hn))
    apply ne_of_gt
    refine lt_of_lt_of_le ?_ (measure_mono hsubset)
    rw [carpetMeasure_range_wordMap]
    exact pos_iff_ne_zero.mpr (pow_ne_zero _ (by simp))

private theorem measure_inter_range_wordMap_eq_zero {w v : List (Fin 8)}
    (hlen : w.length = v.length) (hne : w ≠ v) :
    carpetMeasure (range (wordMap w) ∩ range (wordMap v)) = 0 := by
  induction w generalizing v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    exact (hne hv.symm).elim
  | cons i w ih =>
    cases v with
    | nil => simp at hlen
    | cons j v =>
      simp only [wordMap, range_comp]
      by_cases hij : i = j
      · subst j
        rw [← image_inter (injective_cellMap i), carpetMeasure_image_cellMap i
          ((measurableEmbedding_wordMap w).measurableSet_range.inter
            (measurableEmbedding_wordMap v).measurableSet_range)]
        rw [ih (Nat.succ.inj hlen) (fun h ↦ hne (congrArg (List.cons i) h)), mul_zero]
      · exact measure_mono_null
          (inter_subset_inter (image_subset_range _ _) (image_subset_range _ _))
          (measure_inter_range_cellMap_eq_zero hij)

private theorem measure_closed_le_of_cell_masses {ν : Measure CarpetPoints}
    (hν : ∀ w : List (Fin 8), ν (range (wordMap w)) = ((8 : ℝ≥0∞)⁻¹) ^ w.length)
    {A : Set CarpetPoints} (hA : IsClosed A) :
    ν A ≤ carpetMeasure A := by
  classical
  have hbound (n : ℕ) :
      ν A ≤ carpetMeasure (cthickening
        ((1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints)) A) := by
    let C (w : Fin n → Fin 8) := range (wordMap (List.ofFn w))
    let I := Finset.univ.filter (fun w ↦ (C w ∩ A).Nonempty)
    have hcover : A ⊆ ⋃ w ∈ I, C w := by
      intro x hx
      obtain ⟨w, hw⟩ := exists_wordMap_range n x
      exact mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hw, hx⟩, hw⟩
    have hsub : ⋃ w ∈ I, C w ⊆ cthickening
        ((1 / 3 : ℝ) ^ n * diam (univ : Set CarpetPoints)) A := by
      intro x hx
      obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hx
      obtain ⟨y, hyw, hy⟩ := (Finset.mem_filter.mp hw).2
      exact mem_cthickening_of_dist_le x y _ _ hy (wordMap_dist_le n w hxw hyw)
    have hdisj : (I : Set (Fin n → Fin 8)).Pairwise (AEDisjoint carpetMeasure on C) := by
      intro w _ v _ hwv
      exact measure_inter_range_wordMap_eq_zero
        (by simp)
        (fun h ↦ hwv (List.ofFn_injective h))
    calc
      ν A ≤ ν (⋃ w ∈ I, C w) := measure_mono hcover
      _ ≤ ∑ w ∈ I, ν (C w) := measure_biUnion_finset_le I C
      _ = ∑ w ∈ I, carpetMeasure (C w) := by
        apply Finset.sum_congr rfl
        intro w _
        exact (hν _).trans (carpetMeasure_range_wordMap _).symm
      _ = carpetMeasure (⋃ w ∈ I, C w) :=
        (measure_biUnion_finset₀ hdisj (fun w _ ↦
          (measurableEmbedding_wordMap _).measurableSet_range.nullMeasurableSet)).symm
      _ ≤ _ := measure_mono hsub
  have hlim := (tendsto_measure_cthickening_of_isClosed (μ := carpetMeasure)
    ⟨1, one_pos, measure_ne_top _ _⟩ hA).comp tendsto_wordMap_radius
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)

/-- The finite-word cell masses characterize the normalized carpet measure. -/
theorem eq_carpetMeasure_of_cell_masses {ν : Measure CarpetPoints}
    (hν : ∀ w : List (Fin 8), ν (range (wordMap w)) = ((8 : ℝ≥0∞)⁻¹) ^ w.length) :
    ν = carpetMeasure := by
  have huniv : ν univ = 1 := by simpa [wordMap] using hν []
  have : IsProbabilityMeasure ν := ⟨huniv⟩
  refine Measure.eq_of_le_of_measure_univ_eq ?_
    (huniv.trans (measure_univ (μ := carpetMeasure)).symm)
  refine Measure.le_iff.mpr fun A hA ↦ ?_
  rw [hA.measure_eq_iSup_isCompact ν]
  refine iSup_le fun K ↦ iSup_le fun hK ↦ iSup_le fun hcomp ↦ ?_
  exact (measure_closed_le_of_cell_masses hν hcomp.isClosed).trans (measure_mono hK)

theorem map_cellMap_le (i : Fin 8) :
    carpetMeasure.map (cellMap i) ≤ (8 : ℝ≥0∞) • carpetMeasure := by
  have h : (8 : ℝ≥0∞) • carpetMeasure.restrict (range (cellMap i)) ≤
      (8 : ℝ≥0∞) • carpetMeasure := by
    apply Measure.le_iff'.mpr
    intro A
    simp only [smul_apply, smul_eq_mul]
    gcongr
    exact Measure.restrict_le_self
  rw [carpetMeasure_restrict_cellMap, smul_smul,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_smul] at h
  exact h

/-- The normalized measure is invariant under all eight square symmetries. -/
theorem measurePreserving_carpetSymmetry (σ : SquareSymmetry) :
    MeasurePreserving (carpetSymmetry σ) carpetMeasure carpetMeasure := by
  have hm := (continuous_carpetSymmetry σ).measurable
  refine ⟨hm, eq_carpetMeasure_of_cell_masses fun w ↦ ?_⟩
  obtain ⟨v, hv, hpre⟩ := carpetSymmetry_preimage_wordMap σ w
  rw [Measure.map_apply hm (measurableEmbedding_wordMap w).measurableSet_range, hpre,
    carpetMeasure_range_wordMap, hv]

end CarpetEnergy
