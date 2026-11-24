import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Small ball covers of points of unbounded upper density
-/

open Filter Function Metric MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal

namespace CarpetEnergy

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V]

/-- The points where no finite upper power bound holds at small radii. -/
def UnboundedUpperBallDensity (μ : Measure V) (s : ℝ) : Set V :=
  {x | ∀ M > (0 : ℝ), ∀ R > (0 : ℝ), ∃ r ∈ Ioo 0 R,
      ENNReal.ofReal (M * r ^ s) ≤ μ (ball x r)}

omit [SeparableSpace V] in
set_option maxHeartbeats 1400000 in
theorem measurableSet_unboundedUpperBallDensity [SecondCountableTopology V]
    (μ : Measure V) [IsFiniteMeasure μ] {s : ℝ} (hs : 0 ≤ s) :
    MeasurableSet (UnboundedUpperBallDensity μ s) := by
  let C (m n : ℕ) (r : ℚ) : Set V :=
    if (r : ℝ) ∈ Ioo 0 (1 / ((n : ℝ) + 1)) then
      {x | ENNReal.ofReal (((m : ℝ) + 1) * (r : ℝ) ^ s) ≤ μ (ball x r)}
    else ∅
  have hm (r : ℝ) : Measurable (fun x : V ↦ μ (ball x r)) := by
    have h : MeasurableSet {z : V × V | dist z.2 z.1 < r} :=
      measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const
    exact measurable_measure_prodMk_left h
  have hC (m n : ℕ) (r : ℚ) : MeasurableSet (C m n r) := by
    dsimp only [C]
    split
    · exact measurableSet_le measurable_const (hm r)
    · exact MeasurableSet.empty
  suffices he : UnboundedUpperBallDensity μ s = ⋂ m : ℕ, ⋂ n : ℕ, ⋃ r : ℚ, C m n r by
    rw [he]
    exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun n ↦ MeasurableSet.iUnion (hC m n)
  ext x
  simp only [mem_iInter, mem_iUnion]
  constructor
  · intro hx m n
    have hm₀ : 0 < (m : ℝ) + 1 := by positivity
    have hd : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨r, hr, hmass⟩ := hx (((m : ℝ) + 1) * (2 : ℝ) ^ s)
      (by positivity) ((1 / ((n : ℝ) + 1)) / 2) (half_pos hd)
    obtain ⟨t, hrt, ht⟩ := exists_rat_btwn (show r < 2 * r by linarith [hr.1])
    have ht' : (t : ℝ) ∈ Ioo 0 (1 / ((n : ℝ) + 1)) :=
      ⟨hr.1.trans hrt, ht.trans (by linarith [hr.2])⟩
    refine ⟨t, ?_⟩
    dsimp only [C]
    rw [ite_eq_left ht']
    change ENNReal.ofReal (((m : ℝ) + 1) * (t : ℝ) ^ s) ≤ μ (ball x t)
    have hb := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ht'.1.le ht.le hs) hm₀.le
    rw [Real.mul_rpow (by norm_num) hr.1.le, ← mul_assoc] at hb
    exact (ENNReal.ofReal_le_ofReal hb).trans
      (hmass.trans (measure_mono (ball_subset_ball hrt.le)))
  · intro hx M hM R hR
    obtain ⟨m : ℕ, hm⟩ := exists_nat_gt M
    obtain ⟨n : ℕ, hn⟩ := exists_nat_one_div_lt hR
    obtain ⟨t, ht⟩ := hx m n
    unfold C at ht
    split at ht
    · rename_i ht'
      refine ⟨t, ⟨ht'.1, ht'.2.trans hn⟩, ?_⟩
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (hm.le.trans (le_add_of_nonneg_right zero_le_one)) (Real.rpow_nonneg ht'.1.le s))).trans ht
    · exact (notMem_empty x ht).elim

omit [BorelSpace V] [SeparableSpace V] in
theorem exists_upper_density_bound_of_notMem {μ : Measure V} [IsFiniteMeasure μ]
    {s : ℝ} {x : V} (hx : x ∉ UnboundedUpperBallDensity μ s) :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧ ∀ r ∈ Ioo 0 R, μ.real (ball x r) ≤ M * r ^ s := by
  change ¬ ∀ M > (0 : ℝ), ∀ R > (0 : ℝ), ∃ r ∈ Ioo 0 R,
    ENNReal.ofReal (M * r ^ s) ≤ μ (ball x r) at hx
  push Not at hx
  obtain ⟨M, hM, R, hR, h⟩ := hx
  refine ⟨M, R, hM, hR, fun r hr ↦ ?_⟩
  have hnn : 0 ≤ M * r ^ s := mul_nonneg hM.le (Real.rpow_nonneg hr.1.le _)
  simpa only [Measure.real, ENNReal.toReal_ofReal hnn] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (h r hr).le

set_option maxHeartbeats 2000000 in
/-- A compact subset of the unbounded-density set has a finite cover
whose sum of radius powers is arbitrarily small. -/
theorem exists_small_finite_cover_of_unbounded_density
    (μ : Measure V) [IsFiniteMeasure μ] {s : ℝ}
    {K : Set V} (hK : IsCompact K) (hKB : K ⊆ UnboundedUpperBallDensity μ s)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ (m : ℕ) (x : Fin m → V) (r : Fin m → ℝ),
      (∀ i, 0 < r i ∧ r i < η) ∧ K ⊆ (⋃ i, ball (x i) (r i)) ∧
        (∑ i, (r i) ^ s) ≤ ε := by
  classical
  let M := (5 : ℝ) ^ s * μ.real univ / ε + 1
  have hM : 0 < M := add_pos_of_nonneg_of_pos (by dsimp [Measure.real]; positivity) one_pos
  have hMε : (5 : ℝ) ^ s * μ.real univ ≤ M * ε := by
    have he := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (a := (5 : ℝ) ^ s * μ.real univ / ε)
        (show (0 : ℝ) ≤ 1 by norm_num)) hε.le
    dsimp only [M]
    rw [div_mul_cancel₀ _ hε.ne'] at he
    exact he
  let R := η / 5
  have hR : 0 < R := div_pos hη (by norm_num)
  have hrad (x : K) : ∃ r ∈ Ioo 0 R, ENNReal.ofReal (M * r ^ s) ≤ μ (ball x.val r) :=
    hKB x.property M hM R hR
  choose r hr hmass using hrad
  obtain ⟨A, _, hdisj, hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (univ : Set K) Subtype.val r R (fun a _ ↦ (hr a).2.le) 5 (by norm_num)
  let B (x : A) := ball x.val.val (5 * r x.val)
  have hCount : A.Countable := hdisj.countable_of_isOpen (fun _ _ ↦ isOpen_ball)
    (fun x _ ↦ ⟨x.val, mem_ball_self (hr x).1⟩)
  let : Countable A := hCount.to_subtype
  have hdisj' : Pairwise (Disjoint on fun x : A ↦ ball x.val.val (r x.val)) := by
    intro a b hab
    exact hdisj a.property b.property (fun hx ↦ hab (Subtype.ext hx))
  have hb : K ⊆ ⋃ x : A, B x := by
    intro y hy
    obtain ⟨a, ha, hsub⟩ := hcover ⟨y, hy⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hsub (mem_ball_self (hr ⟨y, hy⟩).1)⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover B (fun _ ↦ isOpen_ball) hb
  have hsum : ∑ a ∈ S, μ (ball a.val.val (r a.val)) ≤ μ univ := by
    calc
      _ ≤ ∑' a : A, μ (ball a.val.val (r a.val)) := sum_le_tsum S
      _ = μ (⋃ a : A, ball a.val.val (r a.val)) :=
        (measure_iUnion hdisj' (fun _ ↦ isOpen_ball.measurableSet)).symm
      _ ≤ _ := measure_mono (subset_univ _)
  have hsum' : ∑ a ∈ S, M * r a.val ^ s ≤ μ.real univ := by
    have he := Finset.sum_le_sum (s := S) (fun a _ ↦ hmass a.val)
    have hfin := ENNReal.toReal_mono (measure_ne_top _ _) (he.trans hsum)
    rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.ofReal_ne_top)] at hfin
    simpa only [Measure.real, ENNReal.toReal_ofReal (mul_nonneg hM.le (Real.rpow_nonneg (hr _).1.le _))] using hfin
  have hcost : ∑ a ∈ S, (5 * r a.val) ^ s ≤ ε := by
    simp only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) (hr _).1.le, ← Finset.mul_sum]
    have he := mul_le_mul_of_nonneg_left hsum' (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) s)
    rw [← Finset.mul_sum, mul_left_comm] at he
    exact (mul_le_mul_iff_right₀ hM).mp (he.trans hMε)
  let e := S.equivFin.symm
  refine ⟨S.card, fun i ↦ (e i).val.val.val, fun i ↦ 5 * r (e i).val.val, ?_, ?_, ?_⟩
  · intro i
    have h := hr (e i).val.val
    exact ⟨mul_pos (by norm_num) h.1, by dsimp only [R] at h; linarith [h.2]⟩
  · intro y hy
    obtain ⟨a, ha, hay⟩ := mem_iUnion₂.mp (hS hy)
    exact mem_iUnion.mpr ⟨e.symm ⟨a, ha⟩, by simpa only [Equiv.apply_symm_apply] using hay⟩
  · change (∑ i, (5 * r (e i).val.val) ^ s) ≤ ε
    rw [Equiv.sum_comp e (fun a : S ↦ (5 * r a.val.val) ^ s)]
    exact (Finset.sum_coe_sort S (fun a : A ↦ (5 * r a.val) ^ s)).trans_le hcost

end CarpetEnergy
