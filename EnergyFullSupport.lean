import EnergyDominance
import EnergyLocality

/-!
# Full support of energy-dominant measures

Uniform regularity and scalar truncation give finite-energy cutoffs.
Locality carries all the cutoff energy inside the open set.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A cutoff equal to one at the center and zero outside a given ball. -/
theorem exists_continuous_cutoff (x : CarpetPoints) {r : ℝ} (hr : 0 < r) :
    ∃ (u : C(CarpetPoints, ℝ)), continuousLp p u ∈ E.domain ∧
      u x = 1 ∧ (∀ z ∉ ball x r, u z = 0) ∧ ∀ z, u z ∈ Icc (0 : ℝ) 1 := by
  let b : C(CarpetPoints, ℝ) :=
    ⟨fun z ↦ max (1 - dist z x / r) 0,
      (continuous_const.sub ((continuous_id.dist continuous_const).div_const _)).max continuous_const⟩
  have hbx : b x = 1 := by change max (1 - dist x x / r) 0 = 1; simp
  have hbz (z : CarpetPoints) (hz : z ∉ ball x r) : b z = 0 := by
    change max (1 - dist z x / r) 0 = 0
    have hzr : r ≤ dist z x := not_lt.mp hz
    exact max_eq_right (sub_nonpos.mpr ((le_div_iff₀ hr).mpr (by simpa using hzr)))
  obtain ⟨v, hv, happ⟩ := E.regular_sup b (1 / 3) (by norm_num)
  have hclose (z : CarpetPoints) : |v z - b z| < 1 / 3 := by
    rw [← Real.norm_eq_abs]
    exact ((v - b).norm_coe_le_norm z).trans_lt happ
  let φ (t : ℝ) := (3 : ℝ) * min (max (t - 1 / 3) 0) (1 / 3)
  have hφ : Continuous φ := continuous_const.mul
    (((continuous_id.sub continuous_const).max continuous_const).min continuous_const)
  let u := (⟨φ, hφ⟩ : C(ℝ, ℝ)).comp v
  let f : E.domain := ⟨continuousLp p v, hv⟩
  let g := E.shiftedTruncation (1 / 3) (1 / 3) f
  have hu : continuousLp p u = (((3 : ℝ) • g : E.domain) : CarpetLp p) := by
    apply Lp.ext
    filter_upwards [continuousLp_ae_eq p u, continuousLp_ae_eq p v,
      E.shiftedTruncation_ae (1 / 3) (by norm_num : (0 : ℝ) < 1 / 3) f,
      Lp.coeFn_smul (3 : ℝ) (g : CarpetLp p)] with z h1 h2 h3 h4
    change continuousLp p u z = ((3 : ℝ) • (g : CarpetLp p)) z
    rw [h1, h4, Pi.smul_apply, h3]
    change φ (v z) = 3 * min (max ((continuousLp p v) z - 1 / 3) 0) (1 / 3)
    rw [h2]
  refine ⟨u, hu.symm ▸ ((3 : ℝ) • g : E.domain).property, ?_, ?_, ?_⟩
  · change φ (v x) = 1
    have hx := hclose x
    rw [hbx, abs_lt] at hx
    have h : 1 / 3 ≤ v x - 1 / 3 := by linarith [hx.1]
    dsimp only [φ]
    rw [min_eq_right (h.trans (le_max_left _ _))]
    norm_num
  · intro z hz
    change φ (v z) = 0
    have hvz := hclose z
    rw [hbz z hz, sub_zero, abs_lt] at hvz
    dsimp only [φ]
    rw [max_eq_right (by linarith [hvz.2]), min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 3),
      mul_zero]
  · intro z
    change 0 ≤ φ (v z) ∧ φ (v z) ≤ 1
    unfold φ
    exact ⟨mul_nonneg (by norm_num) (le_min (le_max_right _ _) (by norm_num)),
      by linarith [min_le_right (max (v z - 1 / 3) 0) (1 / 3)]⟩

/-- Every measure dominating all energy measures has full support. -/
theorem energyDominant_pos_of_isOpen (μ : Measure CarpetPoints)
    (hdom : ∀ f, E.energyMeasure f ≪ μ) {U : Set CarpetPoints}
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U := by
  by_contra! h
  have hzero : μ U = 0 := nonpos_iff_eq_zero.mp h
  by_cases hfull : U = univ
  · obtain ⟨f, hf⟩ := E.exists_energy_ne_zero
    have hz := hdom f hzero
    rw [hfull, E.energyMeasure_univ, ENNReal.coe_eq_zero] at hz
    exact hf hz
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨u, hu, hux, huz, _⟩ := E.exists_continuous_cutoff x hr
  let v : E.domain := ⟨continuousLp p u, hu⟩
  have hcompl : E.energyMeasure v Uᶜ = 0 :=
    measure_mono_null (fun z hz ↦ huz z (fun hb ↦ hz (hball hb)))
      (E.energyMeasure_levelSet_eq_zero u hu 0)
  have htotal : E.energyMeasure v univ = 0 := by
    rw [← union_compl_self U, measure_union disjoint_compl_right hU.measurableSet.compl,
      hcompl, hdom v hzero, add_zero]
  rw [E.energyMeasure_univ, ENNReal.coe_eq_zero] at htotal
  obtain ⟨a, ha⟩ := (E.zero_iff_constant v).1 htotal
  have hconst : (u : CarpetPoints → ℝ) = fun _ ↦ a := by
    apply Measure.eq_of_ae_eq (μ := carpetMeasure) _ u.continuous continuous_const
    apply (continuousLp_ae_eq p u).symm.trans
    change continuousLp p u = constantLp p a at ha
    rw [ha]
    exact Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a
  obtain ⟨y, hy⟩ := nonempty_compl.mpr hfull
  exact zero_ne_one ((huz y (fun hy' ↦ hy (hball hy'))).symm.trans
    ((congrFun hconst y).trans ((congrFun hconst x).symm.trans hux)))

end CarpetEnergy.SelfSimilarPEnergy
