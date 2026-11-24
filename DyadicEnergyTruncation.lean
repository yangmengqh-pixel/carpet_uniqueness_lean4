import DyadicLayerMass
import EnergyBlowup
import EnergyLocality
import EnergySeminorm

/-!
# Dyadic energy truncation

A strip contributes the energy of the original function restricted to that
strip. The dyadic moment bounds and the two countable budgets select a
normalized strip with a sufficiently large plateau.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The moment of a nonnegative continuous function is its Lp norm raised to p. -/
private theorem continuousLp_rpow_norm_eq_lintegral
    (hp₁ : 1 ≤ p) (u : C(CarpetPoints, ℝ)) (hu₀ : ∀ x, 0 ≤ u x) :
    ENNReal.ofReal (‖continuousLp p u‖ ^ p) =
      ∫⁻ x, ENNReal.ofReal (u x) ^ p ∂carpetMeasure := by
  have hp : 0 < p := zero_lt_one.trans_le hp₁
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp₁⟩
  have hLp : ENNReal.ofReal ‖continuousLp p u‖ = eLpNorm u (ENNReal.ofReal p) carpetMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
      eLpNorm_congr_ae (continuousLp_ae_eq p u)]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top u.continuous.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le] at hLp
  have h := congrArg (fun t : ℝ≥0∞ ↦ t ^ p) hLp
  change ENNReal.ofReal ‖continuousLp p u‖ ^ p = _ at h
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (continuousLp p u)) hp.le,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one] at h
  rw [h]
  congr with x
  rw [← ofReal_norm, Real.norm_of_nonneg (hu₀ x)]

/-- The two adjacent dyadic thresholds bound the normalized truncation. -/
private noncomputable def normalizedStrip (u : C(CarpetPoints, ℝ)) (b : ℝ) :
    C(CarpetPoints, ℝ) :=
  ⟨fun x ↦ b⁻¹ * min (max (u x - b) 0) b,
    continuous_const.mul (((u.continuous.sub continuous_const).max continuous_const).min
      continuous_const)⟩

private theorem normalizedStrip_bounds (u : C(CarpetPoints, ℝ)) {b : ℝ} (hb : 0 < b)
    (x : CarpetPoints) :
    0 ≤ normalizedStrip u b x ∧ normalizedStrip u b x ≤ 1 := by
  change 0 ≤ b⁻¹ * min (max (u x - b) 0) b ∧ b⁻¹ * min (max (u x - b) 0) b ≤ 1
  exact ⟨mul_nonneg (inv_nonneg.mpr hb.le) (le_min (le_max_right _ _) hb.le),
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_nonneg.mpr hb.le)).trans_eq
      (inv_mul_cancel₀ hb.ne')⟩

private theorem normalizedStrip_pos_iff (u : C(CarpetPoints, ℝ)) {b : ℝ} (hb : 0 < b)
    (x : CarpetPoints) : 0 < normalizedStrip u b x ↔ b < u x := by
  change 0 < b⁻¹ * min (max (u x - b) 0) b ↔ _
  rw [mul_pos_iff_of_pos_left (inv_pos.mpr hb), lt_min_iff, lt_max_iff]
  simp only [lt_irrefl, or_false, sub_pos, hb, and_true]

private theorem normalizedStrip_eq_one_iff (u : C(CarpetPoints, ℝ)) {b : ℝ} (hb : 0 < b)
    (x : CarpetPoints) : normalizedStrip u b x = 1 ↔ 2 * b ≤ u x := by
  change b⁻¹ * min (max (u x - b) 0) b = 1 ↔ _
  rw [inv_mul_eq_iff_eq_mul₀ hb.ne', mul_one]
  constructor
  · intro h
    have hmax := h ▸ (min_le_left (max (u x - b) 0) b)
    rcases le_max_iff.mp hmax with h | h
    · linarith
    · exact False.elim (hb.not_ge h)
  · intro h
    exact min_eq_right ((show b ≤ u x - b by linarith).trans (le_max_left _ _))

private theorem continuousLp_normalizedStrip (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) {b : ℝ} (hb : 0 < b) :
    continuousLp p (normalizedStrip u b) =
      ((b⁻¹ • E.shiftedTruncation b b ⟨continuousLp p u, hu⟩ : E.domain) : CarpetLp p) := by
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let cut := E.shiftedTruncation b b f
  apply Lp.ext
  filter_upwards [continuousLp_ae_eq p (normalizedStrip u b), continuousLp_ae_eq p u,
    E.shiftedTruncation_ae b hb f, Lp.coeFn_smul b⁻¹ (cut : CarpetLp p)]
    with x hg hx hcut hs
  change continuousLp p u x = u x at hx
  change cut.val x = min (max (f.val x - b) 0) b at hcut
  change continuousLp p (normalizedStrip u b) x = (b⁻¹ • cut.val) x
  rw [hg, hs, Pi.smul_apply, smul_eq_mul, hcut]
  exact congrArg (fun a : ℝ ↦ b⁻¹ * min (max (a - b) 0) b) hx.symm

private theorem energy_normalizedStrip (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) {b : ℝ} (hb : 0 < b)
    (hg : continuousLp p (normalizedStrip u b) ∈ E.domain) :
    (ENNReal.ofReal b) ^ p * (E.energy ⟨continuousLp p (normalizedStrip u b), hg⟩ : ℝ≥0∞) =
      E.energyMeasure ⟨continuousLp p u, hu⟩ (u ⁻¹' Ioo b (2 * b)) := by
  let cut := E.shiftedTruncation b b ⟨continuousLp p u, hu⟩
  let g : E.domain := ⟨continuousLp p (normalizedStrip u b), hg⟩
  have hg' : g = b⁻¹ • cut := Subtype.ext (E.continuousLp_normalizedStrip u hu hb)
  have hcut : b • g = cut := by rw [hg', smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  have henergy := congrArg (fun μ : Measure CarpetPoints ↦ μ univ)
    (E.energyMeasure_smul b g)
  change E.energyMeasure (b • g) univ =
    (ENNReal.ofReal (|b| ^ p) • E.energyMeasure g) univ at henergy
  rw [hcut, abs_of_pos hb, ← ENNReal.ofReal_rpow_of_nonneg hb.le
    (zero_lt_one.trans E.one_lt_p).le, smul_apply, smul_eq_mul, E.energyMeasure_univ,
    E.energyMeasure_univ] at henergy
  have hc := congrArg (fun μ : Measure CarpetPoints ↦ μ univ)
    (E.energyMeasure_shiftedTruncation_eq_restrict u hu b hb)
  change E.energyMeasure cut univ =
    ((E.energyMeasure ⟨continuousLp p u, hu⟩).restrict (u ⁻¹' Ioo b (b + b))) univ at hc
  rw [Measure.restrict_apply_univ, ← two_mul, E.energyMeasure_univ, henergy] at hc
  exact hc

private theorem exists_dyadic_budget_index
    (x y z : ℕ → ℝ≥0∞) {J R e : ℝ≥0∞}
    (hJ : J ≠ 0) (hJt : J ≠ ∞) (hR : 1 ≤ R) (hRt : R ≠ ∞) (het : e ≠ ∞)
    (hX : J ≤ R * (∑' i, x i)) (hX' : (∑' i, x i) ≤ ∑' i, y i)
    (hy : (∑' i, y i) ≤ 2 * J) (hz : (∑' i, z i) ≤ e) :
    ∃ i, x i ≠ 0 ∧ y i ≤ (8 * R) * x i ∧ J * z i ≤ (4 * R) * e * x i := by
  let X := ∑' i, x i
  have hX0 : X ≠ 0 := by
    intro h
    change J ≤ R * X at hX
    rw [h, mul_zero] at hX
    exact hJ (nonpos_iff_eq_zero.mp hX)
  have hXt : X ≠ ∞ :=
    ((hX'.trans hy).trans_lt (ENNReal.mul_lt_top (by norm_num) hJt.lt_top)).ne
  have hC0 : 2 * R ≠ 0 := mul_ne_zero (by norm_num) (zero_lt_one.trans_le hR).ne'
  have hCt : 2 * R ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hRt
  have hy' : (∑' i, y i) ≤ (2 * R) * X := by
    rw [mul_assoc]
    exact hy.trans (mul_le_mul' le_rfl hX)
  obtain ⟨i, hi, hiy, hiz⟩ := exists_simultaneous_bounds x y z hX0 hXt hC0 hCt het rfl hy' hz
  refine ⟨i, hi, ?_, ?_⟩
  · simpa only [← mul_assoc, show (4 : ℝ≥0∞) * 2 = 8 by norm_num] using hiy
  · calc
      J * z i ≤ (R * X) * z i := mul_le_mul' hX le_rfl
      _ = R * (X * z i) := mul_assoc _ _ _
      _ ≤ R * (4 * e * x i) := mul_le_mul' le_rfl hiz
      _ = (4 * R) * e * x i := by ac_rfl

/-- Lemma 3.4. The constants depend only on p. The energy ratio estimate is
multiplied by the positive Lp moment and plateau mass. -/
theorem exists_dyadic_truncation (hp : 1 < p) :
    ∃ C₁ C₂ : ℝ≥0, 1 < C₁ ∧ 1 < C₂ ∧
      ∀ (E : SelfSimilarPEnergy p) (u : C(CarpetPoints, ℝ))
        (hu : continuousLp p u ∈ E.domain), u ≠ 0 → (∀ x, 0 ≤ u x) →
        ∃ (g : C(CarpetPoints, ℝ)) (hg : continuousLp p g ∈ E.domain),
          (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ {x | 0 < g x} ⊆ {x | 0 < u x} ∧
          0 < carpetMeasure {x | g x = 1} ∧
          0 < carpetMeasure {x | 0 < g x} ∧
          carpetMeasure {x | 0 < g x} ≤ (C₁ : ℝ≥0∞) * carpetMeasure {x | g x = 1} ∧
          ENNReal.ofReal (‖continuousLp p u‖ ^ p) *
              (E.energy ⟨continuousLp p g, hg⟩ : ℝ≥0∞) ≤
            (C₂ : ℝ≥0∞) * (E.energy ⟨continuousLp p u, hu⟩ : ℝ≥0∞) *
              carpetMeasure {x | g x = 1} := by
  let D : ℝ≥0∞ := (2 : ℝ≥0∞) ^ p
  let R := D * D
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hD₁ : 1 ≤ D := (ENNReal.one_lt_rpow (by norm_num) hp₀).le
  have hDt : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp₀.le (by norm_num)
  have hR₁ : 1 ≤ R := by simpa only [one_mul] using mul_le_mul' hD₁ hD₁
  have hRt : R ≠ ∞ := ENNReal.mul_ne_top hDt hDt
  have hC₁t : 8 * R ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hRt
  have hC₂t : 4 * R ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hRt
  have hC₁' : 1 < (8 * R).toNNReal := by
    apply ENNReal.coe_lt_coe.mp
    rw [ENNReal.coe_toNNReal hC₁t, ENNReal.coe_one]
    exact (by norm_num : (1 : ℝ≥0∞) < 8).trans_le (by
      simpa only [mul_one] using mul_le_mul' (le_refl 8) hR₁)
  have hC₂' : 1 < (4 * R).toNNReal := by
    apply ENNReal.coe_lt_coe.mp
    rw [ENNReal.coe_toNNReal hC₂t, ENNReal.coe_one]
    exact (by norm_num : (1 : ℝ≥0∞) < 4).trans_le (by
      simpa only [mul_one] using mul_le_mul' (le_refl 4) hR₁)
  refine ⟨(8 * R).toNNReal, (4 * R).toNNReal, hC₁', hC₂', ?_⟩
  intro E u hu hu₀ hu_nonneg
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let J := ENNReal.ofReal (‖continuousLp p u‖ ^ p)
  let M := ENNReal.ofReal (‖u‖ + 1)
  let t := dyadicLevel M
  have hM₀ : M ≠ 0 := ENNReal.ofReal_pos.mpr (by positivity) |>.ne'
  have ht₀ (n : ℕ) : t n ≠ 0 := dyadicLevel_ne_zero hM₀ n
  have htt (n : ℕ) : t n ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (by norm_num))
  have hJ : J ≠ 0 := by
    have hne : continuousLp p u ≠ 0 := by
      intro h
      apply hu₀
      apply continuousLp_injective p
      rw [h]
      apply Lp.ext
      exact (Lp.coeFn_zero ℝ (ENNReal.ofReal p) carpetMeasure).trans
        (continuousLp_ae_eq p (0 : C(CarpetPoints, ℝ))).symm
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hne) p)).ne'
  have hmoment := continuousLp_rpow_norm_eq_lintegral hp.le u hu_nonneg
  have hsup (x : CarpetPoints) : ENNReal.ofReal (u x) ≤ M :=
    ENNReal.ofReal_le_ofReal ((ContinuousMap.apply_le_norm u x).trans
      (le_add_of_nonneg_right zero_le_one))
  have hmass := dyadicLayerMass_bounds carpetMeasure (fun x ↦ ENNReal.ofReal (u x))
    (u.continuous.measurable.ennreal_ofReal) hp.le hM₀ ENNReal.ofReal_ne_top
    (Filter.Eventually.of_forall hsup)
  let A (n : ℕ) : Set CarpetPoints := {x | t n ≤ ENNReal.ofReal (u x)}
  let x (n : ℕ) := (t (n + 1)) ^ p * carpetMeasure (A n)
  let y (n : ℕ) := (t (n + 1)) ^ p * carpetMeasure (A (n + 1))
  have hstep (n : ℕ) : 2 * t (n + 1) = t n := dyadicLevel_succ_mul_two M n
  have hscale (n : ℕ) : t n ^ p = D * t (n + 1) ^ p := by
    rw [← hstep n, ENNReal.mul_rpow_of_nonneg _ _ hp₀.le]
  have htsucc (n : ℕ) : t (n + 1) ≤ t n := by
    rw [← hstep n]
    simpa only [one_mul] using mul_le_mul' (by norm_num : (1 : ℝ≥0∞) ≤ 2) (le_refl (t (n + 1)))
  change (∫⁻ a, ENNReal.ofReal (u a) ^ p ∂carpetMeasure) ≤
      D * (∑' n, t n ^ p * carpetMeasure (A n)) ∧
    (∑' n, t n ^ p * carpetMeasure (A n)) ≤
      2 * (∫⁻ a, ENNReal.ofReal (u a) ^ p ∂carpetMeasure) at hmass
  rw [← hmoment] at hmass
  have hX : J ≤ R * (∑' n, x n) := by
    have hs (n : ℕ) : t n ^ p * carpetMeasure (A n) = D * x n := by
      rw [hscale, mul_assoc]
    simpa only [hs, ENNReal.tsum_mul_left, ← mul_assoc] using hmass.1
  have hX' : (∑' n, x n) ≤ ∑' n, y n :=
    tsum_le_tsum fun n ↦ mul_le_mul' le_rfl (measure_mono fun a ha ↦ (htsucc n).trans ha)
  have hy : (∑' n, y n) ≤ 2 * J :=
    (tsum_comp_le_tsum_of_injective Nat.succ_injective _).trans hmass.2
  let b (n : ℕ) := (t (n + 1)).toReal
  have hb (n : ℕ) : 0 < b n := ENNReal.toReal_pos (ht₀ (n + 1)) (htt (n + 1))
  have ht_b (n : ℕ) : ENNReal.ofReal (b n) = t (n + 1) :=
    ENNReal.ofReal_toReal (htt (n + 1))
  let g (n : ℕ) := normalizedStrip u (b n)
  have hg (n : ℕ) : continuousLp p (g n) ∈ E.domain := by
    rw [E.continuousLp_normalizedStrip u hu (hb n)]
    exact Subtype.property _
  let z (n : ℕ) := (t (n + 1)) ^ p * (E.energy ⟨continuousLp p (g n), hg n⟩ : ℝ≥0∞)
  let B (n : ℕ) := u ⁻¹' Ioo (b n) (2 * b n)
  have hB (n : ℕ) : MeasurableSet (B n) := measurableSet_Ioo.preimage u.continuous.measurable
  have hB_disjoint : Pairwise (Disjoint on B) := by
    have hb_mono : Antitone b := antitone_nat_of_succ_le fun n ↦
      ENNReal.toReal_mono (htt _) (htsucc _)
    have hb_succ (n : ℕ) : 2 * b (n + 1) = b n := by
      have he := congrArg ENNReal.toReal (dyadicLevel_succ_mul_two M (n + 1))
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using he
    suffices h : ∀ i j : ℕ, i < j → Disjoint (B i) (B j) by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hij | hij
      · exact h i j hij
      · exact (h j i hij).symm
    intro i j hij
    apply Set.disjoint_left.mpr
    intro a hai haj
    have ha₁ : b i < u a := hai.1
    have ha₂ : u a < 2 * b j := haj.2
    exact ha₁.not_ge (ha₂.le.trans (by
      rw [← hb_succ i]
      exact mul_le_mul_of_nonneg_left (hb_mono hij) (by norm_num)))
  let f : E.domain := ⟨continuousLp p u, hu⟩
  have hz_eq (n : ℕ) : z n = E.energyMeasure f (B n) := by
    dsimp only [z]
    rw [← ht_b n]
    exact E.energy_normalizedStrip u hu (hb n) (hg n)
  have hz : (∑' n, z n) ≤ (E.energy f : ℝ≥0∞) := by
    simp_rw [hz_eq]
    rw [← measure_iUnion hB_disjoint hB, ← E.energyMeasure_univ]
    exact measure_mono (subset_univ _)
  obtain ⟨n, hn, hny, hnz⟩ := exists_dyadic_budget_index x y z hJ ENNReal.ofReal_ne_top
    hR₁ hRt ENNReal.coe_ne_top hX hX' hy hz
  have hplateau : {a | g n a = 1} = A n := by
    ext a
    change g n a = 1 ↔ t n ≤ ENNReal.ofReal (u a)
    have htwo : ENNReal.ofReal (2 * b n) = 2 * ENNReal.ofReal (b n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    rw [normalizedStrip_eq_one_iff u (hb n), ← hstep n, ← ht_b n, ← htwo]
    exact (ENNReal.ofReal_le_ofReal_iff (hu_nonneg a)).symm
  have hsupport : {a | 0 < g n a} ⊆ A (n + 1) := by
    intro a ha
    change t (n + 1) ≤ ENNReal.ofReal (u a)
    rw [← ht_b n]
    exact ENNReal.ofReal_le_ofReal ((normalizedStrip_pos_iff u (hb n) a).mp ha).le
  have hA₀ : 0 < carpetMeasure (A n) := by
    by_contra! h
    exact hn (by simp only [x, nonpos_iff_eq_zero.mp h, mul_zero])
  have hA_pos : A n ⊆ {a | 0 < g n a} := fun a ha ↦ by
    change 0 < g n a
    rw [← hplateau] at ha
    rw [show g n a = 1 from ha]
    norm_num
  have ht_pow₀ : t (n + 1) ^ p ≠ 0 :=
    (ENNReal.rpow_pos_of_nonneg (ht₀ (n + 1)).pos hp₀.le).ne'
  have ht_powt : t (n + 1) ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp₀.le (htt (n + 1))
  refine ⟨g n, hg n, normalizedStrip_bounds u (hb n), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a ha ↦ (hb n).trans ((normalizedStrip_pos_iff u (hb n) a).mp ha)
  · simpa only [hplateau] using hA₀
  · exact hA₀.trans_le (measure_mono hA_pos)
  · rw [hplateau, ENNReal.coe_toNNReal hC₁t]
    apply (measure_mono hsupport).trans
    apply (ENNReal.mul_le_mul_iff_right ht_pow₀ ht_powt).mp
    convert hny using 1
    dsimp only [x]
    ac_rfl
  · rw [hplateau, ENNReal.coe_toNNReal hC₂t]
    apply (ENNReal.mul_le_mul_iff_right ht_pow₀ ht_powt).mp
    convert hnz using 1 <;> dsimp only [z, x, f, J] <;> ac_rfl

end CarpetEnergy.SelfSimilarPEnergy
