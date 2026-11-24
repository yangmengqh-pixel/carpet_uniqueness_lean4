import EnergyHarmonicMajorants
import EnergyNeighborhoodZeroPoincare
import EnergyNormalizedHarmonic

/-!
# A local sup bound from the neighborhood Harnack inequality

For either sign of a centered harmonic profile, a nonnegative
replacement controls that sign. Poincaré and local energy minimization
bound the average of each replacement, to which Harnack applies.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

theorem wordCellUnion_mono {n : ℕ} {S T : Finset (Fin n → Fin 8)} (h : S ⊆ T) :
    wordCellUnion S ⊆ wordCellUnion T := by
  intro x hx
  obtain ⟨w, hw⟩ := mem_iUnion.mp hx
  obtain ⟨hS, hx⟩ := mem_iUnion.mp hw
  exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨h hS, hx⟩⟩

theorem carpetMeasure_wordCellUnion_compl_ne_zero {n : ℕ} {S : Finset (Fin n → Fin 8)}
    (hS : S ≠ Finset.univ) : carpetMeasure (wordCellUnion Sᶜ) ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ : ∃ u : Fin n → Fin 8, u ∉ S := by
    by_contra! h
    exact hS (Finset.eq_univ_iff_forall.mpr h)
  have hsub : range (wordMap (List.ofFn u)) ⊆ wordCellUnion Sᶜ :=
    fun _ hx ↦ mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨Finset.mem_compl.mpr hu, hx⟩⟩
  have h := measure_mono (μ := carpetMeasure) hsub
  rw [carpetMeasure_range_wordMap, List.length_ofFn] at h
  refine ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr ?_) h)
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))

theorem cellNeighborhood_ne_univ_of_disjoint_outerBoundary {n k : ℕ} (w : Fin n → Fin 8)
    (hw : Disjoint (wordCellUnion (cellNeighborhood w k)) carpetOuterBoundary) :
    cellNeighborhood w k ≠ Finset.univ := by
  intro h
  rw [h, wordCellUnion_univ] at hw
  have hc : cornerPoint 0 0 ∈ carpetOuterBoundary :=
    (mem_carpetOuterBoundary _).mpr ⟨0, 0, by rw [cornerPoint_first]⟩
  exact Set.disjoint_left.mp hw (mem_univ _) hc

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Lemma 4.7 in pairwise almost-everywhere form. -/
def HasNeighborhoodHarnack (H : ℝ) : Prop :=
  ∀ (n : ℕ) (w : Fin n → Fin 8),
    Disjoint (wordCellUnion (cellNeighborhood w 3)) carpetOuterBoundary →
    ∀ f : E.domain,
      E.MinimizesWithExterior (wordCellUnion (cellNeighborhood w 3)ᶜ) f →
      (∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 3)), 0 ≤ (f : CarpetLp p) x) →
      ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 2)),
        ∀ᵐ y ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 2)),
          (f : CarpetLp p) x ≤ H * (f : CarpetLp p) y

private theorem integrable_abs_rpow_lp (hp : 0 < p) (f : CarpetLp p) :
    Integrable (fun x ↦ |f x| ^ p) carpetMeasure := by
  have h := (Lp.memLp f).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using h

private theorem abs_rpow_sum_le {p : ℝ} (hp : 1 ≤ p) (x y : ℝ) :
    |x + y| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|x| ^ p + |y| ^ p) := by
  refine (Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (zero_le_one.trans hp)).trans ?_
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    ⟨|x|, abs_nonneg _⟩ ⟨|y|, abs_nonneg _⟩ hp

private theorem abs_rpow_le_of_ae_mul {A : Set CarpetPoints} (hp : 0 < p) {H : ℝ} (hH : 0 ≤ H)
    (f : CarpetLp p) (x : CarpetPoints) (hx : 0 ≤ f x)
    (h : ∀ᵐ y ∂carpetMeasure.restrict A, f x ≤ H * f y) :
    (carpetMeasure A).toReal * |f x| ^ p ≤ H ^ p * ∫ y in A, |f y| ^ p ∂carpetMeasure := by
  have h' : ∀ᵐ y ∂carpetMeasure.restrict A, |f x| ^ p ≤ H ^ p * |f y| ^ p := by
    filter_upwards [h] with y hy
    rw [abs_of_nonneg hx, ← Real.mul_rpow hH (abs_nonneg _)]
    exact Real.rpow_le_rpow hx (hy.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hH)) hp.le
  have hb := integral_mono_ae (integrable_const (|f x| ^ p))
    ((integrable_abs_rpow_lp hp f).restrict.const_mul (H ^ p)) h'
  rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smul_eq_mul, integral_const_mul] at hb
  exact hb

private theorem local_integral_majorant_le (hp₁ : 1 < p) {A : Set CarpetPoints} (f t u : CarpetLp p)
    (ht : t =ᵐ[carpetMeasure] fun x ↦ max (f x) 0) :
    (∫ x in A, |u x| ^ p ∂carpetMeasure) ≤
      (2 : ℝ) ^ (p - 1) * (‖u - t‖ ^ p + ∫ x in A, |f x| ^ p ∂carpetMeasure) := by
  have hp := zero_lt_one.trans hp₁
  let v := u - t
  let Q := (2 : ℝ) ^ (p - 1)
  have hv := integrable_abs_rpow_lp hp v
  have hf := integrable_abs_rpow_lp hp f
  have h : ∀ᵐ x ∂carpetMeasure.restrict A, |u x| ^ p ≤ Q * (|v x| ^ p + |f x| ^ p) := by
    filter_upwards [(Lp.coeFn_sub u t).filter_mono (ae_mono Measure.restrict_le_self),
      ht.filter_mono (ae_mono Measure.restrict_le_self)] with x hx ht'
    have hx' : v x = u x - t x := hx
    have hsum : v x + t x = u x := by rw [hx', sub_add_cancel]
    have ht'' : |t x| ^ p ≤ |f x| ^ p := by
      rw [ht', abs_of_nonneg (le_max_right _ _)]
      exact Real.rpow_le_rpow (le_max_right _ _) (max_le (le_abs_self _) (abs_nonneg _)) hp.le
    calc
      _ = |v x + t x| ^ p := by rw [hsum]
      _ ≤ Q * (|v x| ^ p + |t x| ^ p) := abs_rpow_sum_le hp₁.le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right ht'' _) (by positivity)
  have hi := integral_mono_ae (integrable_abs_rpow_lp hp u).restrict
    ((hv.restrict.add hf.restrict).const_mul Q) h
  rw [integral_const_mul] at hi
  change (∫ x in A, |u x| ^ p ∂carpetMeasure) ≤
    Q * ∫ x in A, (|v x| ^ p + |f x| ^ p) ∂carpetMeasure at hi
  rw [integral_add hv.restrict hf.restrict] at hi
  refine hi.trans (mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (by positivity))
  rw [← integral_abs_rpow_eq_norm_rpow hp v]
  exact setIntegral_le_integral hv (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)

private theorem cellUnionEnergy_neg {n : ℕ} (S : Finset (Fin n → Fin 8)) (f : E.domain) :
    E.cellUnionEnergy S (-f) = E.cellUnionEnergy S f := by
  rw [← neg_one_smul ℝ f]
  simp only [E.cellUnionEnergy_eq_energyMeasure_real, E.energyMeasure_smul, abs_neg, abs_one,
    Real.one_rpow, ENNReal.ofReal_one, one_smul]

set_option maxHeartbeats 2100000 in
theorem exists_harmonic_neighborhood_abs_rpow_bound [Fact (1 ≤ ENNReal.ofReal p)]
    {H : ℝ} (hH : 1 ≤ H) (hHar : E.HasNeighborhoodHarnack H)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ E.energy f)) :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8),
      Disjoint (wordCellUnion (cellNeighborhood w 3)) carpetOuterBoundary →
      ∀ f : E.domain, E.MinimizesWithExterior (wordCellUnion (cellNeighborhood w 3)ᶜ) f →
        ∀ M ≥ (0 : ℝ),
        (∫ x in wordCellUnion (cellNeighborhood w 3), |(f : CarpetLp p) x| ^ p ∂carpetMeasure) ≤
          ((8 : ℝ)⁻¹) ^ n * M →
        E.cellUnionEnergy (cellNeighborhood w 3) f ≤ E.scalingFactor ^ n * M →
        ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 2)),
          |(f : CarpetLp p) x| ^ p ≤ C * M := by
  have hp := zero_lt_one.trans E.one_lt_p
  let Q := (2 : ℝ) ^ (p - 1)
  obtain ⟨A, hA, hpi⟩ := E.exists_poincare_of_zero_exterior_neighborhood 3
  let C := H ^ p * (Q * (A * (2 : ℝ) ^ p + 1))
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  refine ⟨C, by dsimp only [C, Q]; positivity, fun n w hw f hf M hM hI he ↦ ?_⟩
  let S := cellNeighborhood w 3
  let V := wordCellUnion (cellNeighborhood w 2)
  let r := ((8 : ℝ)⁻¹) ^ n
  have hr : 0 < r := by dsimp [r]; positivity
  have hproper : S ≠ Finset.univ := cellNeighborhood_ne_univ_of_disjoint_outerBoundary w hw
  have hV : V ⊆ wordCellUnion S := wordCellUnion_mono (cellNeighborhood_subset_succ w)
  have hmass : r ≤ (carpetMeasure V).toReal := by
    have hs : range (wordMap (List.ofFn w)) ⊆ V :=
      fun _ hx ↦ mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨self_mem_cellNeighborhood w 2, hx⟩⟩
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (μ := carpetMeasure) hs)
    rw [carpetMeasure_range_wordMap, List.length_ofFn, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat] at h
    exact h
  have hsign (g : E.domain) (hg : E.MinimizesWithExterior (wordCellUnion Sᶜ) g)
      (hgI : (∫ x in wordCellUnion S, |(g : CarpetLp p) x| ^ p ∂carpetMeasure) ≤ r * M)
      (hgE : E.cellUnionEnergy S g ≤ E.scalingFactor ^ n * M) :
      ∀ᵐ x ∂carpetMeasure.restrict V, 0 ≤ (g : CarpetLp p) x →
        |(g : CarpetLp p) x| ^ p ≤ C * M := by
    obtain ⟨t, u, ht, hu, humin, hu₀, hgu, htE, huE⟩ :=
      E.exists_nonneg_harmonic_majorant S (carpetMeasure_wordCellUnion_compl_ne_zero hproper) hG g hg
    have huzero : ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion Sᶜ), ((u - t : E.domain) : CarpetLp p) x = 0 := by
      filter_upwards [hu, (Lp.coeFn_sub (u : CarpetLp p) (t : CarpetLp p)).filter_mono
        (ae_mono Measure.restrict_le_self)] with x h₁ h₂
      have h₂' : ((u - t : E.domain) : CarpetLp p) x = (u : CarpetLp p) x - (t : CarpetLp p) x := h₂
      rw [h₂', h₁, sub_self]
    let P := E.cellUnionEnergy S g
    have hP : 0 ≤ P := E.cellUnionEnergy_nonneg S g
    have hdiff : E.cellUnionEnergy S (u - t) ≤ (2 : ℝ) ^ p * P := by
      have h := E.cellUnionEnergy_sub_rpow_inv_le S u t
      have h₁ := Real.rpow_le_rpow (E.cellUnionEnergy_nonneg S u) (huE.trans htE)
        (inv_nonneg.mpr hp.le)
      have h₂ := Real.rpow_le_rpow (E.cellUnionEnergy_nonneg S t) htE (inv_nonneg.mpr hp.le)
      have hle : E.cellUnionEnergy S (u - t) ^ p⁻¹ ≤ 2 * P ^ p⁻¹ := by
        change E.cellUnionEnergy S u ^ p⁻¹ ≤ P ^ p⁻¹ at h₁
        change E.cellUnionEnergy S t ^ p⁻¹ ≤ P ^ p⁻¹ at h₂
        linarith only [h, h₁, h₂]
      have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (E.cellUnionEnergy_nonneg S (u - t)) _)
        hle hp.le
      rw [Real.rpow_inv_rpow (E.cellUnionEnergy_nonneg S (u - t)) hp.ne',
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hP _),
        Real.rpow_inv_rpow hP hp.ne'] at hpow
      exact hpow
    have hnorm : ‖((u - t : E.domain) : CarpetLp p)‖ ^ p ≤ r * (A * (2 : ℝ) ^ p * M) := by
      have hρ₀ := E.isScalingFactor_scalingFactor.1
      have hK : 0 ≤ A * (8 * E.scalingFactor)⁻¹ ^ n := by positivity
      have hl := (hpi n w hproper (u - t) huzero).trans
        (mul_le_mul_of_nonneg_left (hdiff.trans (mul_le_mul_of_nonneg_left hgE (by positivity))) hK)
      refine hl.trans_eq ?_
      have hρ := E.isScalingFactor_scalingFactor.1.ne'
      rw [mul_inv, mul_pow]
      have hpow : E.scalingFactor⁻¹ ^ n * E.scalingFactor ^ n = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hρ, one_pow]
      dsimp only [r]
      calc
        _ = ((8 : ℝ)⁻¹) ^ n * (A * (2 : ℝ) ^ p * M) *
          (E.scalingFactor⁻¹ ^ n * E.scalingFactor ^ n) := by ring
        _ = _ := by rw [hpow, mul_one]
    have hint : (∫ x in V, |(u : CarpetLp p) x| ^ p ∂carpetMeasure) ≤
        r * (Q * (A * (2 : ℝ) ^ p + 1) * M) := by
      have hm := integral_mono_measure (Measure.restrict_mono hV le_rfl)
        (Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg ((u : CarpetLp p) x)) p)
        (integrable_abs_rpow_lp hp (u : CarpetLp p)).restrict
      refine (hm.trans (local_integral_majorant_le E.one_lt_p (g : CarpetLp p) (t : CarpetLp p)
        (u : CarpetLp p) ht)).trans ?_
      have h := mul_le_mul_of_nonneg_left (add_le_add hnorm hgI)
        (show 0 ≤ Q by dsimp only [Q]; positivity)
      exact h.trans_eq (by ring)
    have har := hHar n w hw u humin (hu₀.filter_mono (ae_mono Measure.restrict_le_self))
    filter_upwards [har, hu₀.filter_mono (ae_mono (Measure.restrict_le_self (s := V))),
      hgu.filter_mono (ae_mono (Measure.restrict_le_self (s := V)))] with x hx hx₀ hxg hg₀
    have hb := (abs_rpow_le_of_ae_mul hp hH₀.le (u : CarpetLp p) x hx₀ hx).trans
      (mul_le_mul_of_nonneg_left hint (Real.rpow_nonneg hH₀.le p))
    have hb' : r * |(u : CarpetLp p) x| ^ p ≤ r * (C * M) := by
      refine (mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (abs_nonneg _) _)).trans
        (hb.trans_eq ?_)
      dsimp only [C]
      ring
    have hux := le_of_mul_le_mul_left hb' hr
    rw [abs_of_nonneg hg₀]
    rw [abs_of_nonneg hx₀] at hux
    exact (Real.rpow_le_rpow hg₀ hxg hp.le).trans hux
  have hneg : (∫ x in wordCellUnion S, |(((-f : E.domain) : CarpetLp p) x)| ^ p ∂carpetMeasure) ≤
      r * M := by
    refine (integral_congr_ae ?_).le.trans hI
    filter_upwards [(Lp.coeFn_neg (f : CarpetLp p)).filter_mono (ae_mono Measure.restrict_le_self)] with x hx
    have hx' : ((-f : E.domain) : CarpetLp p) x = -((f : CarpetLp p) x) := hx
    rw [hx', abs_neg]
  have hfneg := hsign (-f) (MinimizesWithExterior.neg E hf) hneg (by rwa [E.cellUnionEnergy_neg])
  filter_upwards [hsign f hf hI he, hfneg, (Lp.coeFn_neg (f : CarpetLp p)).filter_mono
    (ae_mono (Measure.restrict_le_self (s := V)))] with x hpos hneg hx
  rcases le_total 0 ((f : CarpetLp p) x) with h | h
  · exact hpos h
  · have hx' : ((-f : E.domain) : CarpetLp p) x = -((f : CarpetLp p) x) := hx
    rw [hx', abs_neg] at hneg
    exact hneg (neg_nonneg.mpr h)

set_option maxHeartbeats 1300000 in
/-- Proposition 4.8, conditional on the neighborhood Harnack inequality. -/
theorem exists_harmonic_neighborhood_centered_bound [Fact (1 ≤ ENNReal.ofReal p)]
    {H : ℝ} (hH : 1 ≤ H) (hHar : E.HasNeighborhoodHarnack H)
    (hG : E.HasFiniteGeneralizedPContraction (fun f ↦ E.energy f)) :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (w : Fin n → Fin 8),
      Disjoint (wordCellUnion (cellNeighborhood w 3)) carpetOuterBoundary →
      ∀ f : E.domain, E.MinimizesWithExterior (wordCellUnion (cellNeighborhood w 3)ᶜ) f →
        ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood w 2)),
          |(f : CarpetLp p) x - E.wordMean (List.ofFn w) f| ≤
            C * ((E.scalingFactor ^ n)⁻¹ * E.cellUnionEnergy (cellNeighborhood w 3) f) ^ p⁻¹ := by
  obtain ⟨B, hB, hbound⟩ := E.exists_harmonic_neighborhood_abs_rpow_bound hH hHar hG
  obtain ⟨A, hA, hpi⟩ := E.exists_neighborhood_poincare 3
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let K := max A 1
  have hK : 0 < K := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨(B * K) ^ p⁻¹, Real.rpow_pos_of_pos (mul_pos hB hK) _, fun n w hw f hf ↦ ?_⟩
  let S := cellNeighborhood w 3
  let m := E.wordMean (List.ofFn w) f
  let a : E.domain := ⟨constantLp p (-m), E.constant_mem (-m)⟩
  let g := f + a
  let localEnergy := (E.scalingFactor ^ n)⁻¹ * E.cellUnionEnergy S f
  have hρ : 0 < E.scalingFactor ^ n := pow_pos E.isScalingFactor_scalingFactor.1 _
  have hLocal : 0 ≤ localEnergy := mul_nonneg (inv_nonneg.mpr hρ.le) (E.cellUnionEnergy_nonneg S f)
  have hg := MinimizesWithExterior.add_constant E hf (-m)
  have ha : (a : CarpetLp p) =ᵐ[carpetMeasure] fun _ ↦ -m :=
    Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (-m)
  have hpoint : (g : CarpetLp p) =ᵐ[carpetMeasure] fun x ↦ (f : CarpetLp p) x - m := by
    filter_upwards [Lp.coeFn_add (f : CarpetLp p) (a : CarpetLp p), ha] with x hx ha'
    have hx' : (g : CarpetLp p) x = (f : CarpetLp p) x + (a : CarpetLp p) x := hx
    rw [hx', ha', sub_eq_add_neg]
  have hgI : (∫ x in wordCellUnion S, |(g : CarpetLp p) x| ^ p ∂carpetMeasure) ≤
      ((8 : ℝ)⁻¹) ^ n * (K * localEnergy) := by
    have h := (hpoint.filter_mono (ae_mono (Measure.restrict_le_self (s := wordCellUnion S)))).fun_comp
      (fun t : ℝ ↦ |t| ^ p)
    change (fun x ↦ |(g : CarpetLp p) x| ^ p) =ᵐ[carpetMeasure.restrict (wordCellUnion S)]
      (fun x ↦ |(f : CarpetLp p) x - m| ^ p) at h
    rw [integral_congr_ae h]
    have hsum : localEnergy = ∑ v ∈ S, (E.energy (E.pullbackWord (List.ofFn v) f) : ℝ) := by
      dsimp only [localEnergy, cellUnionEnergy]
      rw [← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul]
    have hle := mul_le_mul_of_nonneg_right (le_max_left A 1) hLocal
    have hle' := mul_le_mul_of_nonneg_left hle (show 0 ≤ ((8 : ℝ)⁻¹) ^ n by positivity)
    apply (hpi n w f).trans
    rw [← hsum]
    exact (show A * ((8 : ℝ)⁻¹) ^ n * localEnergy =
      ((8 : ℝ)⁻¹) ^ n * (A * localEnergy) by ring).le.trans hle'
  have hgE : E.cellUnionEnergy S g ≤ E.scalingFactor ^ n * (K * localEnergy) := by
    have he : E.cellUnionEnergy S g = E.cellUnionEnergy S f := by
      simp only [E.cellUnionEnergy_eq_energyMeasure_real, g, a, E.energyMeasure_add_constant]
    have hfp : E.scalingFactor ^ n * localEnergy = E.cellUnionEnergy S f := by
      dsimp only [localEnergy]
      rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
    rw [he, ← hfp]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hLocal (le_max_right _ _)) hρ.le
  have h := hbound n w hw g hg (K * localEnergy) (mul_nonneg hK.le hLocal) hgI hgE
  filter_upwards [h, hpoint.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hx'
  rw [hx'] at hx
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) hx (inv_nonneg.mpr hp.le)
  rw [Real.rpow_rpow_inv (abs_nonneg _) hp.ne', ← mul_assoc,
    Real.mul_rpow (mul_nonneg hB.le hK.le) hLocal] at hpow
  exact hpow

end SelfSimilarPEnergy

end CarpetEnergy
