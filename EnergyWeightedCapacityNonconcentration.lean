import EnergyWeightedCutoffComposition
import CarpetWordIntegral

/-!
# Nonconcentration from small weighted Sobolev cutoffs

If the volume pushforward were concentrated on the exceptional set,
small cutoffs on its compact subsets would approximate a nonconstant
coordinate in Lp while their energy went to zero.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy

/-- A smooth cutoff whose weighted Sobolev moments are at most ε. -/
def IsSmallWeightedCutoff (p : ℝ) (κ : Measure (Fin 2 → ℝ))
    (K : Set (Fin 2 → ℝ)) (ε : ℝ) (f : (Fin 2 → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ HasCompactSupport f ∧
    (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ K, f x = 1) ∧
    (∫ x, |f x| ^ p ∂κ) ≤ ε ∧
    ∀ i : Fin 2, (∫ x, |fderiv ℝ f x (Pi.single i 1)| ^ p ∂κ) ≤ ε

/-- The smooth weighted cutoff property on compact subsets used in
Proposition 5.11. -/
def HasSmallWeightedCutoffsOnCompacts (p : ℝ) (κ : Measure (Fin 2 → ℝ))
    (B : Set (Fin 2 → ℝ)) : Prop :=
  ∀ K ⊆ B, IsCompact K → ∀ ε > (0 : ℝ), ∃ f, IsSmallWeightedCutoff p κ K ε f

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

set_option maxHeartbeats 3600000 in
/-- Small weighted cutoffs cannot cover almost all of the volume
pushforward of a tuple with a positive-energy coordinate. -/
theorem false_of_small_weighted_cutoff_approximation
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (u : Fin 2 → E.continuousCore) (j : Fin 2)
    (hj : 0 < E.rootSeminorm (E.continuousCoreToDomain (u j)))
    (hb : ∀ ε > (0 : ℝ), ∃ K : Set (Fin 2 → ℝ), IsCompact K ∧
      (carpetMeasure.map (E.continuousCoreTuple u)).real Kᶜ ≤ ε ∧
      ∃ f, IsSmallWeightedCutoff p ((E.pairEnergyMeasure u).map (E.continuousCoreTuple u)) K ε f) :
    False := by
  let H := E.continuousCoreTuple u
  let ν := carpetMeasure.map H
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε₁ (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hεL : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose K hK hKtail f hf hfs hf01 hfK hfb hdfb using fun n : ℕ ↦ hb (ε n) (hε n)
  let M := ‖(u j).val‖
  have hM : 0 ≤ M := norm_nonneg _
  have hm (x : CarpetPoints) : |(u j).val x| ≤ M := by
    rw [← Real.norm_eq_abs]
    exact (u j).val.norm_coe_le_norm x
  choose v hv hroot using fun n : ℕ ↦ E.exists_core_coordinate_mul_cutoff h hc u j hM hm
    (f n) (hf n) ⟨hfb n, hdfb n⟩
  let g (n : ℕ) := E.continuousCoreToDomain (v n)
  let U := E.continuousCoreToDomain (u j)
  let C := (2 : ℝ) ^ (p - 1) * (1 + M ^ p)
  let R (n : ℕ) := 2 * (C * ε n) ^ p⁻¹
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hp := zero_lt_one.trans E.one_lt_p
  have hRlim : Tendsto R atTop (𝓝 0) := by
    have ht := ((hεL.const_mul C).rpow_const (Or.inr (inv_nonneg.mpr hp.le))).const_mul 2
    simpa only [R, mul_zero, Real.zero_rpow (inv_ne_zero hp.ne')] using ht
  have hgNorm (n : ℕ) : ‖(g n : CarpetLp p)‖ ≤ M := by
    apply norm_carpetLp_le_of_ae_bound _ hM
    filter_upwards [continuousLp_ae_eq p (v n).val] with x hx
    change (g n : CarpetLp p) x = (v n).val x at hx
    rw [hx, Real.norm_eq_abs, hv n x, abs_mul, abs_of_nonneg (hf01 n _).1]
    exact (mul_le_mul_of_nonneg_left (hf01 n _).2 (abs_nonneg _)).trans
      (by rw [mul_one]; exact hm x)
  have hR₁ (n : ℕ) : R n ≤ 2 * C ^ p⁻¹ := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.rpow_le_rpow (mul_nonneg hC (hε n).le)
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hε₁ n) hC)
      (inv_nonneg.mpr hp.le)
  have hgraph (n : ℕ) : E.graphSeminorm (g n) ≤ ((2 * C ^ p⁻¹) ^ p + M ^ p) ^ p⁻¹ :=
    E.graphSeminorm_le_of_le (g n) (hgNorm n) ((hroot n).trans (hR₁ n))
  have herror (n : ℕ) : ‖(g n : CarpetLp p) - (U : CarpetLp p)‖ ^ p ≤ M ^ p * ε n := by
    let A := H ⁻¹' (K n)ᶜ
    have hA : MeasurableSet A := (hK n).isClosed.measurableSet.compl.preimage H.continuous.measurable
    let F : CarpetLp p := (g n : CarpetLp p) - (U : CarpetLp p)
    have hI : Integrable (fun x ↦ |F x| ^ p) carpetMeasure := by
      simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using
        (Lp.memLp F).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    have hle : ∀ᵐ x ∂carpetMeasure, |F x| ^ p ≤ A.indicator (fun _ ↦ M ^ p) x := by
      filter_upwards [Lp.coeFn_sub (g n : CarpetLp p) (U : CarpetLp p),
        continuousLp_ae_eq p (v n).val, continuousLp_ae_eq p (u j).val] with x h₁ h₂ h₃
      change F x = (g n : CarpetLp p) x - (U : CarpetLp p) x at h₁
      change (g n : CarpetLp p) x = (v n).val x at h₂
      change (U : CarpetLp p) x = (u j).val x at h₃
      rw [h₁, h₂, h₃, hv n x]
      by_cases hx : H x ∈ K n
      · rw [hfK n _ hx, mul_one, sub_self, abs_zero, Real.zero_rpow hp.ne',
          indicator_of_notMem (show x ∉ A from fun h ↦ h hx)]
      · rw [indicator_of_mem (show x ∈ A from hx)]
        apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
        rw [← mul_sub_one, abs_mul, abs_of_nonpos (sub_nonpos.mpr (hf01 n _).2)]
        calc
          _ ≤ |(u j).val x| * 1 := mul_le_mul_of_nonneg_left (by linarith only [(hf01 n (H x)).1])
            (abs_nonneg _)
          _ ≤ M := (mul_one _).le.trans (hm x)
    have hh := integral_mono_ae hI ((integrable_const (M ^ p)).indicator hA) hle
    rw [integral_abs_rpow_eq_norm_rpow hp, integral_indicator hA, integral_const,
      Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul] at hh
    have hmass : (carpetMeasure A).toReal = ν.real (K n)ᶜ := by
      rw [Measure.real, show ν (K n)ᶜ = carpetMeasure A from
        Measure.map_apply H.continuous.measurable (hK n).isClosed.measurableSet.compl]
    rw [hmass, mul_comm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hKtail n) (Real.rpow_nonneg hM _))
  have hlim : Tendsto (fun n ↦ (g n : CarpetLp p)) atTop (𝓝 (U : CarpetLp p)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have ht := (hεL.const_mul (M ^ p)).rpow_const (Or.inr (inv_nonneg.mpr hp.le))
    simp only [mul_zero, Real.zero_rpow (inv_ne_zero hp.ne')] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ ↦ norm_nonneg _)
    intro n
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) (herror n) (inv_nonneg.mpr hp.le)
    rwa [Real.rpow_rpow_inv (norm_nonneg _) hp.ne'] at hh
  obtain ⟨w, hw, hwRoot⟩ := E.exists_domain_of_tendsto_of_seminorm_le
    E.rootSeminorm E.rootSeminorm_le_graphSeminorm g (U : CarpetLp p) hgraph
    (fun r hr ↦ (hRlim.eventually_lt_const hr).mono fun n hn ↦ (hroot n).trans hn.le) hlim
  have hw' : w = U := Subtype.ext hw
  rw [hw'] at hwRoot
  exact hj.not_ge hwRoot

/-- The nonconcentration step of Proposition 5.11, under its smooth
weighted cutoff conclusion. -/
theorem map_carpetMeasure_compl_pos_of_small_weighted_cutoffs
    (h : E.HasLinearFirstVariations)
    (hc : E.HasFiniteGeneralizedPContraction (fun f ↦ (E.energy f : ℝ)))
    (u : Fin 2 → E.continuousCore) (j : Fin 2)
    (hj : 0 < E.rootSeminorm (E.continuousCoreToDomain (u j)))
    {B : Set (Fin 2 → ℝ)} (hB : MeasurableSet B)
    (hb : HasSmallWeightedCutoffsOnCompacts p
      ((E.pairEnergyMeasure u).map (E.continuousCoreTuple u)) B) :
    0 < (carpetMeasure.map (E.continuousCoreTuple u)) Bᶜ := by
  let ν := carpetMeasure.map (E.continuousCoreTuple u)
  let : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (carpetMeasure.map _))
  apply pos_iff_ne_zero.mpr
  intro hnull
  apply E.false_of_small_weighted_cutoff_approximation h hc u j hj
  intro ε hε
  obtain ⟨K, hKsub, hK, hsmall⟩ := hB.exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top _ _) (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨K, hK, ?_, hb K hKsub hK ε hε⟩
  have he : Kᶜ \ Bᶜ = B \ K := by
    ext x
    simp only [Set.mem_sdiff, mem_compl_iff, not_not, and_comm]
  have he' : ν (B \ K) = ν Kᶜ := by rw [← he, measure_sdiff_null hnull]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall.le
  rw [he', ENNReal.toReal_ofReal hε.le] at hh
  exact hh

end SelfSimilarPEnergy

end CarpetEnergy
