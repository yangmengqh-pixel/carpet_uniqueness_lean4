import CarpetDirectionSelection
import EnergyNormalizedPairMeasure
import EnergyDirectionalMeasureEstimates

/-!
# Harmonic blowup with fixed directional energy ratios

A recurring good cell where the directional densities concentrate
supplies a normalized pair. Graph convergence of a subsequence
passes the integrated estimates to every Borel set.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem measure_half_le_inter {μ : Measure CarpetPoints} [IsFiniteMeasure μ]
    {K C : Set CarpetPoints} (hC : MeasurableSet C)
    (hsmall : μ (K ∩ Cᶜ) ≤ μ K / 2) :
    μ K / 2 ≤ μ (K ∩ C) := by
  refine ENNReal.le_of_add_le_add_right
    (ENNReal.div_ne_top (measure_ne_top μ K) (by norm_num : (2 : ℝ≥0∞) ≠ 0)) ?_
  calc
    _ = μ K := ENNReal.add_halves _
    _ = μ (K ∩ C) + μ (K ∩ Cᶜ) := (measure_inter_add_sdiff K hC).symm
    _ ≤ _ := add_le_add le_rfl hsmall

private theorem cell_measure_component_ge {μ ν : Measure CarpetPoints}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : ν ≪ μ)
    {K C : Set CarpetPoints} (hK : MeasurableSet K) (hC : MeasurableSet C)
    {d : ℝ≥0∞} (hbound : ∀ x ∈ C, d ≤ ν.rnDeriv μ x)
    (hsmall : μ (K ∩ Cᶜ) ≤ μ K / 2) :
    (d / 2) * μ K ≤ ν K := by
  have h := (measure_bounds_by_density hac hC hK d ∞ (Eventually.of_forall hbound)
    (Eventually.of_forall fun _ _ ↦ le_top)).1
  calc
    _ = d * (μ K / 2) := by simp only [div_eq_mul_inv]; ac_rfl
    _ ≤ d * μ (K ∩ C) := mul_le_mul' le_rfl (measure_half_le_inter hC hsmall)
    _ ≤ ν (K ∩ C) := h
    _ ≤ ν K := measure_mono inter_subset_left

private theorem normalized_directional_bounds (w : List (Fin 8)) (f g : E.domain)
    (a b : ℚ) (A C : Set CarpetPoints) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hm : 0 < (E.energyMeasure f + E.energyMeasure g) (range (wordMap w)))
    (θ ε : ℝ≥0∞)
    (hclose : ∀ x ∈ C,
      (E.energyMeasure (a • f + b • g)).rnDeriv (E.energyMeasure f + E.energyMeasure g) x ≤ θ + ε ∧
      θ ≤ (E.energyMeasure (a • f + b • g)).rnDeriv (E.energyMeasure f + E.energyMeasure g) x + ε)
    (hsmall : (E.energyMeasure f + E.energyMeasure g) (range (wordMap w) ∩ Cᶜ) ≤
      ε * (E.energyMeasure f + E.energyMeasure g) (range (wordMap w))) :
    let v := E.normalizedPairWordPullback w f g
    let m := (E.energyMeasure v.1 + E.energyMeasure v.2) A
    let d := E.energyMeasure (a • v.1 + b • v.2) A
    d ≤ θ * m + (ε + ENNReal.ofReal ((‖a‖ + ‖b‖) ^ p) * ε) ∧
      θ * m ≤ d + (ε + θ * ε) := by
  let μ := E.energyMeasure f + E.energyMeasure g
  let ν := E.energyMeasure (a • f + b • g)
  let K := range (wordMap w)
  let m := μ K
  let T := wordMap w '' A
  let U := ENNReal.ofReal ((‖a‖ + ‖b‖) ^ p)
  let : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (E.energyMeasure f + E.energyMeasure g))
  have hT : MeasurableSet T := (measurableEmbedding_wordMap w).measurableSet_image.mpr hA
  have hTK : T ⊆ K := image_subset_range _ _
  have hu := E.ae_rnDeriv_pair_le f g a b
  have hh := measure_directional_sandwich (E.energyMeasure_add_rat_smul_absolutelyContinuous f g a b)
    hC hT hTK θ ε U hu hclose hsmall
  have hr : m⁻¹ * m = 1 := ENNReal.inv_mul_cancel hm.ne' (measure_ne_top _ _)
  have hs₁ := mul_le_mul' (a := m⁻¹) (b := m⁻¹) le_rfl hh.1
  have hs₂ := mul_le_mul' (a := m⁻¹) (b := m⁻¹) le_rfl hh.2
  dsimp only
  rw [E.energyMeasure_normalizedPairWordPullback_image w f g a b A hm,
    E.normalizedPairMeasure_image w f g A hm]
  constructor
  · calc
      m⁻¹ * ν T ≤ m⁻¹ * (θ * μ T + (ε + U * ε) * m) := hs₁
      _ = θ * (m⁻¹ * μ T) + (ε + U * ε) * (m⁻¹ * m) := by rw [mul_add]; ac_rfl
      _ = _ := by rw [hr, mul_one]
  · calc
      θ * (m⁻¹ * μ T) = m⁻¹ * (θ * μ T) := by ac_rfl
      _ ≤ m⁻¹ * (ν T + (ε + θ * ε) * m) := hs₂
      _ = m⁻¹ * ν T + (ε + θ * ε) * (m⁻¹ * m) := by rw [mul_add]; ac_rfl
      _ = _ := by rw [hr, mul_one]

/-- Theorem 5.5 in terms of rational combinations and proportionality of
their energy measures. The remaining hypothesis is the same harmonic
compactness input as in the proof of the zero-one law. -/
theorem exists_harmonic_fixed_direction_measures
    (hcompact : E.HasInteriorHarmonicCompactness) (f g : E.domain)
    (hf : E.IsInteriorHarmonic f) (hg : E.IsInteriorHarmonic g)
    (A : Set CarpetPoints) (hA : MeasurableSet A)
    (hpos : 0 < (E.energyMeasure f + E.energyMeasure g) A)
    (d : ℝ) (hd : 0 < d)
    (hbound : ∀ x ∈ A, ∀ a b : ℚ, ENNReal.ofReal ((d * (‖a‖ + ‖b‖)) ^ p) ≤
      (E.energyMeasure (a • f + b • g)).rnDeriv (E.energyMeasure f + E.energyMeasure g) x) :
    ∃ (v₁ v₂ : E.domain) (u₁ u₂ : C(CarpetPoints, ℝ)) (Θ : ℚ × ℚ → ℝ≥0∞),
      E.IsInteriorHarmonic v₁ ∧ E.IsInteriorHarmonic v₂ ∧
      continuousLp p u₁ = (v₁ : CarpetLp p) ∧ continuousLp p u₂ = (v₂ : CarpetLp p) ∧
      (E.energy v₁ : ℝ) + (E.energy v₂ : ℝ) = 1 ∧
      (∀ a b : ℚ, ENNReal.ofReal ((d * (‖a‖ + ‖b‖)) ^ p) ≤ Θ (a, b) ∧
        Θ (a, b) ≤ ENNReal.ofReal ((‖a‖ + ‖b‖) ^ p)) ∧
      ∀ a b : ℚ, E.energyMeasure (a • v₁ + b • v₂) = Θ (a, b) • (E.energyMeasure v₁ + E.energyMeasure v₂) := by
  classical
  let μ := E.energyMeasure f + E.energyMeasure g
  let : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (E.energyMeasure f + E.energyMeasure g))
  let D (x : CarpetPoints) (q : ℚ × ℚ) := (E.energyMeasure (q.1 • f + q.2 • g)).rnDeriv μ x
  let L (q : ℚ × ℚ) := ENNReal.ofReal ((d * (‖q.1‖ + ‖q.2‖)) ^ p)
  let U (q : ℚ × ℚ) := ENNReal.ofReal ((‖q.1‖ + ‖q.2‖) ^ p)
  let good := {x | ∀ q, D x q ≤ U q}
  have hgood : ∀ᵐ x ∂μ, x ∈ good :=
    ae_all_iff.mpr fun q ↦ E.ae_rnDeriv_pair_le f g q.1 q.2
  have hmeas : MeasurableSet good := by
    rw [show good = ⋂ q, {x | D x q ≤ U q} from by ext x; simp [good]]
    exact MeasurableSet.iInter fun q ↦ measurableSet_le (Measure.measurable_rnDeriv _ _) measurable_const
  have hA₀ : μ (A ∩ good) = μ A := by
    apply measure_congr
    filter_upwards [hgood] with x hx
    exact ⟨And.left, fun h ↦ ⟨h, hx⟩⟩
  have hnull : μ carpetAllCellBoundaries = 0 := by
    rw [add_apply, E.energyMeasure_carpetAllCellBoundaries_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero,
      E.energyMeasure_carpetAllCellBoundaries_eq_zero E.energyMeasure_carpetOuterBoundary_eq_zero, add_zero]
  have hboundary : μ carpetOuterBoundary = 0 := by
    rw [add_apply, E.energyMeasure_carpetOuterBoundary_eq_zero, E.energyMeasure_carpetOuterBoundary_eq_zero, add_zero]
  obtain ⟨α, hα, Θ, hΘ, hsel⟩ := exists_directional_good_cells μ hnull hboundary
    (A ∩ good) (hA.inter hmeas) (hA₀.symm ▸ hpos) 3 D
    (fun _ ↦ Measure.measurable_rnDeriv _ _) L U (fun _ ↦ ENNReal.ofReal_lt_top)
    (fun x hx q ↦ ⟨hbound x hx.1 q.1 q.2, hx.2 q⟩)
  obtain ⟨q, hq⟩ := exists_surjective_nat (ℚ × ℚ)
  let J (n : ℕ) := (Finset.range (n + 1)).image q
  let ε (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((n : ℝ) + 2))
  have hε (n : ℕ) : 0 < ε n := ENNReal.ofReal_pos.mpr (by positivity)
  have hε₀ : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun n ↦ by positivity)
        (fun n ↦ one_div_le_one_div_of_le (by positivity) (by linarith))
    have h2 := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h1
    change Tendsto ε atTop (𝓝 (ENNReal.ofReal 0)) at h2
    rwa [ENNReal.ofReal_zero] at h2
  have hε₂ (n : ℕ) : ε n ≤ (2 : ℝ≥0∞)⁻¹ := by
    change ENNReal.ofReal (1 / ((n : ℝ) + 2)) ≤ _
    rw [← ENNReal.ofReal_ofNat (2 : ℕ), ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hn
  choose C W hCA hC hn hclose hmass hratio hloc hsmall using fun n ↦ hsel (J n) (ε n) (hε n) n
  let n (k : ℕ) := (W k).1
  let w (k : ℕ) : Fin (n k) → Fin 8 := (W k).2
  let K (k : ℕ) := range (wordMap (List.ofFn (w k)))
  let d₀ := ENNReal.ofReal (d ^ p)
  have hd₀ : 0 < d₀ := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hd _)
  have hh (k : ℕ) : μ (K k ∩ (C k)ᶜ) ≤ μ (K k) / 2 :=
    (hsmall k).trans (by
      change ε k * μ (K k) ≤ _
      rw [div_eq_mul_inv, mul_comm (ε k)]
      exact mul_le_mul' le_rfl (hε₂ k))
  have hcF (k : ℕ) : (d₀ / 2) * μ (K k) ≤ E.energyMeasure f (K k) := by
    have hu : ∀ x ∈ C k, d₀ ≤ (E.energyMeasure f).rnDeriv μ x := by
      intro x hx
      have ht := hbound x (hCA k hx).1 1 0
      simpa only [norm_one, norm_zero, add_zero, mul_one, one_smul, zero_smul] using ht
    exact cell_measure_component_ge ((Measure.absolutelyContinuous_of_le
      (le_add_of_nonneg_right bot_le)) : E.energyMeasure f ≪ μ)
      (measurableEmbedding_wordMap _).measurableSet_range (hC k) hu (hh k)
  have hcG (k : ℕ) : (d₀ / 2) * μ (K k) ≤ E.energyMeasure g (K k) := by
    have hu : ∀ x ∈ C k, d₀ ≤ (E.energyMeasure g).rnDeriv μ x := by
      intro x hx
      have ht := hbound x (hCA k hx).1 0 1
      simpa only [norm_one, norm_zero, zero_add, mul_one, one_smul, zero_smul] using ht
    exact cell_measure_component_ge ((Measure.absolutelyContinuous_of_le
      (le_add_of_nonneg_left bot_le)) : E.energyMeasure g ≪ μ)
      (measurableEmbedding_wordMap _).measurableSet_range (hC k) hu (hh k)
  let δ := d₀ / 2
  have hδ : 0 < δ := ENNReal.div_pos hd₀.ne' (by norm_num)
  have hr (v : E.domain) (hv : E.energyMeasure v ≤ μ) (h : ∀ k, δ * μ (K k) ≤ E.energyMeasure v (K k)) :
      (∀ k, 0 < E.energyMeasure v (K k)) ∧
      (∃ a : ℝ≥0∞, 0 < a ∧ ∀ k, a * E.energyMeasure v (wordCellUnion (cellNeighborhood (w k) 3)) ≤
        E.energyMeasure v (K k)) := by
    refine ⟨fun k ↦ (ENNReal.mul_pos hδ.ne' (hmass k).ne').trans_le (h k),
      δ * α, ENNReal.mul_pos hδ.ne' hα.ne', fun k ↦ ?_⟩
    rw [mul_assoc]
    exact (mul_le_mul' le_rfl ((mul_le_mul' le_rfl (hv _)).trans (hratio k))).trans (h k)
  obtain ⟨hposF, hrF⟩ := hr f (le_add_of_nonneg_right bot_le) hcF
  obtain ⟨hposG, hrG⟩ := hr g (le_add_of_nonneg_left bot_le) hcG
  obtain ⟨j, v₁, v₂, u₁, u₂, hj, hu₁, hu₂, hv₁, hv₂, hE, ht₁, ht₂⟩ :=
    E.exists_normalizedPairWordPullback_subseq hcompact f g hf hg n w hn hposF hposG hrF hrG hloc
  refine ⟨v₁, v₂, u₁, u₂, Θ, hv₁, hv₂, hu₁, hu₂, hE, fun a b ↦ hΘ (a, b), ?_⟩
  intro a b
  ext S hS
  simp only [smul_apply, smul_eq_mul]
  let Q (k : ℕ) := E.normalizedPairWordPullback (List.ofFn (w (j k))) f g
  have hm := ((E.continuous_graphEnergyMeasure S hS).tendsto _).comp ht₁ |>.add
    (((E.continuous_graphEnergyMeasure S hS).tendsto _).comp ht₂)
  have ht := (((ht₁.const_smul (a : ℝ)).add (ht₂.const_smul (b : ℝ))))
  have hν := ((E.continuous_graphEnergyMeasure S hS).tendsto _).comp ht
  let P (k : ℕ) := (E.energyMeasure (Q k).1 + E.energyMeasure (Q k).2) S
  let R (k : ℕ) := E.energyMeasure (a • (Q k).1 + b • (Q k).2) S
  have hm' : Tendsto P atTop (𝓝 ((E.energyMeasure v₁ + E.energyMeasure v₂) S)) := by
    simp only [P, add_apply]
    exact hm
  have hν' : Tendsto R atTop (𝓝 (E.energyMeasure (a • v₁ + b • v₂) S)) := by
    change Tendsto (fun k ↦ E.energyMeasure ((a : ℝ) • (Q k).1 + (b : ℝ) • (Q k).2) S)
      atTop (𝓝 (E.energyMeasure ((a : ℝ) • v₁ + (b : ℝ) • v₂) S)) at hν
    simpa only [R, Rat.cast_smul_eq_qsmul] using hν
  have htθ := ((ENNReal.continuous_const_mul (show Θ (a, b) ≠ ∞ from
    ((hΘ (a, b)).2.trans_lt ENNReal.ofReal_lt_top).ne)).tendsto _).comp hm'
  have hεj := hε₀.comp hj.tendsto_atTop
  have hz (c : ℝ≥0∞) (hc : c ≠ ∞) :
      Tendsto (fun k ↦ ε (j k) + c * ε (j k)) atTop (𝓝 0) := by
    have hh := hεj.add ((ENNReal.continuous_const_mul hc).tendsto 0 |>.comp hεj)
    simpa only [mul_zero, add_zero, Function.comp_apply] using hh
  obtain ⟨i, hi⟩ := hq (a, b)
  have he : ∀ᶠ k in atTop, R k ≤ Θ (a, b) * P k + (ε (j k) + U (a, b) * ε (j k)) ∧
      Θ (a, b) * P k ≤ R k + (ε (j k) + Θ (a, b) * ε (j k)) := by
    filter_upwards [hj.tendsto_atTop.eventually_ge_atTop i] with k hk
    have hk' : (a, b) ∈ J (j k) := Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hi⟩
    exact E.normalized_directional_bounds _ f g a b S (C (j k)) hS (hC (j k)) (hmass (j k))
      (Θ (a, b)) (ε (j k)) (fun x hx ↦ ⟨(hclose (j k) x hx _ hk').1.le, (hclose (j k) x hx _ hk').2.le⟩)
      (hsmall (j k))
  apply le_antisymm
  · have hh := htθ.add (hz (U (a, b)) ENNReal.ofReal_ne_top)
    exact le_of_tendsto_of_tendsto hν' (by simpa only [add_zero, Function.comp_apply] using hh) (he.mono fun _ h ↦ h.1)
  · have hh := hν'.add (hz (Θ (a, b)) ((hΘ (a, b)).2.trans_lt ENNReal.ofReal_lt_top).ne)
    exact le_of_tendsto_of_tendsto htθ (by simpa only [add_zero, Function.comp_apply] using hh) (he.mono fun _ h ↦ h.2)

end CarpetEnergy.SelfSimilarPEnergy
