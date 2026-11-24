import EnergyFixedDirections
import EnergyPositivePairDirections

/-!
# Extending stationary directional masses to real coefficients

Graph-norm continuity of every Borel energy mass extends the
rational identities and their bounds to real coefficients.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The energy measure of every real combination of a stationary pair
is its total energy times the pair's common probability measure. -/
theorem fixed_real_directions_of_rational (f g : E.domain) (d : ℝ)
    (hE : (E.energy f : ℝ) + (E.energy g : ℝ) = 1)
    (Θ : ℚ × ℚ → ℝ≥0∞)
    (hΘ : ∀ a b : ℚ, ENNReal.ofReal ((d * (‖a‖ + ‖b‖)) ^ p) ≤ Θ (a, b) ∧
      Θ (a, b) ≤ ENNReal.ofReal ((‖a‖ + ‖b‖) ^ p))
    (hM : ∀ a b : ℚ, E.energyMeasure (a • f + b • g) = Θ (a, b) • (E.energyMeasure f + E.energyMeasure g)) :
    ∀ a b : ℝ, ENNReal.ofReal ((d * (|a| + |b|)) ^ p) ≤ (E.energy (a • f + b • g) : ℝ≥0∞) ∧
      (E.energy (a • f + b • g) : ℝ≥0∞) ≤ ENNReal.ofReal ((|a| + |b|) ^ p) ∧
      E.energyMeasure (a • f + b • g) =
        (E.energy (a • f + b • g) : ℝ≥0∞) • (E.energyMeasure f + E.energyMeasure g) := by
  let μ := E.energyMeasure f + E.energyMeasure g
  have hμ : μ univ = 1 := by
    change (E.energyMeasure f + E.energyMeasure g) univ = 1
    rw [add_apply, E.energyMeasure_univ, E.energyMeasure_univ, ← ENNReal.coe_add]
    have h' : E.energy f + E.energy g = 1 := by exact_mod_cast hE
    rw [h', ENNReal.coe_one]
  have hΘE (a b : ℚ) : Θ (a, b) = (E.energy (a • f + b • g) : ℝ≥0∞) := by
    have h := congrArg (fun m : Measure CarpetPoints ↦ m univ) (hM a b)
    change E.energyMeasure (a • f + b • g) univ = (Θ (a, b) • μ) univ at h
    rw [E.energyMeasure_univ, smul_apply, smul_eq_mul, hμ, mul_one] at h
    exact h.symm
  let z (x : ℝ × ℝ) : E.GraphDomain := x.1 • E.toGraph f + x.2 • E.toGraph g
  have hz : Continuous z :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  let T (A : Set CarpetPoints) (x : ℝ × ℝ) :=
    E.energyMeasure (x.1 • f + x.2 • g) A
  have hT (A : Set CarpetPoints) (hA : MeasurableSet A) : Continuous (T A) :=
    (E.continuous_graphEnergyMeasure A hA).comp hz
  let H (x : ℝ × ℝ) := ENNReal.ofReal ((|x.1| + |x.2|) ^ p)
  let L (x : ℝ × ℝ) := ENNReal.ofReal ((d * (|x.1| + |x.2|)) ^ p)
  have hsum : Continuous (fun x : ℝ × ℝ ↦ |x.1| + |x.2|) :=
    continuous_fst.abs.add continuous_snd.abs
  have hp : 0 ≤ p := zero_le_one.trans E.one_lt_p.le
  have hH : Continuous H :=
    ENNReal.continuous_ofReal.comp ((Real.continuous_rpow_const hp).comp hsum)
  have hL : Continuous L :=
    ENNReal.continuous_ofReal.comp ((Real.continuous_rpow_const hp).comp (hsum.const_mul d))
  have hDense : DenseRange (fun q : ℚ × ℚ ↦ ((q.1 : ℝ), (q.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hL' (x : ℝ × ℝ) : L x ≤ T univ x := by
    refine hDense.induction_on (p := fun y ↦ L y ≤ T univ y) x (isClosed_le hL (hT univ MeasurableSet.univ)) ?_
    rintro ⟨a, b⟩
    have h := (hΘ a b).1
    rw [hΘE, ← E.energyMeasure_univ] at h
    change ENNReal.ofReal ((d * (|(a : ℝ)| + |(b : ℝ)|)) ^ p) ≤ E.energyMeasure
      ((a : ℝ) • f + (b : ℝ) • g) univ
    rwa [← Real.norm_eq_abs, ← Real.norm_eq_abs, Rat.norm_cast_real, Rat.norm_cast_real,
      Rat.cast_smul_eq_qsmul, Rat.cast_smul_eq_qsmul]
  have hU' (x : ℝ × ℝ) : T univ x ≤ H x := by
    refine hDense.induction_on (p := fun y ↦ T univ y ≤ H y) x
      (isClosed_le (hT univ MeasurableSet.univ) hH) ?_
    rintro ⟨a, b⟩
    have h := (hΘ a b).2
    rw [hΘE, ← E.energyMeasure_univ] at h
    change E.energyMeasure ((a : ℝ) • f + (b : ℝ) • g) univ ≤
      ENNReal.ofReal ((|(a : ℝ)| + |(b : ℝ)|) ^ p)
    rwa [← Real.norm_eq_abs, ← Real.norm_eq_abs, Rat.norm_cast_real, Rat.norm_cast_real,
      Rat.cast_smul_eq_qsmul, Rat.cast_smul_eq_qsmul]
  intro a b
  refine ⟨?_, ?_, ?_⟩
  · simpa only [L, T, E.energyMeasure_univ] using hL' (a, b)
  · simpa only [H, T, E.energyMeasure_univ] using hU' (a, b)
  ext A hA
  have hM' (x : ℝ × ℝ) : T A x = T univ x * μ A := by
    refine hDense.induction_on (p := fun y ↦ T A y = T univ y * μ A) x (isClosed_eq (hT A hA)
      ((ENNReal.continuous_mul_const (measure_ne_top μ A)).comp (hT univ MeasurableSet.univ))) ?_
    rintro ⟨r, s⟩
    change E.energyMeasure ((r : ℝ) • f + (s : ℝ) • g) A =
      E.energyMeasure ((r : ℝ) • f + (s : ℝ) • g) univ * μ A
    rw [Rat.cast_smul_eq_qsmul, Rat.cast_smul_eq_qsmul, E.energyMeasure_univ,
      ← hΘE, hM, smul_apply, smul_eq_mul]
  simpa only [T, E.energyMeasure_univ, smul_apply, smul_eq_mul] using hM' (a, b)

/-- With harmonic compactness, any failure of the rank-one assertion
produces a continuous harmonic pair with fixed, coercive directional
energy ratios for all real coefficients. -/
theorem exists_fixed_real_directions_of_not_hasPairwiseEnergyDependence
    (hcompact : E.HasInteriorHarmonicCompactness)
    (μ : Measure CarpetPoints) [IsFiniteMeasure μ] (hdom : ∀ f, E.energyMeasure f ≪ μ)
    (h : ¬ E.HasPairwiseEnergyDependence μ) :
    ∃ (f g : E.domain) (u v : C(CarpetPoints, ℝ)) (d : ℝ),
      E.IsInteriorHarmonic f ∧ E.IsInteriorHarmonic g ∧
      continuousLp p u = (f : CarpetLp p) ∧ continuousLp p v = (g : CarpetLp p) ∧
      (E.energy f : ℝ) + (E.energy g : ℝ) = 1 ∧ 0 < d ∧
      ∀ a b : ℝ, ENNReal.ofReal ((d * (|a| + |b|)) ^ p) ≤ (E.energy (a • f + b • g) : ℝ≥0∞) ∧
        (E.energy (a • f + b • g) : ℝ≥0∞) ≤ ENNReal.ofReal ((|a| + |b|) ^ p) ∧
        E.energyMeasure (a • f + b • g) =
          (E.energy (a • f + b • g) : ℝ≥0∞) • (E.energyMeasure f + E.energyMeasure g) := by
  have hn : ¬ ∀ f g : E.domain, E.IsInteriorHarmonic f → E.IsInteriorHarmonic g →
      ∀ᵐ x ∂(E.energyMeasure f + E.energyMeasure g),
        ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
          E.energyDensityRoot (E.energyMeasure f + E.energyMeasure g) (a • f + b • g) x ≤
            ε * (‖a‖ + ‖b‖) := fun H ↦ h (E.hasPairwiseEnergyDependence_of_interiorHarmonic H μ hdom)
  obtain ⟨f, hf⟩ := not_forall.mp hn
  obtain ⟨g, hg⟩ := not_forall.mp hf
  obtain ⟨hf, hfg⟩ := not_imp.mp hg
  obtain ⟨hg, hg'⟩ := not_imp.mp hfg
  obtain ⟨A, d, hA, hpos, hd, hbound⟩ := E.exists_positive_pair_direction_bound f g hg'
  obtain ⟨f', g', u, v, Θ, hf', hg', hu, hv, hE, hΘ, hM⟩ :=
    E.exists_harmonic_fixed_direction_measures hcompact f g hf hg A hA hpos d hd hbound
  exact ⟨f', g', u, v, d, hf', hg', hu, hv, hE, hd, E.fixed_real_directions_of_rational f' g' d hE Θ hΘ hM⟩

end CarpetEnergy.SelfSimilarPEnergy
