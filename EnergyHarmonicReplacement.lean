import EnergyHarmonicMinimization
import EnergyAdjacentCellMeans
import EnergyRootUniformConvex
import SeminormPowerMidpoints

/-!
# Uniqueness of harmonic replacement

The uniform midpoint inequality extends from the continuous core to the
graph domain. An exterior set of positive measure fixes the additive
constant in the minimization problem.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem exists_domain_energy_midpoint_deficit (ε : ℝ) (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ f g : E.domain,
      (E.energy (f - g) : ℝ) + C * (E.energy ((1 / 2 : ℝ) • (f + g)) : ℝ) ≤
        (ε + C / 2) * ((E.energy f : ℝ) + (E.energy g : ℝ)) := by
  let S := E.rootSeminorm.comp E.continuousCoreToDomain
  obtain ⟨C, hC, hgap⟩ := power_deficit_controls_difference S E.one_lt_p
    (fun e he ↦ E.exists_root_midpoint_gap e he) ε hε
  have hPow (f : E.continuousCore) :
      S f ^ p = (E.energy (E.continuousCoreToDomain f) : ℝ) := by
    change E.rootSeminorm (E.continuousCoreToDomain f) ^ p = _
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) (zero_lt_one.trans E.one_lt_p).ne'
  refine ⟨C, hC, fun f g ↦ ?_⟩
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have approx (v : E.domain) : ∃ a : ℕ → E.continuousCore,
      Tendsto (fun n ↦ E.toGraph (E.continuousCoreToDomain (a n))) atTop (𝓝 (E.toGraph v)) := by
    choose u hu hnear using fun n ↦ E.regular_graph v (r n) (hr n)
    refine ⟨fun n ↦ ⟨u n, hu n⟩, ?_⟩
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ ↦ norm_nonneg _) (fun n ↦ (hnear n).le)
  obtain ⟨u, hu⟩ := approx f
  obtain ⟨v, hv⟩ := approx g
  let F (z : E.GraphDomain) := (E.energy (E.graphToDomain z) : ℝ)
  have hF : Continuous F := E.continuous_graphEnergy
  have h₁ := (hF.tendsto _).comp (hu.sub hv)
  have h₂ := (hF.tendsto _).comp ((hu.add hv).const_smul (1 / 2 : ℝ))
  have h₃ := (hF.tendsto _).comp hu
  have h₄ := (hF.tendsto _).comp hv
  apply le_of_tendsto_of_tendsto (h₁.add (h₂.const_mul C)) ((h₃.add h₄).const_mul (ε + C / 2))
  filter_upwards with n
  have h := hgap (u n) (v n)
  simp only [hPow, map_sub, map_smul, map_add] at h
  change (E.energy (E.continuousCoreToDomain (u n) - E.continuousCoreToDomain (v n)) : ℝ) +
    C * (E.energy ((1 / 2 : ℝ) • (E.continuousCoreToDomain (u n) + E.continuousCoreToDomain (v n))) : ℝ) ≤
      (ε + C / 2) * ((E.energy (E.continuousCoreToDomain (u n)) : ℝ) +
        (E.energy (E.continuousCoreToDomain (v n)) : ℝ))
  linarith only [h]

/-- Equal endpoint and midpoint energies force the endpoints to differ
by a constant. -/
theorem energy_sub_eq_zero_of_energy_midpoint_eq (f g : E.domain)
    (he : E.energy f = E.energy g)
    (hm : E.energy ((1 / 2 : ℝ) • (f + g)) = E.energy f) :
    E.energy (f - g) = 0 := by
  apply NNReal.coe_eq_zero.mp
  by_contra h
  let a := (E.energy (f - g) : ℝ)
  let b := (E.energy f : ℝ)
  have ha : 0 < a := lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm h)
  have hb : 0 ≤ b := NNReal.coe_nonneg _
  let ε := a / (2 * b + 1)
  have hd : 0 < 2 * b + 1 := by positivity
  obtain ⟨C, _, hC⟩ := E.exists_domain_energy_midpoint_deficit ε (div_pos ha hd)
  have hbound := hC f g
  rw [hm, ← he] at hbound
  have hab : a ≤ ε * (2 * b) := by
    change a + C * b ≤ (ε + C / 2) * (b + b) at hbound
    linarith only [hbound]
  have hlt : ε * (2 * b) < a := by
    calc
      ε * (2 * b) < ε * (2 * b + 1) :=
        mul_lt_mul_of_pos_left (lt_add_one _) (div_pos ha hd)
      _ = a := div_mul_cancel₀ _ hd.ne'
  exact hlt.not_ge hab

/-- Minimization with exterior values prescribed almost everywhere. -/
def MinimizesWithExterior (A : Set CarpetPoints) (f : E.domain) : Prop :=
  ∀ g : E.domain, (g : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (f : CarpetLp p) →
    E.energy f ≤ E.energy g

theorem MinimizesWithExterior.eq_of_ae_eq {A : Set CarpetPoints}
    (hA : carpetMeasure A ≠ 0) {f g : E.domain}
    (hf : E.MinimizesWithExterior A f) (hg : E.MinimizesWithExterior A g)
    (hfg : (f : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (g : CarpetLp p)) : f = g := by
  let m : E.domain := (1 / 2 : ℝ) • (f + g)
  have he := le_antisymm (hf g hfg.symm) (hg f hfg)
  have hm : (m : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (f : CarpetLp p) := by
    have hsmul := Lp.coeFn_smul (1 / 2 : ℝ) ((f : CarpetLp p) + (g : CarpetLp p))
    filter_upwards [hsmul.filter_mono (ae_mono Measure.restrict_le_self),
      (Lp.coeFn_add (f : CarpetLp p) (g : CarpetLp p)).filter_mono (ae_mono Measure.restrict_le_self),
      hfg] with x hs hadd hx
    change (((1 / 2 : ℝ) • ((f : CarpetLp p) + (g : CarpetLp p))) : CarpetLp p) x =
      (f : CarpetLp p) x
    have hs' : (((1 / 2 : ℝ) • ((f : CarpetLp p) + (g : CarpetLp p))) : CarpetLp p) x =
        (1 / 2 : ℝ) * (((f : CarpetLp p) + (g : CarpetLp p)) : CarpetLp p) x := hs
    have hadd' : (((f : CarpetLp p) + (g : CarpetLp p)) : CarpetLp p) x =
        (f : CarpetLp p) x + (g : CarpetLp p) x := hadd
    rw [hs', hadd', ← hx]
    ring
  have hroot (u : E.domain) :
      E.rootSeminorm u ^ p = (E.energy u : ℝ) := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) (zero_lt_one.trans E.one_lt_p).ne'
  have hmid : E.energy m ≤ E.energy f := by
    have hh := E.rootSeminorm.add_le' f g
    change E.rootSeminorm (f + g) ≤ E.rootSeminorm f + E.rootSeminorm g at hh
    have hh' : E.rootSeminorm f = E.rootSeminorm g := by simp only [E.rootSeminorm_apply, he]
    rw [← hh'] at hh
    have hle : E.rootSeminorm m ≤ E.rootSeminorm f := by
      dsimp only [m]
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      linarith only [hh]
    exact NNReal.coe_le_coe.mp (by
      rw [← hroot m, ← hroot f]
      exact Real.rpow_le_rpow (apply_nonneg _ _) hle (zero_lt_one.trans E.one_lt_p).le)
  obtain ⟨c, hc⟩ := (E.zero_iff_constant (f - g)).mp
    (E.energy_sub_eq_zero_of_energy_midpoint_eq f g he (le_antisymm hmid (hf m hm)))
  have hsub : (constantLp p c : CarpetLp p) =ᵐ[carpetMeasure.restrict A] fun _ ↦ (0 : ℝ) := by
    change (f : CarpetLp p) - (g : CarpetLp p) = constantLp p c at hc
    rw [← hc]
    filter_upwards [(Lp.coeFn_sub (f : CarpetLp p) (g : CarpetLp p)).filter_mono
      (ae_mono Measure.restrict_le_self), hfg] with x hx heq
    change (((f : CarpetLp p) - (g : CarpetLp p)) : CarpetLp p) x =
      (f : CarpetLp p) x - (g : CarpetLp p) x at hx
    rw [hx, heq, sub_self]
  have : NeZero (carpetMeasure.restrict A) := ⟨fun hn ↦ hA
    (by simpa [Measure.restrict_apply MeasurableSet.univ] using congrArg (fun μ : Measure CarpetPoints ↦ μ univ) hn)⟩
  have hz : c = 0 := by
    have hh := (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure c).filter_mono
      (ae_mono (Measure.restrict_le_self (s := A)))
    change (constantLp p c : CarpetLp p) =ᵐ[carpetMeasure.restrict A] fun _ ↦ c at hh
    obtain ⟨x, hx⟩ := (hh.symm.trans hsub).exists
    exact hx
  apply sub_eq_zero.mp
  apply Subtype.ext
  rw [hc, hz]
  apply Lp.ext
  exact (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (0 : ℝ)).trans
    (Lp.coeFn_zero (E := ℝ) (ENNReal.ofReal p) carpetMeasure).symm

/-- The exterior data determine exactly one harmonic replacement. -/
theorem existsUnique_minimizesWithExterior (A : Set CarpetPoints)
    (hA : carpetMeasure A ≠ 0) (f : E.domain) :
    ∃! h : E.domain, (h : CarpetLp p) =ᵐ[carpetMeasure.restrict A] (f : CarpetLp p) ∧
      E.MinimizesWithExterior A h := by
  obtain ⟨h, hh, hmin⟩ := E.exists_harmonic_with_fixed_values A hA f
  have hhmin : E.MinimizesWithExterior A h :=
    fun g hg ↦ hmin g (hg.trans hh)
  exact ⟨h, ⟨hh, hhmin⟩, fun g hg ↦
    MinimizesWithExterior.eq_of_ae_eq E hA hg.2 hhmin (hg.1.trans hh.symm)⟩

end CarpetEnergy.SelfSimilarPEnergy
