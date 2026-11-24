import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Invariant densities and proportional energy measures

These lemmas formalize the measure-theoretic argument of Section 7 in
Meng Yang, *On the uniqueness of p-energy on the Sierpiński carpet*.
They are stated for a family of measurable maps on an arbitrary measurable space.
-/

open Function Set Filter MeasureTheory
open scoped ENNReal

namespace CarpetEnergy

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A family of maps satisfies a zero-one law if every measurable set invariant
up to a null set under all maps in the family is null or conull. -/
def HasZeroOneLaw (μ : Measure X) (maps : ι → X → X) : Prop :=
  ∀ A : Set X, MeasurableSet A →
    (∀ i, ∀ᵐ x ∂μ, maps i x ∈ A ↔ x ∈ A) →
    μ A = 0 ∨ μ Aᶜ = 0

/-- The rational level set argument of Proposition 7.7. -/
theorem ae_eq_const_of_invariant_of_bounded {maps : ι → X → X}
    (zeroOne : HasZeroOneLaw μ maps) {a : X → ℝ} (ha : Measurable a)
    (invariant : ∀ i, a ∘ maps i =ᵐ[μ] a) {lower upper : ℝ} (hle : lower ≤ upper)
    (bounds : ∀ᵐ x ∂μ, lower ≤ a x ∧ a x ≤ upper) :
    ∃ c ∈ Icc lower upper, a =ᵐ[μ] fun _ ↦ c := by
  by_cases hμ : μ = 0
  · exact ⟨lower, ⟨le_rfl, hle⟩, by simp [hμ, Filter.EventuallyEq]⟩
  have cuts : ∀ᵐ x ∂μ, ∀ q : ℚ,
      ((q : ℝ) < a x ↔ μ {y : X | (q : ℝ) < a y} ≠ 0) := by
    rw [ae_all_iff]
    intro q
    let A : Set X := {y | (q : ℝ) < a y}
    rcases zeroOne A (measurableSet_lt measurable_const ha) (fun i ↦
      (invariant i).mono fun x hx ↦ by
        change (q : ℝ) < a (maps i x) ↔ (q : ℝ) < a x
        rw [show a (maps i x) = a x from hx]) with hA | hAc
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hA] with x hx
      exact iff_of_false hx (not_not_intro hA)
    · have hn : μ A ≠ 0 := fun hA ↦ by
        apply hμ (Measure.measure_univ_eq_zero.mp _)
        simpa only [union_compl_self] using measure_union_null hA hAc
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hAc] with x hx
      exact iff_of_true (not_not.mp hx) hn
  have : NeBot (ae μ) := ae_neBot.mpr hμ
  obtain ⟨x₀, hx₀, hb₀⟩ := (cuts.and bounds).exists
  refine ⟨a x₀, hb₀, cuts.mono fun x hx ↦ ?_⟩
  apply le_antisymm
  · by_contra! h
    obtain ⟨q, h₀, h₁⟩ := exists_rat_btwn h
    exact h₀.not_ge (le_of_lt ((hx₀ q).mpr ((hx q).mp h₁)))
  · by_contra! h
    obtain ⟨q, h₀, h₁⟩ := exists_rat_btwn h
    exact h₀.not_ge (le_of_lt ((hx q).mpr ((hx₀ q).mp h₁)))

private theorem map_withDensity_comp {τ : X → X} (hτ : Measurable τ)
    (ν : Measure X) {b : X → ℝ≥0∞} (hb : Measurable b) :
    (ν.withDensity (b ∘ τ)).map τ = (ν.map τ).withDensity b := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hτ hA, withDensity_apply _ (hτ hA), withDensity_apply _ hA,
    setLIntegral_map hA hb hτ]
  rfl

/-- Transport a common density through a measurable cell embedding, using the
same covariance factor for both measure families. This is the change of
variables in Proposition 7.6. -/
theorem ae_eq_comp_of_restrict_map {τ : X → X} (hτ : MeasurableEmbedding τ)
    {ν ν' η η' : Measure X} [IsFiniteMeasure ν'] {s : ℝ≥0∞}
    (hs₀ : s ≠ 0) (hsTop : s ≠ ⊤) {a : X → ℝ} (ha : Measurable a)
    (hν : ν.restrict (range τ) = s • ν'.map τ)
    (hη : η.restrict (range τ) = s • η'.map τ)
    (hd : η = ν.withDensity fun x ↦ ENNReal.ofReal (a x))
    (hd' : η' = ν'.withDensity fun x ↦ ENNReal.ofReal (a x))
    (hna : ∀ x, 0 ≤ a x) :
    a ∘ τ =ᵐ[ν'] a := by
  let b : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (a x)
  have hb : Measurable b := ha.ennreal_ofReal
  change η = ν.withDensity b at hd
  change η' = ν'.withDensity b at hd'
  have hmap : s • (ν'.withDensity b).map τ = s • (ν'.withDensity (b ∘ τ)).map τ := by
    calc
      s • (ν'.withDensity b).map τ = η.restrict (range τ) := by rw [hη, hd']
      _ = (ν.restrict (range τ)).withDensity b := by
        rw [hd, restrict_withDensity hτ.measurableSet_range]
      _ = s • (ν'.withDensity (b ∘ τ)).map τ := by
        rw [hν, withDensity_smul_measure, map_withDensity_comp hτ.measurable ν' hb]
  have hcancel := congrArg (fun ν₁ : Measure X ↦ s⁻¹ • ν₁) hmap
  simp only [smul_smul, ENNReal.inv_mul_cancel hs₀ hsTop, one_smul] at hcancel
  have heq := (withDensity_eq_iff_of_sigmaFinite hb.aemeasurable (hb.comp hτ.measurable).aemeasurable).mp
    (hτ.map_injective hcancel)
  exact heq.symm.mono fun x hx ↦
    (ENNReal.ofReal_eq_ofReal_iff (hna (τ x)) (hna x)).mp hx

/-- It suffices to apply the cell calculation to the family used to construct
the reference measure. The extension condition is the input supplied by the
folding construction on the dense family in Section 7. -/
theorem ae_eq_comp_of_restrict_map_sum {F J : Type*} [Countable J]
    {τ : X → X} (hτ : MeasurableEmbedding τ) (pullback : F → F)
    (Γ₀ Γ : F → Measure X) (finite : ∀ f, IsFiniteMeasure (Γ₀ f))
    (d : J → F) (weight : J → ℝ≥0∞) (extend : ∀ j, ∃ g, pullback g = d j)
    {s : ℝ≥0∞} (hs₀ : s ≠ 0) (hsTop : s ≠ ⊤)
    {a : X → ℝ} (ha : Measurable a) (hna : ∀ x, 0 ≤ a x)
    (density : ∀ f, Γ f = (Γ₀ f).withDensity fun x ↦ ENNReal.ofReal (a x))
    (cov₀ : ∀ f, (Γ₀ f).restrict (range τ) = s • (Γ₀ (pullback f)).map τ)
    (cov : ∀ f, (Γ f).restrict (range τ) = s • (Γ (pullback f)).map τ) :
    a ∘ τ =ᵐ[Measure.sum (fun j ↦ weight j • Γ₀ (d j))] a := by
  apply ae_iff.mpr
  rw [Measure.sum_apply_eq_zero]
  · intro j
    obtain ⟨g, hg⟩ := extend j
    have : IsFiniteMeasure (Γ₀ (pullback g)) := finite _
    have heq := ae_eq_comp_of_restrict_map hτ hs₀ hsTop ha (cov₀ g) (cov g)
      (density g) (density (pullback g)) hna
    rw [hg] at heq
    rw [smul_apply, ae_iff.mp heq, smul_zero]

/-- In the self-similar decomposition, off-diagonal cells contribute zero
if their preimages of the overlap are null. This is the restriction identity
in Lemma 7.2, expressed using pushforward measures. -/
theorem restrict_eq_smul_map_of_null_overlaps {I : Type*}
    (cell : I → X → X) (embed : ∀ i, MeasurableEmbedding (cell i))
    (ν : I → Measure X) (s : ℝ≥0∞) (j : I)
    (disjoint_ae : ∀ i ≠ j, ν i ((cell i) ⁻¹' range (cell j)) = 0) :
    (Measure.sum (fun i ↦ s • (ν i).map (cell i))).restrict (range (cell j)) = s • (ν j).map (cell j) := by
  classical
  ext A hA
  rw [Measure.restrict_apply hA]
  have hB := hA.inter (embed j).measurableSet_range
  rw [Measure.sum_apply _ hB, tsum_eq_single j]
  · rw [smul_apply, smul_apply, (embed j).map_apply, (embed j).map_apply, preimage_inter,
      preimage_range, inter_univ]
  · intro i hij
    rw [smul_apply, (embed i).map_apply, preimage_inter]
    rw [measure_mono_null inter_subset_right (disjoint_ae i hij), smul_zero]

/-- An almost everywhere constant common density gives the same multiplier
for each energy measure and, in particular, for its total mass. -/
theorem proportional_of_invariant_density {F : Type*} {maps : ι → X → X}
    (zeroOne : HasZeroOneLaw μ maps) {Γ₀ Γ : F → Measure X} {a : X → ℝ}
    (ha : Measurable a) (invariant : ∀ i, a ∘ maps i =ᵐ[μ] a)
    {lower upper : ℝ} (hpos : 0 < lower) (hle : lower ≤ upper)
    (bounds : ∀ᵐ x ∂μ, lower ≤ a x ∧ a x ≤ upper)
    (dominates : ∀ f, Γ₀ f ≪ μ)
    (density : ∀ f, Γ f = (Γ₀ f).withDensity fun x ↦ ENNReal.ofReal (a x)) :
    ∃ c ∈ Icc lower upper, 0 < c ∧
      ∀ f, Γ f = ENNReal.ofReal c • Γ₀ f ∧ (Γ f univ).toReal = c * (Γ₀ f univ).toReal := by
  obtain ⟨c, hc, heq⟩ := ae_eq_const_of_invariant_of_bounded zeroOne ha invariant hle bounds
  have hcpos := hpos.trans_le hc.1
  refine ⟨c, hc, hcpos, fun f ↦ ?_⟩
  have hΓ : Γ f = ENNReal.ofReal c • Γ₀ f := by
    have hd : (fun x ↦ ENNReal.ofReal (a x)) =ᵐ[Γ₀ f] fun _ ↦ ENNReal.ofReal c :=
      ((dominates f).ae_eq heq).mono fun _ hx ↦ congrArg ENNReal.ofReal hx
    rw [density f, withDensity_congr_ae hd, withDensity_const]
  refine ⟨hΓ, ?_⟩
  rw [hΓ, smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le]

end CarpetEnergy
