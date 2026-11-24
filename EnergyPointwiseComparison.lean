import EnergyDensities
import EnergyQuasiUniqueness

/-!
# Simultaneous comparison of density seminorms

On a countable rational subspace the normalized reference measure supplies
a common exceptional set, on whose complement the two density roots are
seminorms with uniform comparison constants.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E D : SelfSimilarPEnergy p)

/-- The two-sided energy measure comparison in (7.1). -/
theorem exists_energyMeasure_comparison :
    ∃ (h : E.domain ≤ D.domain) (C : ℝ≥0), 1 ≤ C ∧
      ∀ f : E.domain, E.energyMeasure f ≤
        (C : ℝ≥0∞) • D.energyMeasure (Submodule.inclusion h f) ∧
        D.energyMeasure (Submodule.inclusion h f) ≤ (C : ℝ≥0∞) • E.energyMeasure f := by
  obtain ⟨hED, A, _, hA⟩ := D.exists_energy_le E
  obtain ⟨hDE, B, _, hB⟩ := E.exists_energy_le D
  let C := max 1 (max A B)
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hED, C, le_max_left _ _, fun f ↦ ⟨?_, ?_⟩⟩
  · have hB' (f : E.domain) : E.energy f ≤ B * D.energy (Submodule.inclusion hED f) := by
      have he : Submodule.inclusion hDE (Submodule.inclusion hED f) = f := Subtype.ext rfl
      simpa only [he] using hB (Submodule.inclusion hED f)
    have h := E.energyMeasure_le_of_energy_le D hED (E.scalingFactor_eq D) B hB' f
    refine h.trans (fun s ↦ ?_)
    simp only [smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.coe_le_coe.mpr hBC) le_rfl
  · have hA' (f : D.domain) : D.energy f ≤ A * E.energy (Submodule.inclusion hDE f) := by
      have he : Submodule.inclusion hED (Submodule.inclusion hDE f) = f := Subtype.ext rfl
      simpa only [he] using hA (Submodule.inclusion hDE f)
    have h := D.energyMeasure_le_of_energy_le E hDE (D.scalingFactor_eq E) A hA'
      (Submodule.inclusion hED f)
    have he : Submodule.inclusion hDE (Submodule.inclusion hED f) = f := Subtype.ext rfl
    rw [he] at h
    refine h.trans (fun s ↦ ?_)
    simp only [smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.coe_le_coe.mpr hAC) le_rfl

/-- The simultaneous seminorm, density, comparison and normalization
identities of Lemma 7.3. The null set can contain any prescribed reference-null set. -/
theorem exists_pointwise_density_comparison
    (h : E.domain ≤ D.domain) (C : ℝ≥0)
    (hcomp : ∀ f : E.domain, E.energyMeasure f ≤
      (C : ℝ≥0∞) • D.energyMeasure (Submodule.inclusion h f) ∧
      D.energyMeasure (Submodule.inclusion h f) ≤ (C : ℝ≥0∞) • E.energyMeasure f)
    (V : Submodule ℚ E.domain) [Countable V] (d : ℕ → V)
    (hdense : ∀ f : E.domain, ∃ j : ℕ → ℕ,
      Tendsto (fun n ↦ E.rootSeminorm (f - (d (j n) : E.domain))) atTop (𝓝 0))
    (A : Set CarpetPoints)
    (hA : E.energyReferenceMeasure (fun n ↦ (d n : E.domain)) A = 0) :
    let u := fun n ↦ (d n : E.domain)
    let μ := E.energyReferenceMeasure u
    ∃ N : Set CarpetPoints, MeasurableSet N ∧ μ N = 0 ∧ A ⊆ N ∧
      ∀ x ∉ N, ∃ R T : Seminorm ℚ V,
        (∀ f : V, R f = E.energyDensityRoot μ (f : E.domain) x ∧
          T f = D.energyDensityRoot μ (Submodule.inclusion h (f : E.domain)) x ∧
          ENNReal.ofReal (R f ^ p) = (E.energyMeasure (f : E.domain)).rnDeriv μ x ∧
          ENNReal.ofReal (T f ^ p) =
            (D.energyMeasure (Submodule.inclusion h (f : E.domain))).rnDeriv μ x ∧
          R f ≤ (C : ℝ) ^ p⁻¹ * T f ∧ T f ≤ (C : ℝ) ^ p⁻¹ * R f) ∧
        (∑' n, E.energyReferenceWeight u n * ENNReal.ofReal (R (d n) ^ p)) = 1 := by
  classical
  let u := fun n ↦ (d n : E.domain)
  let μ := E.energyReferenceMeasure u
  have hE (f : E.domain) : E.energyMeasure f ≪ μ :=
    E.energyMeasure_absolutelyContinuous_reference u hdense f
  let L := (Submodule.inclusion h).restrictScalars ℚ
  have hinj : Injective L := fun a b hab ↦ Subtype.ext (congrArg (fun z : D.domain ↦ (z : CarpetLp p)) hab)
  let W := V.map L
  let F : V ≃ₗ[ℚ] W := Submodule.equivMapOfInjective L hinj V
  have hF (f : V) : (F f : D.domain) = Submodule.inclusion h (f : E.domain) := rfl
  have : Countable W := F.symm.injective.countable
  have hD' (f : E.domain) : D.energyMeasure (Submodule.inclusion h f) ≪ μ := by
    exact (Measure.absolutelyContinuous_of_le_smul (hcomp f).2).trans (hE f)
  have hD (g : D.domain) : D.energyMeasure g ≪ μ := by
    have hg : (g : CarpetLp p) ∈ E.domain := by rw [E.domain_eq D]; exact g.property
    let f : E.domain := ⟨g, hg⟩
    have he : Submodule.inclusion h f = g := Subtype.ext rfl
    rw [← he]
    exact hD' f
  have hbounds : ∀ᵐ x ∂μ, ∀ f : V,
      E.energyDensityRoot μ (f : E.domain) x ≤
        (C : ℝ) ^ p⁻¹ * D.energyDensityRoot μ (Submodule.inclusion h (f : E.domain)) x ∧
      D.energyDensityRoot μ (Submodule.inclusion h (f : E.domain)) x ≤
        (C : ℝ) ^ p⁻¹ * E.energyDensityRoot μ (f : E.domain) x := by
    refine ae_all_iff.mpr fun f ↦ ?_
    exact (E.ae_energyDensityRoot_le_of_energyMeasure_le_smul D μ _ _ (hE f)
      (hD' f) C (hcomp f).1).and
      (D.ae_energyDensityRoot_le_of_energyMeasure_le_smul E μ _ _ (hD' f)
        (hE f) C (hcomp f).2)
  have hfinite : ∀ᵐ x ∂μ, ∀ f : V,
      (E.energyMeasure (f : E.domain)).rnDeriv μ x ≠ ∞ ∧
      (D.energyMeasure (Submodule.inclusion h (f : E.domain))).rnDeriv μ x ≠ ∞ :=
    ae_all_iff.mpr fun f ↦ ((E.energyMeasure (f : E.domain)).rnDeriv_ne_top μ).and
      ((D.energyMeasure (Submodule.inclusion h (f : E.domain))).rnDeriv_ne_top μ)
  let Good (x : CarpetPoints) := ∃ R T : Seminorm ℚ V,
    (∀ f : V, R f = E.energyDensityRoot μ (f : E.domain) x ∧
      T f = D.energyDensityRoot μ (Submodule.inclusion h (f : E.domain)) x ∧
      ENNReal.ofReal (R f ^ p) = (E.energyMeasure (f : E.domain)).rnDeriv μ x ∧
      ENNReal.ofReal (T f ^ p) =
        (D.energyMeasure (Submodule.inclusion h (f : E.domain))).rnDeriv μ x ∧
      R f ≤ (C : ℝ) ^ p⁻¹ * T f ∧ T f ≤ (C : ℝ) ^ p⁻¹ * R f) ∧
    (∑' n, E.energyReferenceWeight u n * ENNReal.ofReal (R (d n) ^ p)) = 1
  have hgood : ∀ᵐ x ∂μ, Good x := by
    filter_upwards [E.ae_exists_energyDensityRoot_seminorm μ hE V,
      D.ae_exists_energyDensityRoot_seminorm μ hD W, hbounds, hfinite,
      E.ae_reference_density_sum_eq_one u hdense] with x hR hT hb hf hs
    obtain ⟨R, hR⟩ := hR
    obtain ⟨T, hT⟩ := hT
    let T' : Seminorm ℚ V := Seminorm.of (fun f ↦ T (F f))
      (fun f g ↦ by rw [map_add]; exact map_add_le_add T _ _)
      (fun c f ↦ by rw [map_smul, map_smul_eq_mul])
    have ht (f : V) : T' f = D.energyDensityRoot μ (Submodule.inclusion h (f : E.domain)) x :=
      (hT (F f)).trans (congrArg (fun g ↦ D.energyDensityRoot μ g x) (hF f))
    have hpR (f : V) : ENNReal.ofReal (R f ^ p) =
        (E.energyMeasure (f : E.domain)).rnDeriv μ x := by
      rw [hR]
      exact E.ofReal_energyDensityRoot_pow μ _ (hf f).1
    refine ⟨R, T', fun f ↦ ⟨hR f, ht f, hpR f, ?_, ?_⟩, ?_⟩
    · rw [ht]
      exact D.ofReal_energyDensityRoot_pow μ _ (hf f).2
    · rw [hR, ht]
      exact hb f
    · simpa only [hpR] using hs
  have hbad : μ {x | ¬Good x} = 0 := ae_iff.mp hgood
  obtain ⟨N, hNsub, hN, hNnull⟩ := exists_measurable_superset_of_null (measure_union_null hbad hA)
  refine ⟨N, hN, hNnull, subset_union_right.trans hNsub, fun x hx ↦ ?_⟩
  change Good x
  by_contra hn
  exact hx (hNsub (Or.inl hn))

end CarpetEnergy.SelfSimilarPEnergy
