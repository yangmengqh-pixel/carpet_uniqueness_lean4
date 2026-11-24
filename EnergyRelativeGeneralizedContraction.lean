import EnergySelfSimilarMixedContraction

/-!
# Generalized contraction of a self-similarized Γ-limit

The finite-exponent inequalities and their componentwise maximum
endpoint are obtained at the scale and on the domain of a given
self-similar energy.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The finite-exponent part of the generalized p-contraction property
[27, Definition 2.2], with both sides raised to the power p. -/
def HasFiniteGeneralizedPContraction (G : E.domain → ℝ) : Prop :=
  ∀ (m n : ℕ) (q₁ q₂ : ℝ), 0 < q₁ → q₁ ≤ p → p ≤ q₂ →
    ∀ (T : (Fin m → ℝ) → Fin n → ℝ),
      (∀ x y, finitePowerSum q₂ (fun i ↦ |T x i - T y i|) ≤
        finitePowerSum q₁ (fun i ↦ |x i - y i|)) →
      ∀ {L : Fin n → ℝ≥0} (hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i)
        (h0 : ∀ i, T 0 i = 0),
        ∃ hD : E.MixedOperationMapsDomain T hLip h0,
          E.HasMixedEnergyBound (q₁ / p) (q₂ / p) G hD

/-- The infinity endpoint of the generalized p-contraction property,
expressed by one bound on each output component. -/
def HasInfinityGeneralizedPContraction (G : E.domain → ℝ) : Prop :=
  ∀ (m n : ℕ) (q₁ : ℝ), 0 < q₁ → q₁ ≤ p →
    ∀ (T : (Fin m → ℝ) → Fin n → ℝ),
      (∀ x y i, |T x i - T y i| ≤ finitePowerSum q₁ (fun j ↦ |x j - y j|)) →
      ∀ {L : Fin n → ℝ≥0} (hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i)
        (h0 : ∀ i, T 0 i = 0),
        ∃ hD : E.MixedOperationMapsDomain T hLip h0,
          ∀ u : Fin m → E.domain, ∀ i : Fin n,
            G ⟨pointwiseLp T hLip h0 (fun j ↦ (u j : CarpetLp p)) i, hD u i⟩ ≤
              finitePowerSum (q₁ / p) (fun j ↦ G (u j))

private theorem finitePowerSum_fin_one {q : ℝ} (hq : 0 < q) {a : ℝ} (ha : 0 ≤ a) :
    finitePowerSum (I := Fin 1) q (fun _ ↦ a) = a := by
  unfold finitePowerSum
  rw [Fin.sum_univ_one, Real.rpow_rpow_inv ha hq.ne']

theorem HasFiniteGeneralizedPContraction.infinity {G : E.domain → ℝ}
    (hG : ∀ f, 0 ≤ G f) (h : E.HasFiniteGeneralizedPContraction G) :
    E.HasInfinityGeneralizedPContraction G := by
  intro m n q₁ h₁ h₁p T hT L hLip h0
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  let U (i : Fin n) : (Fin m → ℝ) → Fin 1 → ℝ := fun x _ ↦ T x i
  let B (i : Fin n) : Fin 1 → ℝ≥0 := fun _ ↦ L i
  have hB (i : Fin n) (j : Fin 1) : LipschitzWith (B i j) (fun x ↦ U i x j) := hLip i
  have hZ (i : Fin n) (j : Fin 1) : U i 0 j = 0 := h0 i
  have hcontr (i : Fin n) (x y : Fin m → ℝ) :
      finitePowerSum p (fun j ↦ |U i x j - U i y j|) ≤ finitePowerSum q₁ (fun j ↦ |x j - y j|) := by
    rw [show (fun j ↦ |U i x j - U i y j|) = fun _ : Fin 1 ↦ |T x i - T y i| from rfl,
      finitePowerSum_fin_one hp (abs_nonneg _)]
    exact hT x y i
  choose hD hbound using fun i : Fin n ↦ h m 1 q₁ p h₁ h₁p le_rfl (U i) (hcontr i) (hB i) (hZ i)
  let D : E.MixedOperationMapsDomain T hLip h0 := fun u i ↦ hD i u 0
  refine ⟨D, fun u i ↦ ?_⟩
  have hb := hbound i u
  simp only [div_self hp.ne'] at hb
  change finitePowerSum (I := Fin 1) 1 (fun _ ↦
    G ⟨pointwiseLp T hLip h0 (fun j ↦ (u j : CarpetLp p)) i, D u i⟩) ≤ _ at hb
  rwa [finitePowerSum_fin_one zero_lt_one (hG _)] at hb

theorem renormalizedGammaLimit_hasFiniteGeneralizedPContraction
    {j : ℕ → ℕ} (hj : StrictMono j) {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F)
    {l : Filter ℕ} [l.NeBot] {G : E.domain → ℝ}
    (hlim : ∀ f, Tendsto (fun n ↦ renormalizationMean E.scalingFactor E.pullback
      (fun v : E.domain ↦ (F v).toReal) n f) l (𝓝 (G f))) :
    E.HasFiniteGeneralizedPContraction G := by
  intro m n q₁ q₂ h₁ h₁p h₂p T hT L hLip h0
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨hD, hbound⟩ := IsGammaLimit.exists_mixedEnergyBound E h₁ h₁p h₂p hj hF T hT hLip h0
  exact ⟨hD, HasMixedEnergyBound.of_renormalizationMean_limit E
    (div_pos h₁ hp) ((div_le_one hp).mpr h₁p) ((one_le_div hp).mpr h₂p)
    (fun _ ↦ ENNReal.toReal_nonneg) hbound hlim⟩

/-- If a Definition 2.1 energy is given, the rescaled graph energies
produce a comparable self-similar functional with the generalized
p-contraction property on that domain. -/
theorem exists_selfSimilarized_discreteLimit_with_generalized_contraction :
    ∃ G : E.domain → ℝ, (∀ f, 0 ≤ G f) ∧
      (∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ f, A * (E.energy f : ℝ) ≤ G f ∧ G f ≤ B * (E.energy f : ℝ)) ∧
      (∀ f, G f = E.scalingFactor * ∑ i, G (E.pullback i f)) ∧
      E.HasFiniteGeneralizedPContraction G ∧ E.HasInfinityGeneralizedPContraction G := by
  obtain ⟨j, F, l, G, A, hA, B, hB, hj, hF, hl₀, _, hcomp, hlim, he⟩ :=
    E.exists_selfSimilarized_discreteLimit
  let : l.NeBot := hl₀
  have hG (f : E.domain) : 0 ≤ G f := (mul_nonneg hA.le (NNReal.coe_nonneg _)).trans (hcomp f).1
  have hh := E.renormalizedGammaLimit_hasFiniteGeneralizedPContraction hj hF hlim
  exact ⟨G, hG, ⟨A, hA, B, hB, hcomp⟩, he, hh, hh.infinity E hG⟩

end CarpetEnergy.SelfSimilarPEnergy
