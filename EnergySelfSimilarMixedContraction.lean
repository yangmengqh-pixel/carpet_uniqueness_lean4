import CarpetGammaMixedContraction
import EnergySelfSimilarization

/-!
# Mixed contraction under cell self-similarization

Pointwise operations commute with cell pullback. Nonnegative finite
sums preserve the mixed inequality, so it holds for the renormalization
iterates, their means, and their pointwise limit.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)
variable [Fact (1 ≤ ENNReal.ofReal p)]
variable {I O : Type*} [Fintype I]

/-- Invariance of the common domain under a pointwise vector operation. -/
def MixedOperationMapsDomain (T : (I → ℝ) → O → ℝ)
    {L : O → ℝ≥0} (hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i) (h0 : ∀ i, T 0 i = 0) : Prop :=
  ∀ (u : I → E.domain) i, pointwiseLp T hLip h0 (fun k ↦ (u k : CarpetLp p)) i ∈ E.domain

noncomputable def domainMixedOperation {T : (I → ℝ) → O → ℝ}
    {L : O → ℝ≥0} {hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i} {h0 : ∀ i, T 0 i = 0}
    (hD : E.MixedOperationMapsDomain T hLip h0) (u : I → E.domain) (i : O) : E.domain :=
  ⟨pointwiseLp T hLip h0 (fun k ↦ (u k : CarpetLp p)) i, hD u i⟩

private theorem pullback_domainMixedOperation {T : (I → ℝ) → O → ℝ}
    {L : O → ℝ≥0} {hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i} {h0 : ∀ i, T 0 i = 0}
    (hD : E.MixedOperationMapsDomain T hLip h0) (w : Fin 8) (u : I → E.domain) (i : O) :
    E.pullback w (E.domainMixedOperation hD u i) =
      E.domainMixedOperation hD (fun k ↦ E.pullback w (u k)) i := by
  apply Subtype.ext
  apply Lp.ext
  let f : I → CarpetLp p := fun k ↦ u k
  let g : I → CarpetLp p := fun k ↦ E.pullback w (u k)
  let hq : QuasiMeasurePreserving (cellMap w) carpetMeasure carpetMeasure :=
    ⟨(continuous_cellMap w).measurable.aemeasurable, map_cellMap_absolutelyContinuous w⟩
  have h₁ := cellPullback_isLpPullback w (pointwiseLp T hLip h0 f i)
  have h₂ := hq.ae_eq_comp (ae_pointwiseLp T hLip h0 f i)
  have h₃ := ae_pointwiseLp T hLip h0 g i
  have h₄ : ∀ᵐ x ∂carpetMeasure, ∀ k, g k x = f k (cellMap w x) :=
    ae_all_iff.mpr fun k ↦ cellPullback_isLpPullback w (f k)
  filter_upwards [h₁, h₂, h₃, h₄] with x h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans ((congrArg (fun v ↦ T v i) (funext h₄)).symm.trans h₃.symm))

variable [Fintype O]

/-- Mixed contraction of a real energy functional for an operation
preserving the common domain. The exponents are divided by p. -/
def HasMixedEnergyBound (r t : ℝ) (F : E.domain → ℝ)
    {T : (I → ℝ) → O → ℝ}
    {L : O → ℝ≥0} {hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i} {h0 : ∀ i, T 0 i = 0}
    (hD : E.MixedOperationMapsDomain T hLip h0) : Prop :=
  ∀ u : I → E.domain, finitePowerSum t (fun i ↦ F (E.domainMixedOperation hD u i)) ≤
    finitePowerSum r (fun i ↦ F (u i))

private theorem HasMixedEnergyBound.renormalize {r t : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (ht : 1 ≤ t) {F : E.domain → ℝ} (hF : ∀ f, 0 ≤ F f)
    {T : (I → ℝ) → O → ℝ}
    {L : O → ℝ≥0} {hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i} {h0 : ∀ i, T 0 i = 0}
    {hD : E.MixedOperationMapsDomain T hLip h0} (h : E.HasMixedEnergyBound r t F hD) :
    E.HasMixedEnergyBound r t (CarpetEnergy.renormalize E.scalingFactor E.pullback F) hD := by
  intro u
  unfold CarpetEnergy.renormalize
  simp_rw [Finset.mul_sum, E.pullback_domainMixedOperation]
  exact finitePowerSum_weighted_sum_le hr hr₁ ht (Finset.univ : Finset (Fin 8))
    (fun _ ↦ E.scalingFactor) (fun _ ↦ E.isScalingFactor_scalingFactor.1.le)
    (fun w i ↦ F (E.pullback w (u i)))
    (fun w i ↦ F (E.domainMixedOperation hD (fun j ↦ E.pullback w (u j)) i))
    (fun _ _ ↦ hF _) (fun _ _ ↦ hF _) (fun w _ ↦ h (fun j ↦ E.pullback w (u j)))

private theorem HasMixedEnergyBound.renormalizationMean {r t : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (ht : 1 ≤ t) {F : E.domain → ℝ} (hF : ∀ f, 0 ≤ F f)
    {T : (I → ℝ) → O → ℝ}
    {L : O → ℝ≥0} {hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i} {h0 : ∀ i, T 0 i = 0}
    {hD : E.MixedOperationMapsDomain T hLip h0} (h : E.HasMixedEnergyBound r t F hD)
    (n : ℕ) : E.HasMixedEnergyBound r t (CarpetEnergy.renormalizationMean E.scalingFactor E.pullback F n) hD := by
  let Z (n : ℕ) := (CarpetEnergy.renormalize E.scalingFactor E.pullback)^[n] F
  have hZ : ∀ k, (∀ f, 0 ≤ Z k f) ∧ E.HasMixedEnergyBound r t (Z k) hD := by
    intro k
    induction k with
    | zero => exact ⟨hF, h⟩
    | succ k ih =>
      simp only [Z, Function.iterate_succ_apply']
      exact ⟨fun f ↦ mul_nonneg E.isScalingFactor_scalingFactor.1.le
        (Finset.sum_nonneg fun _ _ ↦ ih.1 _), ih.2.renormalize E hr hr₁ ht ih.1⟩
  intro u
  unfold CarpetEnergy.renormalizationMean
  simp_rw [Finset.mul_sum]
  exact finitePowerSum_weighted_sum_le hr hr₁ ht (Finset.range (n + 1))
    (fun _ ↦ 1 / ((n : ℝ) + 1)) (fun _ ↦ by positivity)
    (fun k i ↦ Z k (u i)) (fun k i ↦ Z k (E.domainMixedOperation hD u i))
    (fun k _ ↦ (hZ k).1 _) (fun k _ ↦ (hZ k).1 _) (fun k _ ↦ (hZ k).2 u)

theorem IsGammaLimit.exists_mixedEnergyBound
    {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₁p : q₁ ≤ p) (h₂p : p ≤ q₂)
    {j : ℕ → ℕ} (hj : StrictMono j) {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p E.scalingFactor (j n)) F)
    (T : (I → ℝ) → O → ℝ)
    (hT : ∀ x y, finitePowerSum q₂ (fun i ↦ |T x i - T y i|) ≤
        finitePowerSum q₁ (fun i ↦ |x i - y i|))
    {L : O → ℝ≥0} (hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i) (h0 : ∀ i, T 0 i = 0) :
    ∃ hD : E.MixedOperationMapsDomain T hLip h0,
      E.HasMixedEnergyBound (q₁ / p) (q₂ / p) (fun f ↦ (F f).toReal) hD := by
  have hp := zero_lt_one.trans E.one_lt_p
  have hdom := IsGammaLimit.discreteLimit_domain_eq E hj hF
  have hfin (u : E.domain) : F u < ∞ := by
    change (u : CarpetLp p) ∈ {f | F f < ∞}
    rw [hdom]
    exact u.property
  have ht (u : I → E.domain) := hF.discreteCellEnergy_mixed_contraction E.one_lt_p.le
    E.isScalingFactor_scalingFactor.1.le h₁ h₁p h₂p hj T hT hLip h0
    (fun i ↦ (u i : CarpetLp p)) (fun i ↦ hfin (u i))
  let hD : E.MixedOperationMapsDomain T hLip h0 := fun u i ↦ by
    have hf := (ht u).1 i
    change pointwiseLp T hLip h0 (fun k ↦ (u k : CarpetLp p)) i ∈ {f | F f < ∞} at hf
    rwa [hdom] at hf
  refine ⟨hD, fun u ↦ ?_⟩
  let a (i : I) := (F (u i)).toReal
  let b (i : O) := (F (E.domainMixedOperation hD u i)).toReal
  have h := (ht u).2
  have hsa : ∀ i, ENNReal.ofReal (a i) = F (u i) :=
    fun i ↦ ENNReal.ofReal_toReal (hfin (u i)).ne
  have hsb : ∀ i, ENNReal.ofReal (b i) = F (pointwiseLp T hLip h0 (fun j ↦ (u j : CarpetLp p)) i) :=
    fun i ↦ ENNReal.ofReal_toReal ((ht u).1 i).ne
  have ha : extendedFinitePowerSum (q₁ / p) (fun i ↦ F (u i)) =
      ENNReal.ofReal (finitePowerSum (q₁ / p) a) := by
    rw [← funext hsa, extendedFinitePowerSum_ofReal (div_nonneg h₁.le hp.le) _ (fun _ ↦ ENNReal.toReal_nonneg)]
  have hb : extendedFinitePowerSum (q₂ / p)
      (fun i ↦ F (pointwiseLp T hLip h0 (fun j ↦ (u j : CarpetLp p)) i)) =
      ENNReal.ofReal (finitePowerSum (q₂ / p) b) := by
    rw [← funext hsb, extendedFinitePowerSum_ofReal (div_nonneg (hp.trans_le h₂p).le hp.le) _
      (fun _ ↦ ENNReal.toReal_nonneg)]
  rw [ha, hb] at h
  exact (ENNReal.ofReal_le_ofReal_iff (finitePowerSum_nonneg _ (a := a)
    (fun _ ↦ ENNReal.toReal_nonneg))).mp h

/-- The mixed inequalities survive the exact cell self-similarization
on the domain of a given energy. -/
theorem HasMixedEnergyBound.of_renormalizationMean_limit {r t : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (ht : 1 ≤ t) {F G : E.domain → ℝ} (hF : ∀ f, 0 ≤ F f)
    {T : (I → ℝ) → O → ℝ}
    {L : O → ℝ≥0} {hLip : ∀ i, LipschitzWith (L i) fun v ↦ T v i} {h0 : ∀ i, T 0 i = 0}
    {hD : E.MixedOperationMapsDomain T hLip h0} (h : E.HasMixedEnergyBound r t F hD)
    {l : Filter ℕ} [l.NeBot]
    (hlim : ∀ f, Tendsto (fun n ↦ CarpetEnergy.renormalizationMean E.scalingFactor E.pullback F n f) l (𝓝 (G f))) :
    E.HasMixedEnergyBound r t G hD := by
  intro u
  have h₁ := (continuous_finitePowerSum (I := O) (zero_le_one.trans ht)).tendsto
    (fun i ↦ G (E.domainMixedOperation hD u i))
  have h₂ := (continuous_finitePowerSum (I := I) hr.le).tendsto (fun i ↦ G (u i))
  exact le_of_tendsto_of_tendsto (h₁.comp (tendsto_pi_nhds.mpr fun i ↦ hlim _))
    (h₂.comp (tendsto_pi_nhds.mpr fun i ↦ hlim _))
    (Eventually.of_forall fun n ↦ (h.renormalizationMean E hr hr₁ ht hF n) u)

end CarpetEnergy.SelfSimilarPEnergy
