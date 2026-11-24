import CarpetGammaMixedContraction

/-!
# Homogeneity and constant invariance of the limiting energy

The finite energies depend only on differences of cell averages.
Homogeneity and translation by constants therefore pass through the
Γ-limit by recovery and the local lower bound.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace CarpetEnergy

theorem IsGammaLimit.apply_le_mul_of_apply_le_mul {X : Type*} [TopologicalSpace X]
    {Fₙ : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞} (hF : IsGammaLimit Fₙ F)
    {g : X → X} (hg : Continuous g) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : ∀ n x, Fₙ n (g x) ≤ c * Fₙ n x) (x : X) :
    F (g x) ≤ c * F x := by
  by_cases hc₀ : c = 0
  · rw [hc₀, zero_mul]
    by_contra! hpos
    obtain ⟨a, ha, hA⟩ := exists_between (show 0 < F (g x) from hpos)
    obtain ⟨V, hV, hlow⟩ := hF.lower (g x) a hA
    obtain ⟨m, hm⟩ := hlow.exists
    have hpos' := (hm (g x) (mem_of_mem_nhds hV)).trans (h m x)
    rw [hc₀, zero_mul] at hpos'
    exact ha.not_ge hpos'
  by_contra! hlt
  have hd : F x < F (g x) / c :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hc₀) (Or.inl hc)).mpr
      (by simpa only [mul_comm] using hlt)
  obtain ⟨a, hx, ha⟩ := exists_between hd
  have hCa : c * a < F (g x) := by
    have hh := (ENNReal.lt_div_iff_mul_lt (Or.inl hc₀) (Or.inl hc)).mp ha
    simpa only [mul_comm] using hh
  obtain ⟨U, hU, hlo⟩ := hF.lower (g x) (c * a) hCa
  have hV : g ⁻¹' U ∈ 𝓝 x := (hg.tendsto x) hU
  obtain ⟨n, hn, z, hz, ha'⟩ := (hlo.and (hF.recovery x _ hV a hx)).exists
  exact (ENNReal.mul_lt_mul_right hc₀ hc ha').not_ge ((hn (g z) hz).trans (h n z))

theorem discreteCellEnergy_smul {p ρ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (n : ℕ)
    (a : ℝ) (f : CarpetLp p) :
    discreteCellEnergy p ρ n (a • f) = ENNReal.ofReal (|a| ^ p) * discreteCellEnergy p ρ n f := by
  classical
  unfold discreteCellEnergy
  simp only [map_smul, smul_eq_mul, ← mul_sub, abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg _)]
  simp_rw [← Finset.mul_sum]
  rw [mul_left_comm, ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]

theorem discreteCellEnergy_add_constant {p ρ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (n : ℕ) (a : ℝ) (f : CarpetLp p) :
    discreteCellEnergy p ρ n (f + constantLp p a) = discreteCellEnergy p ρ n f := by
  have hconst (w : Fin n → Fin 8) : ambientWordMean p (List.ofFn w) (constantLp p a) = a :=
    ambientWordMean_eq_of_ae_eq_on_openWordCell w (ae_restrict_of_ae
      (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a))
  unfold discreteCellEnergy
  simp only [map_add, hconst, add_sub_add_right_eq_sub]

theorem IsGammaLimit.discreteCellEnergy_add_constant {p ρ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {j : ℕ → ℕ} {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p ρ (j n)) F)
    (a : ℝ) (f : CarpetLp p) : F (f + constantLp p a) = F f := by
  have hf (b : ℝ) (u : CarpetLp p) : F (u + constantLp p b) ≤ F u :=
    hF.apply_le_of_apply_le (continuous_id.add continuous_const)
      (fun n x ↦ (CarpetEnergy.discreteCellEnergy_add_constant (ρ := ρ) (j n) b x).le) u
  have hconst : constantLp p a + constantLp p (-a) = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (constantLp p a) (constantLp p (-a)),
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a,
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (-a), Lp.coeFn_zero ℝ (ENNReal.ofReal p) carpetMeasure]
      with x h₁ h₂ h₃ h₄
    change constantLp p a x = a at h₂
    change constantLp p (-a) x = -a at h₃
    rw [h₁, Pi.add_apply, h₂, h₃, add_neg_cancel, h₄]
    rfl
  exact le_antisymm (hf a f) (by simpa only [add_assoc, hconst, add_zero] using hf (-a) (f + constantLp p a))

theorem IsGammaLimit.discreteCellEnergy_smul {p ρ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    {j : ℕ → ℕ} {F : CarpetLp p → ℝ≥0∞}
    (hF : IsGammaLimit (fun n ↦ discreteCellEnergy p ρ (j n)) F)
    (a : ℝ) (f : CarpetLp p) : F (a • f) = ENNReal.ofReal (|a| ^ p) * F f := by
  have hle (b : ℝ) (u : CarpetLp p) : F (b • u) ≤ ENNReal.ofReal (|b| ^ p) * F u :=
    hF.apply_le_mul_of_apply_le_mul (g := fun x : CarpetLp p ↦ b • x)
      (c := ENNReal.ofReal (|b| ^ p)) (by fun_prop) ENNReal.ofReal_ne_top
      (fun n x ↦ (CarpetEnergy.discreteCellEnergy_smul (ρ := ρ) (j n) b x).le) u
  apply le_antisymm (hle a f)
  by_cases ha : a = 0
  · simp only [ha, abs_zero, Real.zero_rpow hp.ne', ENNReal.ofReal_zero, zero_mul]
    exact bot_le
  let c := ENNReal.ofReal (|a| ^ p)
  have hpos : 0 < |a| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr ha) _
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have h' := hle a⁻¹ (a • f)
  rw [inv_smul_smul₀ ha, abs_inv, Real.inv_rpow (abs_nonneg a), ENNReal.ofReal_inv_of_pos hpos] at h'
  change F f ≤ c⁻¹ * F (a • f) at h'
  calc
    c * F f ≤ c * (c⁻¹ * F (a • f)) := mul_le_mul' le_rfl h'
    _ = F (a • f) := by rw [← mul_assoc, ENNReal.mul_inv_cancel hc ENNReal.ofReal_ne_top, one_mul]

end CarpetEnergy
