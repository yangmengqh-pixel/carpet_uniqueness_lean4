import EnergyBoundaryCovariance

/-!
# Cellwise clamping with prescribed boundary values

A continuous competitor agreeing with given boundary values can be
clamped to the range of those data on each cell. The pieces still agree
and contract the energy.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- Clamp a competitor cell by cell, retaining fixed boundary values and
using the oscillation of the datum to control the uniform error. -/
theorem exists_cellwise_clamp (n : ℕ) (f v : C(CarpetPoints, ℝ)) (hv : continuousLp p v ∈ E.domain)
    (htrace : ∀ x ∈ carpetCellBoundary n, v x = f x) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ (w : Fin n → Fin 8) x y,
      |f (wordMap (List.ofFn w) x) - f (wordMap (List.ofFn w) y)| ≤ ε) :
    ∃ (g : C(CarpetPoints, ℝ)) (hg : continuousLp p g ∈ E.domain),
      (∀ x ∈ carpetCellBoundary n, g x = f x) ∧ ‖g - f‖ ≤ ε ∧
      E.energy ⟨continuousLp p g, hg⟩ ≤ E.energy ⟨continuousLp p v, hv⟩ := by
  let Q := E.zeroComponent
  let W := Fin n → Fin 8
  let F (w : W) := wordMap (List.ofFn w)
  let a (w : W) := sInf (range (f ∘ F w))
  let b (w : W) := sSup (range (f ∘ F w))
  have hcompact (w : W) : IsCompact (range (f ∘ F w)) :=
    isCompact_range (f.continuous.comp (continuous_wordMap _))
  have ha (w : W) (x : CarpetPoints) : a w ≤ f (F w x) :=
    csInf_le (hcompact w).bddBelow (mem_range_self x)
  have hb (w : W) (x : CarpetPoints) : f (F w x) ≤ b w :=
    le_csSup (hcompact w).bddAbove (mem_range_self x)
  have hab (w : W) : a w ≤ b w := (ha w (bottomPoint 0)).trans (hb w (bottomPoint 0))
  let φ (w : W) (t : ℝ) := min (max t (a w)) (b w)
  have hφ (w : W) : LipschitzWith 1 (φ w) := (LipschitzWith.id.max_const _).min_const _
  have hφfix (w : W) (t : ℝ) (ht : t ∈ Icc (a w) (b w)) : φ w t = t :=
    (congrArg (fun z : ℝ ↦ min z (b w)) (max_eq_left ht.1)).trans (min_eq_left ht.2)
  let V (w : W) : C(CarpetPoints, ℝ) := v.comp ⟨F w, continuous_wordMap _⟩
  let G (w : W) : C(CarpetPoints, ℝ) := (⟨φ w, (hφ w).continuous⟩ : C(ℝ, ℝ)).comp (V w)
  have hvQ : v ∈ Q.continuousKernel := ⟨hv, rfl⟩
  have hGQ (w : W) : G w ∈ Q.continuousKernel :=
    Q.continuousKernel_comp (Q.continuousKernel_comp_wordMap hvQ _) (hφ w)
  have hfix (w : W) (x : CarpetPoints) (hx : F w x ∈ carpetCellBoundary n) :
      G w x = f (F w x) := by
    change φ w (v (F w x)) = _
    rw [htrace _ hx]
    exact hφfix w _ ⟨ha w x, hb w x⟩
  have hagree (w z : W) (x y : CarpetPoints) (he : F w x = F z y) : G w x = G z y := by
    by_cases h : w = z
    · subst z
      rw [(measurableEmbedding_wordMap (List.ofFn w)).injective he]
    · have hx : F w x ∈ carpetCellBoundary n :=
        inter_word_subset_cellBoundary h ⟨mem_range_self x, ⟨y, he.symm⟩⟩
      rw [hfix w x hx, hfix z y (he ▸ hx), he]
  obtain ⟨g, ⟨hg, _⟩, hgG⟩ := Q.exists_continuousKernel_cellwise n G hGQ hagree
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, y, hy, rfl⟩ := mem_iUnion.mp hx
    rw [hgG, hfix w y hx]
  · apply (ContinuousMap.norm_le (g - f) hε).mpr
    intro z
    obtain ⟨w, x, rfl⟩ := exists_wordMap_range n z
    change ‖g (F w x) - f (F w x)‖ ≤ ε
    rw [hgG, Real.norm_eq_abs, abs_le]
    have hlo : f (F w x) - ε ≤ a w := by
      apply le_csInf ⟨_, mem_range_self x⟩
      rintro _ ⟨y, rfl⟩
      have h := (abs_le.mp (hosc w y x)).1
      change f (F w x) - ε ≤ f (F w y)
      linarith [h]
    have hhi : b w ≤ f (F w x) + ε := by
      apply csSup_le ⟨_, mem_range_self x⟩
      rintro _ ⟨y, rfl⟩
      have h := (abs_le.mp (hosc w y x)).2
      change f (F w y) ≤ f (F w x) + ε
      linarith [h]
    have haG : a w ≤ G w x := le_min (le_max_right _ _) (hab w)
    have hbG : G w x ≤ b w := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  · let g' : E.domain := ⟨continuousLp p g, hg⟩
    let v' : E.domain := ⟨continuousLp p v, hv⟩
    have he (w : W) : E.energy (E.pullbackWord (List.ofFn w) g') ≤
        E.energy (E.pullbackWord (List.ofFn w) v') := by
      let uw := E.pullbackWord (List.ofFn w) v'
      obtain ⟨z, hz, hΓ⟩ := E.exists_energyMeasure_comp_le (hφ w) uw
      have hV : continuousLp p (V w) = (uw : CarpetLp p) :=
        continuousLp_interpolate_word_eq v hv (V w) _ (fun _ ↦ rfl)
      have hG := continuousLp_interpolate_word_eq g hg (G w) _ (hgG w)
      have hz' : (z : CarpetLp p) = continuousLp p (G w) := by
        apply Lp.ext
        have hV' : (uw : CarpetLp p) =ᵐ[carpetMeasure] V w := by
          rw [← hV]
          exact continuousLp_ae_eq p (V w)
        have hφ' : φ w ∘ (uw : CarpetLp p) =ᵐ[carpetMeasure] G w :=
          hV'.mono fun x hx ↦ congrArg (φ w) hx
        exact hz.trans (hφ'.trans (continuousLp_ae_eq p (G w)).symm)
      have hzg : z = E.pullbackWord (List.ofFn w) g' := Subtype.ext (hz'.trans hG)
      have h := hΓ univ
      rw [hzg, smul_apply, smul_eq_mul, E.energyMeasure_univ, E.energyMeasure_univ,
        NNReal.one_rpow, ENNReal.coe_one, one_mul] at h
      exact ENNReal.coe_le_coe.mp h
    apply NNReal.coe_le_coe.mp
    change (E.energy g' : ℝ) ≤ (E.energy v' : ℝ)
    rw [E.energy_eq_sum_words n, E.energy_eq_sum_words n]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun w _ ↦ NNReal.coe_le_coe.mpr (he w)))
      (pow_nonneg E.isScalingFactor_scalingFactor.1.le n)

end CarpetEnergy.SelfSimilarPEnergy
