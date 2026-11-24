import EnergyAdjacentCells
import EnergyWalkScale

/-!
# Amplifying the energy by folding

Folding preserves the carpet probability and copies the original profile
into all eight first-level cells up to square symmetries. The energy
is multiplied by the walk scale. Iteration makes the ambient Lp part
of the rescaled graph norm tend to zero.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy

theorem measurePreserving_cellFoldingMap (i : Fin 8) :
    MeasurePreserving (cellFoldingMap i) carpetMeasure carpetMeasure := by
  let m := (cellFoldingMap i).continuous.measurable
  refine ⟨m, ?_⟩
  conv_lhs => rw [carpetMeasure_eq_sum_cells]
  rw [Measure.map_sum m.aemeasurable]
  trans Measure.sum (fun _ : Fin 8 ↦ (8 : ℝ≥0∞)⁻¹ • carpetMeasure)
  · congr 1
    funext j
    obtain ⟨σ, hσ⟩ := exists_cellFoldingMap_comp_cellMap i j
    rw [Measure.map_smul _ m.aemeasurable, Measure.map_map m (continuous_cellMap j).measurable,
      hσ, (measurePreserving_carpetSymmetry σ).map_eq]
  · ext A hA
    rw [Measure.sum_apply _ hA, tsum_fintype]
    simp only [smul_apply, smul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_cast
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul]

namespace SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- The continuous finite-energy core, as a linear subspace of continuous functions. -/
noncomputable def continuousCore : Submodule ℝ C(CarpetPoints, ℝ) :=
  E.domain.comap (continuousLpLinear p)

/-- Inclusion of the continuous core into the energy domain. -/
noncomputable def continuousCoreToDomain : E.continuousCore →ₗ[ℝ] E.domain :=
  ((continuousLpLinear p).comp E.continuousCore.subtype).codRestrict E.domain
    (fun f ↦ f.property)

private theorem continuousCoreToDomain_coe (f : E.continuousCore) :
    (E.continuousCoreToDomain f : CarpetLp p) = continuousLp p f.val := rfl

/-- Folding in the orientation of the bottom-left cell. -/
noncomputable def foldCore : E.continuousCore →ₗ[ℝ] E.continuousCore where
  toFun f := ⟨f.val.comp (cellFoldingMap 0), E.continuous_gluing _ |>.mpr fun i ↦
    (E.exists_folded_cell_energy f.val f.property 0 i).choose⟩
  map_add' f g := Subtype.ext (by ext x; rfl)
  map_smul' a f := Subtype.ext (by ext x; rfl)

theorem energy_foldCore (f : E.continuousCore) :
    (E.energy (E.continuousCoreToDomain (E.foldCore f)) : ℝ) =
      (8 * E.scalingFactor) * (E.energy (E.continuousCoreToDomain f) : ℝ) := by
  let g := E.continuousCoreToDomain (E.foldCore f)
  have he (j : Fin 8) : E.energy (E.pullback j g) = E.energy (E.continuousCoreToDomain f) := by
    obtain ⟨h, hh⟩ := E.exists_folded_cell_energy f.val f.property 0 j
    have hp : E.pullback j g = ⟨continuousLp p ((f.val.comp (cellFoldingMap 0)).comp ⟨cellMap j, continuous_cellMap j⟩), h⟩ := by
      apply Subtype.ext
      change cellPullback j (continuousLp p (f.val.comp (cellFoldingMap 0))) = _
      exact cellPullback_continuousLp p j (f.val.comp (cellFoldingMap 0))
    rw [hp]
    exact hh
  change (E.energy g : ℝ) = _
  rw [E.isScalingFactor_scalingFactor.2 g]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem norm_foldCore [Fact (1 ≤ ENNReal.ofReal p)] (f : E.continuousCore) :
    ‖(E.continuousCoreToDomain (E.foldCore f) : CarpetLp p)‖ = ‖(E.continuousCoreToDomain f : CarpetLp p)‖ := by
  let M := measurePreserving_cellFoldingMap 0
  rw [← Lp.norm_compMeasurePreserving (E.continuousCoreToDomain f : CarpetLp p) M]
  congr 1

private noncomputable def foldCoreIterate : ℕ → E.continuousCore →ₗ[ℝ] E.continuousCore
  | 0 => LinearMap.id
  | n + 1 => E.foldCore.comp (foldCoreIterate n)

private theorem energy_foldCoreIterate (n : ℕ) (f : E.continuousCore) :
    (E.energy (E.continuousCoreToDomain (E.foldCoreIterate n f)) : ℝ) =
      (8 * E.scalingFactor) ^ n * (E.energy (E.continuousCoreToDomain f) : ℝ) := by
  induction n with
  | zero => simp [foldCoreIterate]
  | succ n ih =>
    simp only [foldCoreIterate, LinearMap.comp_apply, energy_foldCore, ih, pow_succ']
    ring

private theorem norm_foldCoreIterate [Fact (1 ≤ ENNReal.ofReal p)] (n : ℕ) (f : E.continuousCore) :
    ‖(E.continuousCoreToDomain (E.foldCoreIterate n f) : CarpetLp p)‖ =
      ‖(E.continuousCoreToDomain f : CarpetLp p)‖ := by
  induction n with
  | zero => simp [foldCoreIterate]
  | succ n ih => simpa only [foldCoreIterate, LinearMap.comp_apply, norm_foldCore] using ih

/-- The n-fold extension with its energy amplification divided out. -/
noncomputable def scaledFold (n : ℕ) : E.continuousCore →ₗ[ℝ] E.GraphDomain :=
  let L : E.continuousCore →ₗ[ℝ] E.GraphDomain :=
    { toFun := fun f ↦ E.toGraph (E.continuousCoreToDomain f),
      map_add' := fun x y ↦ E.continuousCoreToDomain.map_add x y,
      map_smul' := fun a x ↦ E.continuousCoreToDomain.map_smul a x }
  ((((8 * E.scalingFactor) ^ n) ^ p⁻¹)⁻¹ : ℝ) • (L.comp (E.foldCoreIterate n))

theorem scaledFold_norm_tendsto (f : E.continuousCore) :
    Tendsto (fun n ↦ ‖E.scaledFold n f‖) atTop (𝓝 (E.rootSeminorm (E.continuousCoreToDomain f))) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  have hρ : 0 < E.scalingFactor := E.isScalingFactor_scalingFactor.1
  let r := 8 * E.scalingFactor
  have hr : 1 < r := by
    have h := (div_le_iff₀ (show 0 < (8 : ℝ) by norm_num)).mp E.three_rpow_div_eight_le_scalingFactor
    exact (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hp).trans_le
      (by dsimp only [r]; linarith only [h])
  let v := E.continuousCoreToDomain f
  have he (n : ℕ) : ‖E.scaledFold n f‖ = ((E.energy v : ℝ) +
      (r⁻¹) ^ n * ‖(v : CarpetLp p)‖ ^ p) ^ p⁻¹ := by
    let z := E.continuousCoreToDomain (E.foldCoreIterate n f)
    let a := ((r ^ n) ^ p⁻¹)⁻¹
    have ha : 0 ≤ a := inv_nonneg.mpr (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hr.le) _) _)
    have hpos : 0 < r ^ n := pow_pos (zero_lt_one.trans hr) _
    have haE : a ^ p = (r ^ n)⁻¹ := by
      dsimp only [a]
      rw [Real.inv_rpow (Real.rpow_nonneg hpos.le _), Real.rpow_inv_rpow hpos.le hp.ne']
    change E.graphSeminorm (a • z) = _
    rw [E.graphSeminorm_apply, energyGraphNorm, E.smul_energy, abs_of_nonneg ha]
    change ((a ^ p * (E.energy z : ℝ)) + ‖a • (z : CarpetLp p)‖ ^ p) ^ p⁻¹ = _
    rw [norm_smul_of_nonneg ha, Real.mul_rpow ha (norm_nonneg _), haE,
      E.energy_foldCoreIterate n f, E.norm_foldCoreIterate n f]
    change (((r ^ n)⁻¹ * (r ^ n * (E.energy v : ℝ))) +
      (r ^ n)⁻¹ * ‖(v : CarpetLp p)‖ ^ p) ^ p⁻¹ = _
    rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, inv_pow]
  simp only [he]
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (zero_le_one.trans hr.le))
    (inv_lt_one_of_one_lt₀ hr)
  have h := (tendsto_const_nhds.add (ht.mul_const (‖(v : CarpetLp p)‖ ^ p)) :
    Tendsto (fun n ↦ (E.energy v : ℝ) + (r⁻¹) ^ n * ‖(v : CarpetLp p)‖ ^ p) atTop
      (𝓝 ((E.energy v : ℝ) + 0 * ‖(v : CarpetLp p)‖ ^ p)))
  have hh := ((Real.continuous_rpow_const (inv_nonneg.mpr hp.le)).tendsto _).comp h
  change Tendsto (fun n ↦ ((E.energy v : ℝ) + (r⁻¹) ^ n * ‖(v : CarpetLp p)‖ ^ p) ^ p⁻¹)
    atTop (𝓝 (((E.energy v : ℝ) + 0 * ‖(v : CarpetLp p)‖ ^ p) ^ p⁻¹)) at hh
  rw [zero_mul, add_zero] at hh
  rw [E.rootSeminorm_apply]
  exact hh

end SelfSimilarPEnergy
end CarpetEnergy
