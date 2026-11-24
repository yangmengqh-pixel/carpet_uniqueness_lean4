import CarpetMeasure
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Self-similar p-energies

Definition 2.1 of Yang's *On the uniqueness of p-energy on the Sierpiński carpet*.
The domain is a real subspace of the (L^p) space of the normalized carpet measure.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

/-- Real-valued (L^p) classes for the carpet's reference measure. -/
noncomputable abbrev CarpetLp (p : ℝ) := Lp ℝ (ENNReal.ofReal p) carpetMeasure

/-- The (L^p) class of a continuous function on the carpet. -/
noncomputable def continuousLp (p : ℝ) (u : C(CarpetPoints, ℝ)) : CarpetLp p :=
  (u.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)).toLp u

theorem continuousLp_ae_eq (p : ℝ) (u : C(CarpetPoints, ℝ)) :
    continuousLp p u =ᵐ[carpetMeasure] u :=
  MemLp.coeFn_toLp _

theorem continuousLp_injective (p : ℝ) : Injective (continuousLp p) := by
  intro u v huv
  have hv : continuousLp p u =ᵐ[carpetMeasure] v := by
    rw [huv]
    exact continuousLp_ae_eq p v
  have heq : (u : CarpetPoints → ℝ) =ᵐ[carpetMeasure] v :=
    (continuousLp_ae_eq p u).symm.trans hv
  exact DFunLike.coe_injective (Measure.eq_of_ae_eq heq u.continuous v.continuous)

/-- The (L^p) class of a constant function. -/
noncomputable def constantLp (p a : ℝ) : CarpetLp p :=
  Lp.const (ENNReal.ofReal p) carpetMeasure a

/-- The equality identifying a pullback as an (L^p) class. -/
def IsLpPullback {p : ℝ} (φ : CarpetPoints → CarpetPoints) (f g : CarpetLp p) : Prop :=
  g =ᵐ[carpetMeasure] f ∘ φ

theorem IsLpPullback.unique {p : ℝ} {φ : CarpetPoints → CarpetPoints}
    {f g h : CarpetLp p} (hg : IsLpPullback (p := p) φ f g) (hh : IsLpPullback (p := p) φ f h) :
    g = h :=
  Lp.ext (hg.trans hh.symm)

private theorem memLp_cellPullback {p : ℝ} (i : Fin 8) (f : CarpetLp p) :
    MemLp (f ∘ cellMap i) (ENNReal.ofReal p) carpetMeasure :=
  (((Lp.memLp f).smul_measure (c := (8 : ℝ≥0∞)) (by norm_num)).mono_measure
    (map_cellMap_le i)).comp_of_map (measurableEmbedding_cellMap i).measurable.aemeasurable

/-- Pullback of an (L^p) class by a first-level cell embedding. -/
noncomputable def cellPullback {p : ℝ} (i : Fin 8) (f : CarpetLp p) : CarpetLp p :=
  (memLp_cellPullback i f).toLp (f ∘ cellMap i)

theorem cellPullback_isLpPullback {p : ℝ} (i : Fin 8) (f : CarpetLp p) :
    IsLpPullback (p := p) (cellMap i) f (cellPullback i f) :=
  MemLp.coeFn_toLp _

/-- Pullback of an (L^p) class by a square symmetry. -/
noncomputable def symmetryPullback {p : ℝ} (σ : SquareSymmetry) (f : CarpetLp p) : CarpetLp p :=
  Lp.compMeasurePreserving _ (measurePreserving_carpetSymmetry σ) f

theorem symmetryPullback_isLpPullback {p : ℝ} (σ : SquareSymmetry) (f : CarpetLp p) :
    IsLpPullback (p := p) (carpetSymmetry σ) f (symmetryPullback σ f) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_carpetSymmetry σ)

theorem cellPullback_continuousLp (p : ℝ) (i : Fin 8) (u : C(CarpetPoints, ℝ)) :
    cellPullback i (continuousLp p u) =
      continuousLp p (u.comp ⟨cellMap i, continuous_cellMap i⟩) := by
  apply (cellPullback_isLpPullback i (continuousLp p u)).unique
  have hq : QuasiMeasurePreserving (cellMap i) carpetMeasure carpetMeasure :=
    ⟨(measurableEmbedding_cellMap i).measurable.aemeasurable, map_cellMap_absolutelyContinuous i⟩
  exact (continuousLp_ae_eq p _).trans (hq.ae_eq_comp (continuousLp_ae_eq p u)).symm

/-- The graph norm specified in (SSEb). -/
noncomputable def energyGraphNorm {p : ℝ} {F : Submodule ℝ (CarpetLp p)}
    (E : F → NNReal) (f : F) : ℝ :=
  ((E f : ℝ) + ‖(f : CarpetLp p)‖ ^ p) ^ p⁻¹

/-- Definition 2.1, including the six conditions (SSEa)–(SSEf). -/
structure SelfSimilarPEnergy (p : ℝ) where
  one_lt_p : 1 < p
  domain : Submodule ℝ (CarpetLp p)
  energy : domain → NNReal
  /-- The constants belong to the domain, as required by (SSEa). -/
  constant_mem : ∀ a : ℝ, constantLp p a ∈ domain
  zero_iff_constant : ∀ f : domain, energy f = 0 ↔ ∃ a : ℝ, (f : CarpetLp p) = constantLp p a
  add_constant : ∀ (f : domain) (a : ℝ),
    energy (f + ⟨constantLp p a, constant_mem a⟩) = energy f
  smul_energy : ∀ (a : ℝ) (f : domain), (energy (a • f) : ℝ) = |a| ^ p * (energy f : ℝ)
  /-- The root of the energy is a seminorm, as required by (SSEb). -/
  rootSeminorm : Seminorm ℝ domain
  rootSeminorm_apply : ∀ f, rootSeminorm f = (energy f : ℝ) ^ p⁻¹
  graphSeminorm : Seminorm ℝ domain
  graphSeminorm_apply : ∀ f, graphSeminorm f = energyGraphNorm (p := p) energy f
  graph_complete :
    letI := graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
    CompleteSpace domain
  graph_uniformConvex :
    letI := graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
    UniformConvexSpace domain
  /-- Sup-norm density in continuous functions, as required by the first half of (SSEc). -/
  regular_sup : ∀ (u : C(CarpetPoints, ℝ)) (ε : ℝ), 0 < ε →
    ∃ v : C(CarpetPoints, ℝ), continuousLp p v ∈ domain ∧ ‖v - u‖ < ε
  /-- Graph-norm density of continuous domain functions, the second half of (SSEc). -/
  regular_graph : ∀ (f : domain) (ε : ℝ), 0 < ε →
    ∃ (v : C(CarpetPoints, ℝ)) (hv : continuousLp p v ∈ domain),
      graphSeminorm (⟨continuousLp p v, hv⟩ - f) < ε
  /-- Invariance under all eight square symmetries, as required by (SSEd). -/
  symmetry : ∀ (σ : SquareSymmetry) (f : domain), ∃ g : domain,
    IsLpPullback (p := p) (carpetSymmetry σ) f g ∧ energy g = energy f
  /-- One positive scaling factor works for all domain functions in (SSEe). -/
  selfSimilar : ∃ ρ : ℝ, 0 < ρ ∧ ∀ f : domain, ∃ g : Fin 8 → domain,
    (∀ i, IsLpPullback (p := p) (cellMap i) f (g i)) ∧
    (energy f : ℝ) = ρ * ∑ i : Fin 8, (energy (g i) : ℝ)
  continuous_gluing : ∀ u : C(CarpetPoints, ℝ), continuousLp p u ∈ domain ↔
    ∀ i : Fin 8, continuousLp p (u.comp ⟨cellMap i, continuous_cellMap i⟩) ∈ domain
  /-- Unit contractivity, as required by (SSEf). -/
  unit_contractivity : ∀ f : domain, ∃ g : domain,
    ((g : CarpetLp p) =ᵐ[carpetMeasure] fun x ↦ min (max ((f : CarpetLp p) x) 0) 1) ∧
    energy g ≤ energy f

namespace SelfSimilarPEnergy

/-- The graph seminorm is definite because it controls the (L^p) norm. -/
theorem graphSeminorm_eq_zero_iff {p : ℝ} (E : SelfSimilarPEnergy p) (f : E.domain) :
    E.graphSeminorm f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
    have hnorm : 0 ≤ ‖(f : CarpetLp p)‖ := norm_nonneg _
    have hpow : 0 ≤ ‖(f : CarpetLp p)‖ ^ p := Real.rpow_nonneg hnorm _
    have henergy : 0 ≤ (E.energy f : ℝ) := (E.energy f).property
    rw [E.graphSeminorm_apply, energyGraphNorm, Real.rpow_eq_zero_iff_of_nonneg
      (add_nonneg henergy hpow)] at h
    have hpow' : ‖(f : CarpetLp p)‖ ^ p = 0 := by linarith [h.1]
    have hz : ‖(f : CarpetLp p)‖ = 0 :=
      ((Real.rpow_eq_zero_iff_of_nonneg hnorm).mp hpow').1
    exact Subtype.ext (norm_eq_zero.mp hz)
  · rintro rfl
    exact map_zero E.graphSeminorm

end SelfSimilarPEnergy

end CarpetEnergy
