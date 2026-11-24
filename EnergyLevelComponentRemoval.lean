import EnergyCutoff
import EnergyLocalMidpointDeficit

/-!
# Removing the excess on a union of superlevel components
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 2300000 in
/-- Removing the positive excess on selected superlevel components
subtracts exactly the energy of that excess. -/
theorem exists_superlevel_component_excess
    (f : E.continuousCore) (t : ℝ) (S : Set CarpetPoints) :
    let U := ⋃ x : S, connectedComponentIn {y | t < f.val y} x.val
    ∃ v : E.continuousCore,
      (∀ x ∈ U, v.val x = f.val x - t) ∧
      (∀ x ∉ U, v.val x = 0) ∧
      (E.energy (E.continuousCoreToDomain (f - v)) : ℝ) +
        (E.energy (E.continuousCoreToDomain v) : ℝ) =
        (E.energy (E.continuousCoreToDomain f) : ℝ) := by
  let φ (s : ℝ) := max (s - t) 0
  have hφ : LipschitzWith 1 φ := by
    have hs : LipschitzWith 1 (fun s : ℝ ↦ s - t) :=
      LipschitzWith.of_dist_le_mul fun x y ↦ by rw [dist_sub_right, NNReal.coe_one, one_mul]
    simpa only [one_mul, Function.comp_def] using Lp.lipschitzWith_pos_part.comp hs
  obtain ⟨u, hu, huv, _⟩ := E.exists_continuous_comp_energy_le_mul f.val f.property hφ
  let U := ⋃ x : S, connectedComponentIn {y | t < f.val y} x.val
  have hU : IsOpen U := isOpen_iUnion fun _ ↦ (isOpen_lt continuous_const f.val.continuous).connectedComponentIn
  have hu₀ (x : CarpetPoints) : 0 ≤ u x := (huv x).symm ▸ le_max_right _ _
  have hpos : {x | 0 < u x} = {y | t < f.val y} := by
    ext x
    simp only [mem_ofPred_eq, huv, φ, lt_max_iff, lt_irrefl, or_false, sub_pos]
  obtain ⟨g, hg, hG, _⟩ := E.exists_continuous_indicator_of_component_union u hu hu₀ S
  rw [hpos] at hG
  let v : E.continuousCore := ⟨g, hg⟩
  have hv (x : CarpetPoints) : v.val x = U.indicator u x := congrFun hG x
  have hsub : U ⊆ {y | t < f.val y} := iUnion_subset fun x ↦ connectedComponentIn_subset _ _
  have hv1 (x : CarpetPoints) (hx : x ∈ U) : v.val x = f.val x - t := by
    rw [hv, indicator_of_mem hx, huv]
    change max (f.val x - t) 0 = _
    exact max_eq_left (sub_pos.mpr (show t < f.val x from hsub hx)).le
  have hv0 (x : CarpetPoints) (hx : x ∉ U) : v.val x = 0 := by
    rw [hv, indicator_of_notMem hx]
  refine ⟨v, hv1, hv0, ?_⟩
  let F := f - v
  let μ := E.energyMeasure (E.continuousCoreToDomain f)
  let ν := E.energyMeasure (E.continuousCoreToDomain v)
  let κ := E.energyMeasure (E.continuousCoreToDomain F)
  have hν : ν U = μ U := by
    exact E.energyMeasure_apply_eq_of_sub_constant hU.measurableSet
      v.val f.val v.property f.property (a := -t) (fun x hx ↦ by rw [hv1 x hx]; ring)
  have hν₀ : ν Uᶜ = 0 :=
    measure_mono_null (fun x hx ↦ hv0 x hx) (E.energyMeasure_levelSet_eq_zero v.val v.property 0)
  have hκ : κ Uᶜ = μ Uᶜ := by
    exact E.energyMeasure_apply_eq_of_sub_constant hU.measurableSet.compl
      F.val f.val F.property f.property (a := 0) (fun x hx ↦ by
        change f.val x - v.val x - f.val x = 0
        rw [hv0 x hx, sub_zero, sub_self])
  have hκ₀ : κ U = 0 := by
    apply measure_mono_null _ (E.energyMeasure_levelSet_eq_zero F.val F.property t)
    intro x hx
    change f.val x - v.val x = t
    rw [hv1 x hx]
    ring
  have hadd (η : Measure CarpetPoints) : η univ = η U + η Uᶜ := by
    rw [← measure_union disjoint_compl_right hU.measurableSet.compl, union_compl_self]
  have he : κ univ + ν univ = μ univ := by
    rw [hadd κ, hadd ν, hadd μ, hν, hν₀, hκ, hκ₀, zero_add, add_zero, add_comm]
  have hh := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hh
  simpa only [μ, ν, κ, E.energyMeasure_univ, ENNReal.coe_toReal, F] using hh

end CarpetEnergy.SelfSimilarPEnergy
