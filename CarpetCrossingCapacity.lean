import CarpetCapacity
import CarpetBoundary
import EnergyCutoff
import PlanarCrossing

/-!
# Capacity of two disjoint level-set crossings

A left-to-right crossing separates the top and bottom sides within its
complement. Cutting off one positive component at a time converts two
left-to-right level-set crossings into an opposite-side capacity competitor.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal unitInterval

namespace CarpetEnergy

private def carpetSquare (x : CarpetPoints) : I × I :=
  (⟨(x : Plane) 0, carpet_coord_mem_Icc x 0⟩, ⟨(x : Plane) 1, carpet_coord_mem_Icc x 1⟩)

private theorem continuous_carpetSquare : Continuous carpetSquare := by
  apply Continuous.prodMk
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_subtypeVal).subtype_mk _
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp continuous_subtypeVal).subtype_mk _

private theorem carpetSquare_injective : Injective carpetSquare := by
  intro x y h
  apply Subtype.ext
  ext j
  fin_cases j
  · exact congrArg (fun a : I × I ↦ (a.1 : ℝ)) h
  · exact congrArg (fun a : I × I ↦ (a.2 : ℝ)) h

private theorem not_disjoint_carpet_crossings {A B : Set CarpetPoints}
    (hA : IsCompact A) (hAc : IsPreconnected A) (hBc : IsPreconnected B)
    {a₀ a₁ b₀ b₁ : CarpetPoints} (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A)
    (hb₀ : b₀ ∈ B) (hb₁ : b₁ ∈ B)
    (hleft : (a₀ : Plane) 0 = 0) (hright : (a₁ : Plane) 0 = 1)
    (hbottom : b₀ ∈ carpetBottom) (htop : b₁ ∈ carpetTop) :
    ¬ Disjoint A B := by
  intro hd
  exact not_disjoint_of_connected_axis_crossings
    (hA.image continuous_carpetSquare)
    (hAc.image _ continuous_carpetSquare.continuousOn)
    (hBc.image _ continuous_carpetSquare.continuousOn)
    (mem_image_of_mem _ ha₀) (mem_image_of_mem _ ha₁) (mem_image_of_mem _ hb₀) (mem_image_of_mem _ hb₁)
    (Subtype.ext hleft) (Subtype.ext hright) (Subtype.ext hbottom) (Subtype.ext htop)
    (Set.disjoint_image_of_injective carpetSquare_injective hd)

namespace SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A continuous scalar composition has the energy bound given by its Lipschitz constant. -/
theorem exists_continuous_comp_energy_le_mul (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) {L : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith L φ) :
    ∃ (v : C(CarpetPoints, ℝ)) (hv : continuousLp p v ∈ E.domain),
      (∀ x, v x = φ (u x)) ∧
        (E.energy ⟨continuousLp p v, hv⟩ : ℝ) ≤
          (L : ℝ) ^ p * (E.energy ⟨continuousLp p u, hu⟩ : ℝ) := by
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let v : C(CarpetPoints, ℝ) := (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp u
  obtain ⟨g, hg, henergy⟩ := E.exists_energyMeasure_comp_le hφ f
  have heq : continuousLp p v = (g : CarpetLp p) := by
    apply Lp.ext
    exact (continuousLp_ae_eq p v).trans
      ((hg.trans ((continuousLp_ae_eq p u).mono (fun x hx ↦ congrArg φ hx))).symm)
  have hv : continuousLp p v ∈ E.domain := heq.symm ▸ g.property
  have hv' : (⟨continuousLp p v, hv⟩ : E.domain) = g := Subtype.ext heq
  refine ⟨v, hv, fun _ ↦ rfl, ?_⟩
  rw [hv']
  have hm := henergy (univ : Set CarpetPoints)
  rw [E.energyMeasure_univ, smul_apply, smul_eq_mul, E.energyMeasure_univ] at hm
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_rpow] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hm

private theorem exists_continuous_comp_energy_le (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) :
    ∃ (v : C(CarpetPoints, ℝ)) (hv : continuousLp p v ∈ E.domain),
      (∀ x, v x = φ (u x)) ∧ E.energy ⟨continuousLp p v, hv⟩ ≤ E.energy ⟨continuousLp p u, hu⟩ := by
  obtain ⟨v, hv, hφv, hve⟩ := E.exists_continuous_comp_energy_le_mul u hu hφ
  refine ⟨v, hv, hφv, ?_⟩
  simp only [NNReal.coe_one, Real.one_rpow, one_mul] at hve
  exact_mod_cast hve

private theorem exists_continuous_indicator_of_component
    (u : C(CarpetPoints, ℝ)) (hu : continuousLp p u ∈ E.domain) (hn : ∀ x, 0 ≤ u x)
    (a : CarpetPoints) :
    let U := connectedComponentIn {x | 0 < u x} a
    ∃ g : C(CarpetPoints, ℝ), ∃ hg : continuousLp p g ∈ E.domain,
      (g : CarpetPoints → ℝ) = U.indicator u ∧
      E.energy ⟨continuousLp p g, hg⟩ ≤ E.energy ⟨continuousLp p u, hu⟩ := by
  have hU : (⋃ x : ({a} : Set CarpetPoints), connectedComponentIn {x | 0 < u x} x.val) =
      connectedComponentIn {x | 0 < u x} a := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := mem_iUnion.mp hx
      rwa [show y.val = a from y.property] at hy
    · intro hx
      exact mem_iUnion.mpr ⟨⟨a, rfl⟩, hx⟩
  simpa only [hU] using E.exists_continuous_indicator_of_component_union u hu hn {a}

private theorem leftRightCapacity_le_of_topBottom
    (v : C(CarpetPoints, ℝ)) (hv : continuousLp p v ∈ E.domain)
    (hb : ∀ x ∈ carpetBottom, v x = 0) (ht : ∀ x ∈ carpetTop, v x = 1) :
    E.leftRightCapacity ≤ (E.energy ⟨continuousLp p v, hv⟩ : ℝ) := by
  let w : C(CarpetPoints, ℝ) := v.comp ⟨carpetSymmetry axisSwap, continuous_carpetSymmetry axisSwap⟩
  let f : E.domain := ⟨continuousLp p v, hv⟩
  obtain ⟨g, hLp, hEnergy⟩ := E.symmetry axisSwap f
  have hwg : continuousLp p w = (g : CarpetLp p) := by
    apply Lp.ext
    have h := (measurePreserving_carpetSymmetry axisSwap).quasiMeasurePreserving.ae_eq_comp
      (continuousLp_ae_eq p v)
    exact (continuousLp_ae_eq p w).trans ((hLp.trans h).symm)
  have hw : continuousLp p w ∈ E.domain := hwg.symm ▸ g.property
  have hgw : (⟨continuousLp p w, hw⟩ : E.domain) = g := Subtype.ext hwg
  rw [← hEnergy, ← hgw, E.leftRightCapacity_eq_sInf_prescribed_values]
  refine csInf_le ⟨0, ?_⟩ ⟨w, hw, ?_, ?_, rfl⟩
  · rintro _ ⟨u, hu, _, _, rfl⟩
    exact (E.energy ⟨continuousLp p u, hu⟩).property
  · intro x hx
    apply hb
    change (carpetSymmetry axisSwap x : Plane) 1 = 0
    rw [carpetSymmetry_axisSwap_second, hx]
  · intro x hx
    apply ht
    change (carpetSymmetry axisSwap x : Plane) 1 = 1
    rw [carpetSymmetry_axisSwap_second, hx]

private theorem lipschitzWith_one_sub : LipschitzWith 1 (fun t : ℝ ↦ 1 - t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [show 1 - x - (1 - y) = -(x - y) by ring, abs_neg]

/-- The opposite-side capacity is a lower bound when compact connected sets
carry the two prescribed levels and both meet the left and right sides. -/
theorem leftRightCapacity_le_of_crossing_sets
    (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain) {A Z : Set CarpetPoints}
    (hA : IsCompact A) (hZ : IsCompact Z) (hAc : IsPreconnected A) (hZc : IsPreconnected Z)
    {a₀ a₁ z₀ z₁ : CarpetPoints} (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A) (hz₀ : z₀ ∈ Z) (hz₁ : z₁ ∈ Z)
    (hal : (a₀ : Plane) 0 = 0) (har : (a₁ : Plane) 0 = 1)
    (hzl : (z₀ : Plane) 0 = 0) (hzr : (z₁ : Plane) 0 = 1)
    (hfa : ∀ x ∈ A, f x = 1) (hfz : ∀ x ∈ Z, f x = 0) :
    E.leftRightCapacity ≤ (E.energy ⟨continuousLp p f, hf⟩ : ℝ) := by
  let clamp (x : ℝ) := min (max x 0) 1
  have hclamp : LipschitzWith 1 clamp := (LipschitzWith.id.max_const (0 : ℝ)).min_const 1
  obtain ⟨u, hu, huv, hue⟩ := E.exists_continuous_comp_energy_le f hf hclamp
  have hu₀ (x : CarpetPoints) : 0 ≤ u x := (huv x).symm ▸ le_min (le_max_right _ _) zero_le_one
  have hu₁ (x : CarpetPoints) : u x ≤ 1 := (huv x).symm ▸ min_le_right _ _
  have hua (x : CarpetPoints) (hx : x ∈ A) : u x = 1 := by simp [huv, clamp, hfa x hx]
  have huz (x : CarpetPoints) (hx : x ∈ Z) : u x = 0 := by simp [huv, clamp, hfz x hx]
  let U := connectedComponentIn {x | 0 < u x} a₀
  have hAU : A ⊆ U := hAc.subset_connectedComponentIn ha₀ fun x hx ↦ by
    change 0 < u x
    rw [hua x hx]
    exact zero_lt_one
  have hUZ : Disjoint Z U := Set.disjoint_left.mpr fun x hx hxu ↦ by
    have hpos : 0 < u x := connectedComponentIn_subset _ _ hxu
    rw [huz x hx] at hpos
    exact lt_irrefl 0 hpos
  have hU : Disjoint carpetBottom U ∨ Disjoint carpetTop U := by
    by_contra! hh
    obtain ⟨b, hb, hbU⟩ := Set.not_disjoint_iff.mp hh.1
    obtain ⟨t, ht, htU⟩ := Set.not_disjoint_iff.mp hh.2
    exact not_disjoint_carpet_crossings hZ hZc isPreconnected_connectedComponentIn
      hz₀ hz₁ hbU htU hzl hzr hb ht hUZ
  obtain ⟨g, hg, hUg, hge⟩ := E.exists_continuous_indicator_of_component u hu hu₀ a₀
  have hga (x : CarpetPoints) (hx : x ∈ A) : g x = 1 := by
    have hh := congrFun hUg x
    rw [indicator_of_mem (hAU hx), hua x hx] at hh
    exact hh
  have hg_bounds (x : CarpetPoints) : 0 ≤ g x ∧ g x ≤ 1 := by
    have hh := congrFun hUg x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx] at hh
      exact hh.symm ▸ ⟨hu₀ x, hu₁ x⟩
    · rw [indicator_of_notMem hx] at hh
      exact hh.symm ▸ ⟨le_rfl, zero_le_one⟩
  obtain ⟨v, hv, hvg, hve⟩ := E.exists_continuous_comp_energy_le g hg lipschitzWith_one_sub
  have hv₀ (x : CarpetPoints) : 0 ≤ v x := by rw [hvg]; exact sub_nonneg.mpr (hg_bounds x).2
  have hva (x : CarpetPoints) (hx : x ∈ A) : v x = 0 := by rw [hvg, hga x hx, sub_self]
  have perform (S T : Set CarpetPoints) (hS : IsPreconnected S) (hSn : S.Nonempty)
      (hcase : S = carpetBottom ∧ T = carpetTop ∨ S = carpetTop ∧ T = carpetBottom)
      (hSU : Disjoint S U) :
      ∃ (w : C(CarpetPoints, ℝ)) (hw : continuousLp p w ∈ E.domain),
        (∀ x ∈ S, w x = 1) ∧ (∀ x ∈ T, w x = 0) ∧
        E.energy ⟨continuousLp p w, hw⟩ ≤ E.energy ⟨continuousLp p v, hv⟩ := by
    have hvS (x : CarpetPoints) (hx : x ∈ S) : v x = 1 := by
      have hh := congrFun hUg x
      rw [indicator_of_notMem (Set.disjoint_left.mp hSU hx)] at hh
      rw [hvg, hh, sub_zero]
    obtain ⟨b, hb⟩ := hSn
    let V := connectedComponentIn {x | 0 < v x} b
    have hSV : S ⊆ V := hS.subset_connectedComponentIn hb fun x hx ↦ by
      change 0 < v x
      rw [hvS x hx]
      exact zero_lt_one
    have hAV : Disjoint A V := Set.disjoint_left.mpr fun x hx hV ↦ by
      have hh : 0 < v x := connectedComponentIn_subset _ _ hV
      rw [hva x hx] at hh
      exact lt_irrefl 0 hh
    have hTV : Disjoint T V := by
      by_contra h
      obtain ⟨t, ht, htV⟩ := Set.not_disjoint_iff.mp h
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact not_disjoint_carpet_crossings hA hAc isPreconnected_connectedComponentIn
          ha₀ ha₁ (hSV hb) htV hal har hb ht hAV
      · exact not_disjoint_carpet_crossings hA hAc isPreconnected_connectedComponentIn
          ha₀ ha₁ htV (hSV hb) hal har ht hb hAV
    obtain ⟨w, hw, hwV, hwe⟩ := E.exists_continuous_indicator_of_component v hv hv₀ b
    refine ⟨w, hw, ?_, ?_, hwe⟩
    · intro x hx
      have hh := congrFun hwV x
      rwa [indicator_of_mem (hSV hx), hvS x hx] at hh
    · intro x hx
      have hh := congrFun hwV x
      rwa [indicator_of_notMem (Set.disjoint_left.mp hTV hx)] at hh
  have hcap : E.leftRightCapacity ≤ (E.energy ⟨continuousLp p v, hv⟩ : ℝ) := by
    rcases hU with hU | hU
    · obtain ⟨w, hw, hwb, hwt, hwe⟩ := perform carpetBottom carpetTop isPreconnected_carpetBottom
        carpetBottom_nonempty (Or.inl ⟨rfl, rfl⟩) hU
      obtain ⟨q, hq, hqw, hqe⟩ := E.exists_continuous_comp_energy_le w hw lipschitzWith_one_sub
      exact (E.leftRightCapacity_le_of_topBottom q hq
        (fun x hx ↦ by rw [hqw, hwb x hx, sub_self])
        (fun x hx ↦ by rw [hqw, hwt x hx, sub_zero])).trans
        (by exact_mod_cast hqe.trans hwe)
    · obtain ⟨w, hw, hwt, hwb, hwe⟩ := perform carpetTop carpetBottom isPreconnected_carpetTop
        carpetTop_nonempty (Or.inr ⟨rfl, rfl⟩) hU
      exact (E.leftRightCapacity_le_of_topBottom w hw hwb hwt).trans (by exact_mod_cast hwe)
  exact hcap.trans (by exact_mod_cast hve.trans (hge.trans hue))

/-- Lemma 3.10. Two left-to-right paths carrying levels one and zero
give the opposite-side capacity lower bound. -/
theorem leftRightCapacity_le_of_crossing_paths
    (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain) (γ η : C(I, CarpetPoints))
    (hγ₀ : (γ 0 : Plane) 0 = 0) (hγ₁ : (γ 1 : Plane) 0 = 1)
    (hη₀ : (η 0 : Plane) 0 = 0) (hη₁ : (η 1 : Plane) 0 = 1)
    (hγ : ∀ t, f (γ t) = 1) (hη : ∀ t, f (η t) = 0) :
    E.leftRightCapacity ≤ (E.energy ⟨continuousLp p f, hf⟩ : ℝ) := by
  exact E.leftRightCapacity_le_of_crossing_sets f hf
    (isCompact_range γ.continuous) (isCompact_range η.continuous)
    (isPreconnected_range γ.continuous) (isPreconnected_range η.continuous)
    (mem_range_self _) (mem_range_self _) (mem_range_self _) (mem_range_self _)
    hγ₀ hγ₁ hη₀ hη₁ (by rintro _ ⟨t, rfl⟩; exact hγ t)
    (by rintro _ ⟨t, rfl⟩; exact hη t)

end SelfSimilarPEnergy
end CarpetEnergy
