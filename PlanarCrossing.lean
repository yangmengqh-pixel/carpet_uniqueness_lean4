import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Covering.FundamentalGroupCircle

/-!
# Planar crossing

The sign conditions on the four sides of a square force a continuous map to
vanish. Otherwise normalization and radial contraction would make the
identity of the circle nullhomotopic.
-/

open Set
open scoped ContinuousMap unitInterval

namespace CarpetEnergy

private theorem circle_not_contractible : ¬ ContractibleSpace Circle := by
  intro h
  let : ContractibleSpace Circle := h
  let T := 2 * Real.pi
  have hT : 0 < T := mul_pos (by norm_num) Real.pi_pos
  let : Fact (0 < T) := ⟨hT⟩
  let : ContractibleSpace (AddCircle T) := (AddCircle.homeomorphCircle hT.ne').contractibleSpace
  let e := AddCircle.windingNumberIso (0 : AddCircle T)
  have he : e.symm (Multiplicative.ofAdd (0 : ℤ)) = e.symm (Multiplicative.ofAdd (1 : ℤ)) :=
    Subsingleton.elim _ _
  exact zero_ne_one (Multiplicative.ofAdd.injective (e.symm.injective he))

private def centeredSquare : Set ℂ := {z | |z.re| ≤ 1 ∧ |z.im| ≤ 1}

private noncomputable def circleNormalize (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)])⟩

private theorem continuous_circleNormalize {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} (hf : Continuous f) (hn : ∀ x, f x ≠ 0) :
    Continuous (fun x ↦ circleNormalize (f x) (hn x)) := by
  apply Continuous.subtype_mk
  exact (hf.norm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr (hn x))).smul hf

private noncomputable def circleMax (z : Circle) : ℝ :=
  max |(z : ℂ).re| |(z : ℂ).im|

private theorem circleMax_pos (z : Circle) : 0 < circleMax z := by
  have hn : (z : ℂ) ≠ 0 := z.coe_ne_zero
  by_contra! h
  have hre : |(z : ℂ).re| ≤ 0 := (le_max_left _ _).trans h
  have him : |(z : ℂ).im| ≤ 0 := (le_max_right _ _).trans h
  exact hn (Complex.ext (by simpa only [Complex.zero_re, abs_nonpos_iff] using hre)
    (by simpa only [Complex.zero_im, abs_nonpos_iff] using him))

private theorem radial_abs_le (z : Circle) (r : I) {a : ℝ} (ha : |a| ≤ circleMax z) :
    |(r : ℝ) * (circleMax z)⁻¹ * a| ≤ 1 := by
  have hm := circleMax_pos z
  rw [mul_assoc, abs_mul, abs_mul, abs_of_nonneg r.property.1,
    abs_of_nonneg (inv_nonneg.mpr hm.le)]
  calc
    (r : ℝ) * ((circleMax z)⁻¹ * |a|) ≤ (r : ℝ) * ((circleMax z)⁻¹ * circleMax z) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hm.le)) r.property.1
    _ ≤ 1 := by rw [inv_mul_cancel₀ hm.ne', mul_one]; exact r.property.2

private noncomputable def squareRadial (r : I) (z : Circle) : centeredSquare :=
  ⟨((r : ℝ) * (circleMax z)⁻¹) • (z : ℂ), by
    change |(_ • (z : ℂ)).re| ≤ 1 ∧ |(_ • (z : ℂ)).im| ≤ 1
    rw [Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_eq_mul]
    exact ⟨radial_abs_le z r (le_max_left _ _), radial_abs_le z r (le_max_right _ _)⟩⟩

private theorem continuous_squareRadial : Continuous (fun rz : I × Circle ↦ squareRadial rz.1 rz.2) := by
  have hm : Continuous circleMax := by
    unfold circleMax
    fun_prop
  have hi := (hm.comp continuous_snd).inv₀ (fun rz : I × Circle ↦ (circleMax_pos rz.2).ne')
  apply Continuous.subtype_mk
  exact ((continuous_subtypeVal.comp continuous_fst).mul hi).smul
    (continuous_subtypeVal.comp continuous_snd)

private theorem radial_face_eq {x d : ℝ} (hd : 0 < d) (hx : |x| = d) :
    (0 < x → d⁻¹ * x = 1) ∧ (x < 0 → d⁻¹ * x = -1) := by
  constructor
  · intro h
    rw [abs_of_pos h] at hx
    rw [hx, inv_mul_cancel₀ hd.ne']
  · intro h
    rw [abs_of_neg h] at hx
    rw [show x = -d by linarith, mul_neg, inv_mul_cancel₀ hd.ne']

private theorem blend_face_ne_zero {a b d : ℝ} (hd : 0 < d) (hb : |b| = d)
    (hpos : d⁻¹ * b = 1 → 0 ≤ a) (hneg : d⁻¹ * b = -1 → a ≤ 0)
    {r : I} (hr : 0 < (r : ℝ)) : (1 - (r : ℝ)) * a + (r : ℝ) * b ≠ 0 := by
  have hfaces := radial_face_eq hd hb
  have hb₀ : b ≠ 0 := by rintro rfl; simp at hb; exact hd.ne' hb.symm
  rcases lt_or_gt_of_ne hb₀ with hb_neg | hb_pos
  · exact (add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr r.property.2) (hneg (hfaces.2 hb_neg)))
      (mul_neg_of_pos_of_neg hr hb_neg)).ne
  · exact (add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr r.property.2) (hpos (hfaces.1 hb_pos)))
      (mul_pos hr hb_pos)).ne'

/-- A continuous complex-valued map on the square with outward signs on
its four faces has a zero. -/
private theorem exists_zero_of_square_face_sign (F : C(centeredSquare, ℂ))
    (hre₁ : ∀ z : centeredSquare, z.val.re = 1 → 0 ≤ (F z).re)
    (hre₀ : ∀ z : centeredSquare, z.val.re = -1 → (F z).re ≤ 0)
    (him₁ : ∀ z : centeredSquare, z.val.im = 1 → 0 ≤ (F z).im)
    (him₀ : ∀ z : centeredSquare, z.val.im = -1 → (F z).im ≤ 0) :
    ∃ z, F z = 0 := by
  by_contra! hn
  let A : C(centeredSquare, Circle) :=
    ⟨fun z ↦ circleNormalize (F z) (hn z), continuous_circleNormalize F.continuous hn⟩
  let G : C(Circle, Circle) :=
    ⟨fun z ↦ A (squareRadial 1 z), A.continuous.comp (continuous_squareRadial.comp
      (continuous_const.prodMk continuous_id))⟩
  let center : centeredSquare := ⟨0, by norm_num [centeredSquare]⟩
  have hG : G.Nullhomotopic := by
    refine ⟨A center, ⟨?_⟩⟩
    apply ContinuousMap.Homotopy.symm
    refine ⟨⟨fun rz ↦ A (squareRadial rz.1 rz.2), A.continuous.comp continuous_squareRadial⟩,
      ?_, fun _ ↦ rfl⟩
    intro z
    change A (squareRadial 0 z) = A center
    congr 1
    apply Subtype.ext
    simp [squareRadial, center]
  let B (rz : I × Circle) : ℂ :=
    (1 - (rz.1 : ℝ)) • F (squareRadial 1 rz.2) + (rz.1 : ℝ) • (rz.2 : ℂ)
  have hB : Continuous B := by
    unfold B
    have hrad : Continuous (fun rz : I × Circle ↦ squareRadial 1 rz.2) :=
      continuous_squareRadial.comp (continuous_const.prodMk continuous_snd)
    fun_prop
  have hB₀ (z : Circle) : B (0, z) = F (squareRadial 1 z) := by simp [B]
  have hB₁ (z : Circle) : B (1, z) = (z : ℂ) := by simp [B]
  have hB_ne (rz : I × Circle) : B rz ≠ 0 := by
    obtain ⟨r, z⟩ := rz
    rcases eq_or_ne r 0 with rfl | hr
    · rw [hB₀]
      exact hn _
    have hr_pos : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1 (fun h ↦ hr (Subtype.ext h.symm))
    let q := squareRadial 1 z
    have hqr : q.val.re = (circleMax z)⁻¹ * (z : ℂ).re := by
      simp [q, squareRadial]
    have hqi : q.val.im = (circleMax z)⁻¹ * (z : ℂ).im := by
      simp [q, squareRadial]
    rcases le_total |(z : ℂ).re| |(z : ℂ).im| with h | h
    · have hb : |(z : ℂ).im| = circleMax z := (max_eq_right h).symm
      have hh := blend_face_ne_zero (circleMax_pos z) hb
        (fun h ↦ him₁ q (hqi.trans h)) (fun h ↦ him₀ q (hqi.trans h)) hr_pos
      intro he
      apply hh
      simpa only [B, Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im] using
        congrArg Complex.im he
    · have hb : |(z : ℂ).re| = circleMax z := (max_eq_left h).symm
      have hh := blend_face_ne_zero (circleMax_pos z) hb
        (fun h ↦ hre₁ q (hqr.trans h)) (fun h ↦ hre₀ q (hqr.trans h)) hr_pos
      intro he
      apply hh
      simpa only [B, Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re] using
        congrArg Complex.re he
  have hId : G.Homotopic (ContinuousMap.id Circle) := by
    refine ⟨⟨⟨fun rz ↦ circleNormalize (B rz) (hB_ne rz), continuous_circleNormalize hB hB_ne⟩,
      ?_, ?_⟩⟩
    · intro z
      apply Circle.ext
      change ‖B (0, z)‖⁻¹ • B (0, z) = ‖F (squareRadial 1 z)‖⁻¹ • F (squareRadial 1 z)
      rw [hB₀]
    · intro z
      apply Circle.ext
      change ‖B (1, z)‖⁻¹ • B (1, z) = z.val
      rw [hB₁, Circle.norm_coe, inv_one, one_smul]
  obtain ⟨c, hc⟩ := hG
  exact circle_not_contractible ((contractible_iff_id_nullhomotopic Circle).2
    ⟨c, hId.symm.trans hc⟩)

private noncomputable def squareParameter (x : ℝ) (hx : |x| ≤ 1) : I :=
  ⟨(x + 1) / 2, by obtain ⟨hl, hu⟩ := abs_le.mp hx; constructor <;> linarith⟩

/-- Continuous paths through opposite pairs of faces of the unit square intersect. -/
theorem exists_intersection_of_axis_crossings (γ η : C(I, ℂ))
    (hγ : ∀ t, (γ t).re ∈ Icc (0 : ℝ) 1 ∧ (γ t).im ∈ Icc (0 : ℝ) 1)
    (hη : ∀ t, (η t).re ∈ Icc (0 : ℝ) 1 ∧ (η t).im ∈ Icc (0 : ℝ) 1)
    (hγ₀ : (γ 0).re = 0) (hγ₁ : (γ 1).re = 1)
    (hη₀ : (η 0).im = 0) (hη₁ : (η 1).im = 1) :
    ∃ s t, γ s = η t := by
  let s (z : centeredSquare) := squareParameter z.val.re z.property.1
  let t (z : centeredSquare) := squareParameter z.val.im z.property.2
  have hs : Continuous s := by
    apply Continuous.subtype_mk
    change Continuous (fun z : centeredSquare ↦ (z.val.re + 1) / 2)
    fun_prop
  have ht : Continuous t := by
    apply Continuous.subtype_mk
    change Continuous (fun z : centeredSquare ↦ (z.val.im + 1) / 2)
    fun_prop
  let F : C(centeredSquare, ℂ) :=
    ⟨fun z ↦ (starRingEnd ℂ) (γ (s z) - η (t z)), by fun_prop⟩
  have hs₀ (z : centeredSquare) (h : z.val.re = -1) : s z = 0 := by
    apply Subtype.ext
    change (z.val.re + 1) / 2 = 0
    rw [h]
    norm_num
  have hs₁ (z : centeredSquare) (h : z.val.re = 1) : s z = 1 := by
    apply Subtype.ext
    change (z.val.re + 1) / 2 = 1
    rw [h]
    norm_num
  have ht₀ (z : centeredSquare) (h : z.val.im = -1) : t z = 0 := by
    apply Subtype.ext
    change (z.val.im + 1) / 2 = 0
    rw [h]
    norm_num
  have ht₁ (z : centeredSquare) (h : z.val.im = 1) : t z = 1 := by
    apply Subtype.ext
    change (z.val.im + 1) / 2 = 1
    rw [h]
    norm_num
  have hFr (z : centeredSquare) : (F z).re = (γ (s z)).re - (η (t z)).re := by
    simp [F]
  have hFi (z : centeredSquare) : (F z).im = (η (t z)).im - (γ (s z)).im := by
    simp [F]
    ring
  obtain ⟨z, hz⟩ := exists_zero_of_square_face_sign F
    (fun z h ↦ by rw [hFr, hs₁ z h, hγ₁]; exact sub_nonneg.mpr (hη (t z)).1.2)
    (fun z h ↦ by rw [hFr, hs₀ z h, hγ₀]; exact sub_nonpos.mpr (hη (t z)).1.1)
    (fun z h ↦ by rw [hFi, ht₁ z h, hη₁]; exact sub_nonneg.mpr (hγ (s z)).2.2)
    (fun z h ↦ by rw [hFi, ht₀ z h, hη₀]; exact sub_nonpos.mpr (hγ (s z)).2.1)
  refine ⟨s z, t z, Complex.ext ?_ ?_⟩
  · exact sub_eq_zero.mp (by simpa only [hFr, Complex.zero_re] using congrArg Complex.re hz)
  · exact (sub_eq_zero.mp
      (by simpa only [hFi, Complex.zero_im] using congrArg Complex.im hz)).symm

private theorem exists_path_in_open_of_isPreconnected {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {U A : Set X} (hU : IsOpen U) (hA : IsPreconnected A)
    (hAU : A ⊆ U) {a b : X} (ha : a ∈ A) (hb : b ∈ A) :
    ∃ γ : Path a b, ∀ t, γ t ∈ U := by
  have hC := isConnected_connectedComponentIn_iff.mpr (hAU ha)
  have hC_path := ((hU.connectedComponentIn (x := a)).isConnected_iff_isPathConnected).mp hC
  obtain ⟨γ, hγ⟩ := hC_path.joinedIn a (mem_connectedComponentIn (hAU ha)) b
    (hA.subset_connectedComponentIn ha hAU hb)
  exact ⟨γ, fun t ↦ connectedComponentIn_subset U a (hγ t)⟩

private def coordinateComplex (z : I × I) : ℂ := ⟨z.1, z.2⟩

private theorem continuous_coordinateComplex : Continuous coordinateComplex := by
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_subtypeVal.comp continuous_fst).prodMk
      (continuous_subtypeVal.comp continuous_snd))

private theorem coordinateComplex_injective : Function.Injective coordinateComplex := by
  intro a b h
  exact Prod.ext (Subtype.ext (congrArg Complex.re h)) (Subtype.ext (congrArg Complex.im h))

/-- A compact connected left-to-right set and a connected bottom-to-top set
in the unit square have a common point. -/
theorem not_disjoint_of_connected_axis_crossings {A B : Set (I × I)}
    (hA : IsCompact A) (hAc : IsPreconnected A) (hBc : IsPreconnected B)
    {a₀ a₁ b₀ b₁ : I × I} (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A) (hb₀ : b₀ ∈ B) (hb₁ : b₁ ∈ B)
    (hleft : a₀.1 = 0) (hright : a₁.1 = 1) (hbottom : b₀.2 = 0) (htop : b₁.2 = 1) :
    ¬ Disjoint A B := by
  intro hd
  have : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have hBA : B ⊆ Aᶜ := fun _ hb ha ↦ Set.disjoint_left.mp hd ha hb
  obtain ⟨η, hη⟩ := exists_path_in_open_of_isPreconnected hA.isClosed.isOpen_compl hBc hBA hb₀ hb₁
  have hηc : IsCompact (range η) := isCompact_range η.continuous
  have hAη : A ⊆ (range η)ᶜ := by
    rintro a ha ⟨t, rfl⟩
    exact hη t ha
  obtain ⟨γ, hγ⟩ := exists_path_in_open_of_isPreconnected hηc.isClosed.isOpen_compl hAc hAη ha₀ ha₁
  let γ' : C(I, ℂ) := ⟨coordinateComplex ∘ γ, continuous_coordinateComplex.comp γ.continuous⟩
  let η' : C(I, ℂ) := ⟨coordinateComplex ∘ η, continuous_coordinateComplex.comp η.continuous⟩
  obtain ⟨s, t, hst⟩ := exists_intersection_of_axis_crossings γ' η'
    (fun t ↦ ⟨(γ t).1.property, (γ t).2.property⟩)
    (fun t ↦ ⟨(η t).1.property, (η t).2.property⟩)
    (by change ((γ 0).1 : ℝ) = 0; rw [γ.source, hleft]; rfl)
    (by change ((γ 1).1 : ℝ) = 1; rw [γ.target, hright]; rfl)
    (by change ((η 0).2 : ℝ) = 0; rw [η.source, hbottom]; rfl)
    (by change ((η 1).2 : ℝ) = 1; rw [η.target, htop]; rfl)
  exact hγ s ⟨t, coordinateComplex_injective hst |>.symm⟩

end CarpetEnergy
