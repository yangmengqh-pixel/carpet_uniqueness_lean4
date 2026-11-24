import CarpetCorners
import EnergyAdjacentCells
import EnergyComponentProfile

/-!
# Corner interpolation in a component kernel

A left-to-right kernel profile is averaged with its vertical reflection.
Together with its transpose it interpolates four corner values in a way
that agrees on all same-level cell overlaps.
-/

open Function Set

namespace CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent

variable {p : ℝ} {E : SelfSimilarPEnergy p} (Q : E.SelfSimilarComponent)

/-- A left-to-right kernel profile whose two horizontal traces agree. -/
structure CornerProfile where
  toContinuousMap : C(CarpetPoints, ℝ)
  mem_kernel : toContinuousMap ∈ Q.continuousKernel
  bounds : ∀ x, 0 ≤ toContinuousMap x ∧ toContinuousMap x ≤ 1
  side : ∀ (a : Fin 2) (x : CarpetPoints), (x : Plane) 0 = (a.val : ℝ) →
    toContinuousMap x = (a.val : ℝ)
  flip : ∀ x, toContinuousMap (carpetSymmetry verticalFlip x) = toContinuousMap x

theorem exists_cornerProfile_of_sides {h : C(CarpetPoints, ℝ)}
    (hh : h ∈ Q.continuousKernel)
    (hL : ∀ x : CarpetPoints, (x : Plane) 0 = 0 → h x = 0)
    (hR : ∀ x : CarpetPoints, (x : Plane) 0 = 1 → h x = 1) :
    Nonempty Q.CornerProfile := by
  let φ (t : ℝ) := min (max t 0) 1
  have hφ : LipschitzWith 1 φ := (LipschitzWith.id.max_const (0 : ℝ)).min_const 1
  let u := (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp h
  have hu : u ∈ Q.continuousKernel := Q.continuousKernel_comp hh hφ
  have hub (x : CarpetPoints) : 0 ≤ u x ∧ u x ≤ 1 :=
    ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  have hs (a : Fin 2) (x : CarpetPoints) (hx : (x : Plane) 0 = (a.val : ℝ)) :
      u x = (a.val : ℝ) := by
    fin_cases a
    · change min (max (h x) 0) 1 = 0
      rw [hL x hx, max_self, min_eq_left zero_le_one]
    · change min (max (h x) 0) 1 = 1
      rw [hR x hx, max_eq_left zero_le_one, min_self]
  let vf : C(CarpetPoints, CarpetPoints) := ⟨carpetSymmetry verticalFlip,
    continuous_carpetSymmetry verticalFlip⟩
  let g := (1 / 2 : ℝ) • (u + u.comp vf)
  have hflipFirst (x : CarpetPoints) : (carpetSymmetry verticalFlip x : Plane) 0 = (x : Plane) 0 := rfl
  have hiv (x : CarpetPoints) : carpetSymmetry verticalFlip (carpetSymmetry verticalFlip x) = x := by
    exact carpetSymmetry_leftInverse verticalFlip x
  refine ⟨⟨g, Q.continuousKernel_smul _ (Q.continuousKernel_add hu
    (Q.continuousKernel_comp_symmetry hu verticalFlip)), ?_, ?_, ?_⟩⟩
  · intro x
    change 0 ≤ (1 / 2 : ℝ) * (u x + u (vf x)) ∧ (1 / 2 : ℝ) * (u x + u (vf x)) ≤ 1
    exact ⟨by linarith [(hub x).1, (hub (vf x)).1], by linarith [(hub x).2, (hub (vf x)).2]⟩
  · intro a x hx
    change (1 / 2 : ℝ) * (u x + u (carpetSymmetry verticalFlip x)) = _
    rw [hs a x hx, hs a _ ((hflipFirst x).trans hx)]
    ring
  · intro x
    change (1 / 2 : ℝ) * (u (carpetSymmetry verticalFlip x) +
      u (carpetSymmetry verticalFlip (carpetSymmetry verticalFlip x))) =
      (1 / 2 : ℝ) * (u x + u (carpetSymmetry verticalFlip x))
    rw [hiv, add_comm]

namespace CornerProfile

variable {Q} (P : Q.CornerProfile)

/-- The vertical transpose of the profile. -/
noncomputable def vertical : C(CarpetPoints, ℝ) :=
  P.toContinuousMap.comp ⟨carpetSymmetry axisSwap, continuous_carpetSymmetry axisSwap⟩

theorem vertical_mem_kernel : P.vertical ∈ Q.continuousKernel :=
  Q.continuousKernel_comp_symmetry P.mem_kernel axisSwap

theorem vertical_bounds (x : CarpetPoints) : 0 ≤ P.vertical x ∧ P.vertical x ≤ 1 := P.bounds _

theorem vertical_side (a : Fin 2) (x : CarpetPoints) (hx : (x : Plane) 1 = (a.val : ℝ)) :
    P.vertical x = (a.val : ℝ) := P.side a _ hx

theorem vertical_flip (x : CarpetPoints) :
    P.vertical (carpetSymmetry horizontalFlip x) = P.vertical x := by
  have he : carpetSymmetry axisSwap (carpetSymmetry horizontalFlip x) =
      carpetSymmetry verticalFlip (carpetSymmetry axisSwap x) := by
    apply Subtype.ext
    ext j
    fin_cases j <;> rfl
  change P.toContinuousMap (carpetSymmetry axisSwap (carpetSymmetry horizontalFlip x)) =
    P.toContinuousMap (carpetSymmetry axisSwap x)
  rw [he, P.flip]

private noncomputable def lerpMap (g : C(CarpetPoints, ℝ)) (a b : ℝ) : C(CarpetPoints, ℝ) :=
  ContinuousMap.const CarpetPoints a + (b - a) • g

private theorem lerpMap_apply (g : C(CarpetPoints, ℝ)) (a b : ℝ) (x : CarpetPoints) :
    lerpMap g a b x = (1 - g x) * a + g x * b := by
  change a + (b - a) * g x = _
  ring

private theorem lerpMap_mem_kernel {g : C(CarpetPoints, ℝ)} (hg : g ∈ Q.continuousKernel) (a b : ℝ) :
    lerpMap g a b ∈ Q.continuousKernel :=
  Q.continuousKernel_add (Q.continuousKernel_const a) (Q.continuousKernel_smul _ hg)

private noncomputable def oneMap : C(CarpetPoints, ℝ) := ContinuousMap.const CarpetPoints 1

/-- Interpolate four corner values using the two profiles. -/
noncomputable def interpolate (a : Fin 2 → Fin 2 → ℝ) : C(CarpetPoints, ℝ) :=
  (oneMap - P.toContinuousMap) * lerpMap P.vertical (a 0 0) (a 0 1) +
    P.toContinuousMap * lerpMap P.vertical (a 1 0) (a 1 1)

theorem interpolate_mem_kernel (a : Fin 2 → Fin 2 → ℝ) :
    P.interpolate a ∈ Q.continuousKernel :=
  Q.continuousKernel_add
    (Q.continuousKernel_mul (Q.continuousKernel_sub (Q.continuousKernel_const 1) P.mem_kernel)
      (lerpMap_mem_kernel P.vertical_mem_kernel _ _))
    (Q.continuousKernel_mul P.mem_kernel (lerpMap_mem_kernel P.vertical_mem_kernel _ _))

theorem interpolate_apply (a : Fin 2 → Fin 2 → ℝ) (x : CarpetPoints) :
    P.interpolate a x =
      (1 - P.toContinuousMap x) * ((1 - P.vertical x) * a 0 0 + P.vertical x * a 0 1) +
        P.toContinuousMap x * ((1 - P.vertical x) * a 1 0 + P.vertical x * a 1 1) := by
  change (1 - P.toContinuousMap x) * lerpMap P.vertical (a 0 0) (a 0 1) x +
    P.toContinuousMap x * lerpMap P.vertical (a 1 0) (a 1 1) x = _
  rw [lerpMap_apply, lerpMap_apply]

theorem interpolate_vertical_side (a : Fin 2 → Fin 2 → ℝ) (i : Fin 2) (x : CarpetPoints)
    (hi : (x : Plane) 0 = (i.val : ℝ)) :
    P.interpolate a x = (1 - P.vertical x) * a i 0 + P.vertical x * a i 1 := by
  rw [P.interpolate_apply, P.side i x hi]
  fin_cases i <;> norm_num

theorem interpolate_horizontal_side (a : Fin 2 → Fin 2 → ℝ) (j : Fin 2) (x : CarpetPoints)
    (hj : (x : Plane) 1 = (j.val : ℝ)) :
    P.interpolate a x = (1 - P.toContinuousMap x) * a 0 j + P.toContinuousMap x * a 1 j := by
  rw [P.interpolate_apply, P.vertical_side j x hj]
  fin_cases j <;> norm_num

theorem interpolate_corner (a : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    P.interpolate a (cornerPoint i j) = a i j := by
  rw [P.interpolate_vertical_side a i _ (cornerPoint_first i j),
    P.vertical_side j _ (cornerPoint_second i j)]
  fin_cases j <;> norm_num

private theorem abs_lerp_sub_le {s a b c R : ℝ} (hs : 0 ≤ s ∧ s ≤ 1)
    (ha : |a - c| ≤ R) (hb : |b - c| ≤ R) :
    |(1 - s) * a + s * b - c| ≤ R := by
  have ht : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  calc
    _ = |(1 - s) * (a - c) + s * (b - c)| := by congr 1; ring
    _ ≤ |(1 - s) * (a - c)| + |s * (b - c)| := abs_add_le _ _
    _ ≤ (1 - s) * R + s * R := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg hs.1]
      exact add_le_add (mul_le_mul_of_nonneg_left ha ht) (mul_le_mul_of_nonneg_left hb hs.1)
    _ = R := by ring

theorem abs_interpolate_sub_le (a : Fin 2 → Fin 2 → ℝ) (x : CarpetPoints)
    {c R : ℝ} (h : ∀ i j, |a i j - c| ≤ R) :
    |P.interpolate a x - c| ≤ R := by
  rw [P.interpolate_apply]
  exact abs_lerp_sub_le (P.bounds x)
    (abs_lerp_sub_le (P.vertical_bounds x) (h 0 0) (h 0 1))
    (abs_lerp_sub_le (P.vertical_bounds x) (h 1 0) (h 1 1))

private theorem eq_horizontalFlip_of_opposite_endpoints {x y : CarpetPoints} {i j : Fin 2}
    (hx : (x : Plane) 0 = (i.val : ℝ)) (hy : (y : Plane) 0 = (j.val : ℝ)) (hij : i ≠ j)
    (h : (x : Plane) 1 = (y : Plane) 1) :
    y = carpetSymmetry horizontalFlip x := by
  apply Subtype.ext
  ext k
  fin_cases k
  · change (y : Plane) 0 = (carpetSymmetry horizontalFlip x : Plane) 0
    rw [carpetSymmetry_horizontalFlip_first, hx, hy]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | norm_num
  · exact h.symm

private theorem eq_verticalFlip_of_opposite_endpoints {x y : CarpetPoints} {i j : Fin 2}
    (hx : (x : Plane) 1 = (i.val : ℝ)) (hy : (y : Plane) 1 = (j.val : ℝ)) (hij : i ≠ j)
    (h : (x : Plane) 0 = (y : Plane) 0) :
    y = carpetSymmetry verticalFlip x := by
  apply Subtype.ext
  ext k
  fin_cases k
  · exact h.symm
  · change (y : Plane) 1 = (carpetSymmetry verticalFlip x : Plane) 1
    rw [carpetSymmetry_verticalFlip_second, hx, hy]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | norm_num

/-- The values prescribed at the four corners of a word cell. -/
noncomputable def cornerData (b : CarpetPoints → ℝ) (w : List (Fin 8)) (i j : Fin 2) : ℝ :=
  b (wordMap w (cornerPoint i j))

private theorem interpolate_agree_on_overlap (b : CarpetPoints → ℝ) {w v : List (Fin 8)}
    (hlen : w.length = v.length) {x y : CarpetPoints} (hxy : wordMap w x = wordMap v y) :
    P.interpolate (cornerData b w) x = P.interpolate (cornerData b v) y := by
  have he := (wordMap_eq_iff_grid_coordinate hlen x y).mp hxy
  by_cases h₀ : gridCoordinate w 0 = gridCoordinate v 0
  · have hcoord₀ : (x : Plane) 0 = (y : Plane) 0 := by
      have h := he 0
      rw [h₀] at h
      exact add_left_cancel h
    by_cases h₁ : gridCoordinate w 1 = gridCoordinate v 1
    · have hwv : w = v := gridCoordinate_injective_of_length hlen (fun j ↦ by
        fin_cases j
        · exact h₀
        · exact h₁)
      subst v
      rw [(measurableEmbedding_wordMap w).injective hxy]
    · obtain ⟨j, l, hx, hy, hjl⟩ := overlap_coord_endpoints
        (carpet_coord_mem_Icc x 1) (carpet_coord_mem_Icc y 1) (he 1) h₁
      have hv := eq_verticalFlip_of_opposite_endpoints hx hy hjl hcoord₀
      have hf : P.toContinuousMap x = P.toContinuousMap y := by rw [hv, P.flip]
      have hm (i : Fin 2) : cornerData b w i j = cornerData b v i l := by
        apply congrArg b
        apply (wordMap_eq_iff_grid_coordinate hlen _ _).mpr
        intro k
        fin_cases k
        · change (gridCoordinate w 0 : ℝ) + (cornerPoint i j : Plane) 0 =
            (gridCoordinate v 0 : ℝ) + (cornerPoint i l : Plane) 0
          rw [cornerPoint_first, cornerPoint_first, h₀]
        · change (gridCoordinate w 1 : ℝ) + (cornerPoint i j : Plane) 1 =
            (gridCoordinate v 1 : ℝ) + (cornerPoint i l : Plane) 1
          rw [cornerPoint_second, cornerPoint_second, ← hx, ← hy]
          exact he 1
      rw [P.interpolate_horizontal_side _ j x hx, P.interpolate_horizontal_side _ l y hy, hf, hm 0, hm 1]
  · obtain ⟨i, k, hx, hy, hik⟩ := overlap_coord_endpoints
      (carpet_coord_mem_Icc x 0) (carpet_coord_mem_Icc y 0) (he 0) h₀
    by_cases h₁ : gridCoordinate w 1 = gridCoordinate v 1
    · have hcoord₁ : (x : Plane) 1 = (y : Plane) 1 := by
        have h := he 1
        rw [h₁] at h
        exact add_left_cancel h
      have hv := eq_horizontalFlip_of_opposite_endpoints hx hy hik hcoord₁
      have hg : P.vertical x = P.vertical y := by rw [hv, P.vertical_flip]
      have hm (j : Fin 2) : cornerData b w i j = cornerData b v k j := by
        apply congrArg b
        apply (wordMap_eq_iff_grid_coordinate hlen _ _).mpr
        intro a
        fin_cases a
        · change (gridCoordinate w 0 : ℝ) + (cornerPoint i j : Plane) 0 =
            (gridCoordinate v 0 : ℝ) + (cornerPoint k j : Plane) 0
          rw [cornerPoint_first, cornerPoint_first, ← hx, ← hy]
          exact he 0
        · change (gridCoordinate w 1 : ℝ) + (cornerPoint i j : Plane) 1 =
            (gridCoordinate v 1 : ℝ) + (cornerPoint k j : Plane) 1
          rw [cornerPoint_second, cornerPoint_second, h₁]
      rw [P.interpolate_vertical_side _ i x hx, P.interpolate_vertical_side _ k y hy,
        hg, hm 0, hm 1]
    · obtain ⟨j, l, hx', hy', _⟩ := overlap_coord_endpoints
        (carpet_coord_mem_Icc x 1) (carpet_coord_mem_Icc y 1) (he 1) h₁
      rw [eq_cornerPoint_of_coords hx hx', eq_cornerPoint_of_coords hy hy',
        P.interpolate_corner, P.interpolate_corner]
      exact congrArg b (by rwa [← eq_cornerPoint_of_coords hx hx', ← eq_cornerPoint_of_coords hy hy'])

end CornerProfile

/-- Agreeing finite-energy pieces glue across a finite cover by word cells. -/
theorem exists_continuousKernel_cellwise (n : ℕ)
    (G : (Fin n → Fin 8) → C(CarpetPoints, ℝ))
    (hG : ∀ w, G w ∈ Q.continuousKernel)
    (hagree : ∀ (w v : Fin n → Fin 8) x y,
      wordMap (List.ofFn w) x = wordMap (List.ofFn v) y → G w x = G v y) :
    ∃ g ∈ Q.continuousKernel, ∀ (w : Fin n → Fin 8) (x : CarpetPoints),
      g (wordMap (List.ofFn w) x) = G w x := by
  let W := Fin n → Fin 8
  let F (w : W) := wordMap (List.ofFn w)
  have hex (x : CarpetPoints) : ∃ (w : W) (y : CarpetPoints), F w y = x :=
    exists_wordMap_range n x
  choose w y hy using hex
  let g (x : CarpetPoints) := G (w x) (y x)
  have hcell (v : W) (x : CarpetPoints) : g (F v x) = G v x :=
    hagree (w (F v x)) v (y (F v x)) x (hy (F v x))
  have hclosed (v : W) : Topology.IsClosedEmbedding (F v) :=
    (continuous_wordMap _).isClosedEmbedding (measurableEmbedding_wordMap _).injective
  have hcov : (⋃ v : W, range (F v)) = univ :=
    eq_univ_of_forall fun x ↦ mem_iUnion.mpr ⟨w x, y x, hy x⟩
  have hc (v : W) : ContinuousOn g (range (F v)) := by
    rw [← image_univ, (hclosed v).isEmbedding.isInducing.continuousOn_image_iff, continuousOn_univ]
    rw [show g ∘ F v = G v from funext (hcell v)]
    exact (G v).continuous
  let g' : C(CarpetPoints, ℝ) := ⟨g, (locallyFinite_of_finite _).continuous hcov
    (fun v ↦ (hclosed v).isClosed_range) hc⟩
  refine ⟨g', Q.continuousKernel_of_cellwise g' n ?_, hcell⟩
  intro v
  have he : g'.comp ⟨F v, continuous_wordMap _⟩ = G v := ContinuousMap.ext (hcell v)
  rw [he]
  exact hG v


namespace CornerProfile

variable {Q} (P : Q.CornerProfile)

/-- Interpolate prescribed corner data continuously on every cell of a
fixed level, and keep the result in the component kernel. -/
theorem exists_global_interpolate (b : CarpetPoints → ℝ) (n : ℕ) :
    ∃ g ∈ Q.continuousKernel, ∀ (w : Fin n → Fin 8) (x : CarpetPoints),
      g (wordMap (List.ofFn w) x) = P.interpolate (cornerData b (List.ofFn w)) x :=
  Q.exists_continuousKernel_cellwise n (fun w ↦ P.interpolate (cornerData b (List.ofFn w)))
    (fun _ ↦ P.interpolate_mem_kernel _)
    (fun _ _ _ _ h ↦ P.interpolate_agree_on_overlap b (by simp) h)

end CornerProfile
end CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent
