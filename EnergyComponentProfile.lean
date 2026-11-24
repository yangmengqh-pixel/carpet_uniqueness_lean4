import CarpetBoundaryDensity
import CarpetVerticalFolding
import EnergyComponentKernel

/-!
# Opposite-side profiles in a component kernel

A kernel function that has plateaus on two bottom-row cells can be folded
vertically. Cutting the folded function at the midlines through those cells
gives a continuous profile that remains in the kernel by cellwise gluing.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology unitInterval

namespace CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent

variable {p : ℝ} {E : SelfSimilarPEnergy p} (Q : E.SelfSimilarComponent)

private theorem bottomWord_eq_of_gridCoordinate {w v : List (Fin 8)}
    (hlen : w.length = v.length) (hx : gridCoordinate w 0 = gridCoordinate v 0)
    (hy : gridCoordinate v 1 = 0) :
    bottomWord w = v := by
  apply gridCoordinate_injective_of_length ((length_bottomWord _).trans hlen)
  intro j
  fin_cases j
  · exact (gridCoordinate_bottomWord w).1.trans hx
  · exact (gridCoordinate_bottomWord w).2.trans hy.symm

private theorem gridCoordinate_eq_of_midline {n : ℕ} {w : Fin n → Fin 8} {x : CarpetPoints}
    (hx : x ∈ range (wordMap (List.ofFn w))) {k : ℕ}
    (h : (3 : ℝ) ^ n * (x : Plane) 0 = (k : ℝ) + 1 / 2) :
    gridCoordinate (List.ofFn w) 0 = k := by
  obtain ⟨hl, hu⟩ := gridCoordinate_bounds hx 0
  rw [h] at hl hu
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h' : ((gridCoordinate (List.ofFn w) 0 : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hlt
    linarith
  · have h' : (k : ℝ) + 1 ≤ gridCoordinate (List.ofFn w) 0 := by exact_mod_cast hgt
    linarith

private noncomputable def horizontalSplice
    (H : C(CarpetPoints, ℝ)) (a b : ℝ) (x : CarpetPoints) : ℝ :=
  if (x : Plane) 0 ≤ a then 0 else if b ≤ (x : Plane) 0 then 1 else H x

private theorem continuous_horizontalSplice
    (H : C(CarpetPoints, ℝ)) {a b : ℝ} (hab : a < b)
    (ha : ∀ x : CarpetPoints, (x : Plane) 0 = a → H x = 0)
    (hb : ∀ x : CarpetPoints, (x : Plane) 0 = b → H x = 1) :
    Continuous (horizontalSplice H a b) := by
  let c (x : CarpetPoints) := (x : Plane) 0
  let L := c ⁻¹' Iic a
  let M := c ⁻¹' Icc a b
  let R := c ⁻¹' Ici b
  have hc : Continuous c :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_subtypeVal
  have hL : IsClosed L := isClosed_Iic.preimage hc
  have hM : IsClosed M := isClosed_Icc.preimage hc
  have hR : IsClosed R := isClosed_Ici.preimage hc
  have hcL : ContinuousOn (horizontalSplice H a b) L := continuous_const.continuousOn.congr
    (fun _ hx ↦ ite_eq_left hx)
  have hcR : ContinuousOn (horizontalSplice H a b) R := continuous_const.continuousOn.congr (by
    intro x hx
    exact (ite_eq_right (show ¬ c x ≤ a from (hab.trans_le hx).not_ge)).trans (ite_eq_left hx))
  have hcM : ContinuousOn (horizontalSplice H a b) M := H.continuous.continuousOn.congr (by
    intro x hx
    have hh : a ≤ c x ∧ c x ≤ b := hx
    rcases lt_or_eq_of_le hh.1 with hl | hl
    · rw [horizontalSplice, ite_eq_right hl.not_ge]
      rcases lt_or_eq_of_le hh.2 with hr | hr
      · rw [ite_eq_right hr.not_ge]
      · rw [ite_eq_left hr.ge, hb x hr]
    · rw [horizontalSplice, ite_eq_left hl.ge, ha x hl.symm])
  have hcover : L ∪ M ∪ R = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hl : c x ≤ a
    · exact Or.inl (Or.inl hl)
    by_cases hr : b ≤ c x
    · exact Or.inr hr
    · exact Or.inl (Or.inr ⟨(not_le.mp hl).le, (not_le.mp hr).le⟩)
  have h := (hcL.union_of_isClosed hcM hL hM).union_of_isClosed hcR (hL.union hM) hR
  rwa [hcover, continuousOn_univ] at h

/-- Ordered plateaus on two bottom-row cells produce an opposite-side
profile in the component kernel. -/
theorem exists_profile_of_bottom_plateaus
    {h : C(CarpetPoints, ℝ)} (hh : h ∈ Q.continuousKernel)
    {u v : List (Fin 8)} (hlen : u.length = v.length)
    (hu : gridCoordinate u 1 = 0) (hv : gridCoordinate v 1 = 0)
    (huv : gridCoordinate u 0 < gridCoordinate v 0)
    (h₀ : ∀ x, h (wordMap u x) = 0) (h₁ : ∀ x, h (wordMap v x) = 1) :
    ∃ g ∈ Q.continuousKernel,
      (∀ x : CarpetPoints, (x : Plane) 0 = 0 → g x = 0) ∧
      (∀ x : CarpetPoints, (x : Plane) 0 = 1 → g x = 1) := by
  let n := u.length
  let s : ℝ := 3 ^ n
  have hs : 0 < s := by dsimp only [s]; positivity
  let a := gridCoordinate u 0
  let b := gridCoordinate v 0
  let A := ((a : ℝ) + 1 / 2) / s
  let B := ((b : ℝ) + 1 / 2) / s
  have hab : (a : ℝ) < b := by exact_mod_cast huv
  have hAB : A < B := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have hA : 0 < A := div_pos (by positivity) hs
  have hB : B < 1 := by
    apply (div_lt_iff₀ hs).mpr
    have hb := gridCoordinate_lt v 0
    rw [← hlen] at hb
    have hb' : (b : ℝ) + 1 ≤ s := by
      dsimp only [b, s, n]
      exact_mod_cast (Nat.succ_le_of_lt hb)
    linarith
  let H : C(CarpetPoints, ℝ) := h.comp (verticalFoldMap n)
  have hfold (w : Fin n → Fin 8) (y : CarpetPoints) :
      H (wordMap (List.ofFn w) y) =
        h (wordMap (bottomWord (List.ofFn w))
          (carpetSymmetry (verticalFoldSymmetry (List.ofFn w)) y)) := by
    change h (verticalFoldMap n (wordMap (List.ofFn w) y)) = _
    have he := verticalFoldMap_wordMap (List.ofFn w) y
    rw [List.length_ofFn] at he
    rw [he]
  have hflat (w : Fin n → Fin 8) {q : List (Fin 8)} (hq : n = q.length)
      (hy : gridCoordinate q 1 = 0) (he : gridCoordinate (List.ofFn w) 0 = gridCoordinate q 0)
      {c : ℝ} (hc : ∀ x, h (wordMap q x) = c) (y : CarpetPoints) :
      H (wordMap (List.ofFn w) y) = c := by
    have hlenw : (List.ofFn w).length = q.length := List.length_ofFn.trans hq
    rw [hfold, bottomWord_eq_of_gridCoordinate hlenw he hy, hc]
  have hmid (q : List (Fin 8)) (hq : n = q.length) (hy : gridCoordinate q 1 = 0)
      {c : ℝ} (hc : ∀ x, h (wordMap q x) = c)
      (x : CarpetPoints) (hx : (x : Plane) 0 = ((gridCoordinate q 0 : ℝ) + 1 / 2) / s) :
      H x = c := by
    obtain ⟨w, y, rfl⟩ := exists_wordMap_range n x
    apply hflat w hq hy _ hc
    apply gridCoordinate_eq_of_midline (mem_range_self y)
    have hx' := (eq_div_iff hs.ne').mp hx
    exact (mul_comm _ _).trans hx'
  let g : C(CarpetPoints, ℝ) := ⟨horizontalSplice H A B,
    continuous_horizontalSplice H hAB (hmid u rfl hu h₀) (hmid v hlen hv h₁)⟩
  refine ⟨g, Q.continuousKernel_of_cellwise g n ?_, ?_, ?_⟩
  · intro w
    let r := gridCoordinate (List.ofFn w) 0
    have bounds (x : CarpetPoints) :
        (r : ℝ) ≤ s * (wordMap (List.ofFn w) x : Plane) 0 ∧
          s * (wordMap (List.ofFn w) x : Plane) 0 ≤ (r : ℝ) + 1 :=
      gridCoordinate_bounds (mem_range_self x) 0
    have upper {k : ℕ} (hk : (r : ℝ) + 1 ≤ k) (x : CarpetPoints) :
        (wordMap (List.ofFn w) x : Plane) 0 < ((k : ℝ) + 1 / 2) / s := by
      apply (lt_div_iff₀ hs).mpr
      rw [mul_comm]
      linarith [(bounds x).2]
    have lower {k : ℕ} (hk : (k : ℝ) + 1 ≤ r) (x : CarpetPoints) :
        ((k : ℝ) + 1 / 2) / s < (wordMap (List.ofFn w) x : Plane) 0 := by
      apply (div_lt_iff₀ hs).mpr
      rw [mul_comm]
      linarith [(bounds x).1]
    by_cases ha : r ≤ a
    · have heq : g.comp ⟨wordMap (List.ofFn w), continuous_wordMap _⟩ =
          ContinuousMap.const CarpetPoints 0 := by
        ext x
        change horizontalSplice H A B (wordMap (List.ofFn w) x) = 0
        rcases lt_or_eq_of_le ha with hl | hl
        · exact ite_eq_left (upper (k := a) (by exact_mod_cast hl) x).le
        · have hlt : r < b := by rw [hl]; exact huv
          have he : (r : ℝ) + 1 ≤ b := by exact_mod_cast hlt
          rw [horizontalSplice, ite_eq_right (upper he x).not_ge]
          split_ifs
          · rfl
          · exact hflat w rfl hu hl h₀ x
      rw [heq]
      exact Q.continuousKernel_const 0
    · by_cases hb : b ≤ r
      · have heq : g.comp ⟨wordMap (List.ofFn w), continuous_wordMap _⟩ =
            ContinuousMap.const CarpetPoints 1 := by
          ext x
          change horizontalSplice H A B (wordMap (List.ofFn w) x) = 1
          rcases lt_or_eq_of_le hb with hl | hl
          · have hsB := lower (k := b) (by exact_mod_cast hl) x
            rw [horizontalSplice, ite_eq_right (hAB.trans hsB).not_ge, ite_eq_left hsB.le]
          · have hlt : a < r := by rw [← hl]; exact huv
            have he : (a : ℝ) + 1 ≤ r := by exact_mod_cast hlt
            rw [horizontalSplice, ite_eq_right (lower he x).not_ge]
            split_ifs
            · rfl
            · exact hflat w hlen hv hl.symm h₁ x
        rw [heq]
        exact Q.continuousKernel_const 1
      · have heq : g.comp ⟨wordMap (List.ofFn w), continuous_wordMap _⟩ =
            (h.comp ⟨wordMap (bottomWord (List.ofFn w)), continuous_wordMap _⟩).comp
              ⟨carpetSymmetry (verticalFoldSymmetry (List.ofFn w)), continuous_carpetSymmetry _⟩ := by
          ext x
          change horizontalSplice H A B (wordMap (List.ofFn w) x) = _
          rw [horizontalSplice, ite_eq_right (lower (k := a) (by exact_mod_cast lt_of_not_ge ha) x).not_ge,
            ite_eq_right (upper (k := b) (by exact_mod_cast lt_of_not_ge hb) x).not_ge, hfold]
          rfl
        rw [heq]
        exact Q.continuousKernel_comp_symmetry (Q.continuousKernel_comp_wordMap hh _) _
  · intro x hx
    change horizontalSplice H A B x = 0
    rw [horizontalSplice, hx, ite_eq_left hA.le]
  · intro x hx
    change horizontalSplice H A B x = 1
    rw [horizontalSplice, hx, ite_eq_right (hAB.trans hB).not_ge, ite_eq_left hB.le]

private theorem exists_plateau_lipschitz (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : ℝ → ℝ) (L : ℝ≥0), LipschitzWith L φ ∧
      (∀ x, |x - a| ≤ ε → φ x = 0) ∧ (∀ x, 2 * ε ≤ |x - a| → φ x = 1) := by
  let L : ℝ≥0 := ε⁻¹.toNNReal
  let ψ (x : ℝ) := (|x - a| - ε) / ε
  have hψ : LipschitzWith L ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (ψ x) (ψ y) ≤ (L : ℝ) * dist x y
    have he : ψ x - ψ y = ε⁻¹ * (|x - a| - |y - a|) := by dsimp only [ψ]; ring
    rw [Real.dist_eq, he, abs_mul, abs_of_pos (inv_pos.mpr hε), Real.dist_eq]
    change _ ≤ (ε⁻¹.toNNReal : ℝ) * _
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hε.le)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hε.le)
    simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (x - a) (y - a)
  refine ⟨fun x ↦ min (max (ψ x) 0) 1, L, (hψ.max_const 0).min_const 1, ?_, ?_⟩
  · intro x hx
    have hh : ψ x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le
    change min (max (ψ x) 0) 1 = 0
    rw [max_eq_right hh, min_eq_left zero_le_one]
  · intro x hx
    have hh : 1 ≤ ψ x := (le_div_iff₀ hε).mpr (by linarith)
    exact min_eq_right (hh.trans (le_max_left _ _))

private theorem exists_profile_of_bottom_ordered_values
    {f : C(CarpetPoints, ℝ)} (hf : f ∈ Q.continuousKernel)
    (t₀ t₁ : I) (ht : (t₀ : ℝ) < t₁) (hvalues : f (bottomPoint t₀) ≠ f (bottomPoint t₁)) :
    ∃ g ∈ Q.continuousKernel,
      (∀ x : CarpetPoints, (x : Plane) 0 = 0 → g x = 0) ∧
      (∀ x : CarpetPoints, (x : Plane) 0 = 1 → g x = 1) := by
  let x₀ := bottomPoint t₀
  let x₁ := bottomPoint t₁
  let ε := |f x₁ - f x₀| / 3
  have hε : 0 < ε := div_pos (abs_pos.mpr (sub_ne_zero.mpr hvalues.symm)) (by norm_num)
  obtain ⟨φ, L, hφ, hφ₀, hφ₁⟩ := exists_plateau_lipschitz (f x₀) hε
  let h := (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp f
  have hh : h ∈ Q.continuousKernel := Q.continuousKernel_comp hf hφ
  obtain ⟨r₀, hr₀, hcont₀⟩ := Metric.continuousAt_iff.mp (f.continuous.continuousAt (x := x₀)) ε hε
  obtain ⟨r₁, hr₁, hcont₁⟩ := Metric.continuousAt_iff.mp (f.continuous.continuousAt (x := x₁)) ε hε
  have hradius : Tendsto (fun n : ℕ ↦ (1 / 3 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨n, hn, hn'⟩ := ((tendsto_wordMap_radius.eventually_lt_const (lt_min hr₀ hr₁)).and
    (hradius.eventually_lt_const (sub_pos.mpr ht))).exists
  obtain ⟨u, hu⟩ := exists_wordMap_range n x₀
  obtain ⟨v, hv⟩ := exists_wordMap_range n x₁
  have h₀ (x : CarpetPoints) : h (wordMap (List.ofFn u) x) = 0 := by
    apply hφ₀
    have hd := wordMap_dist_le n u (mem_range_self x) hu
    have hc := hcont₀ (hd.trans_lt (hn.trans_le (min_le_left _ _)))
    rw [Real.dist_eq] at hc
    exact hc.le
  have h₁ (x : CarpetPoints) : h (wordMap (List.ofFn v) x) = 1 := by
    apply hφ₁
    have hd := wordMap_dist_le n v (mem_range_self x) hv
    have hc := hcont₁ (hd.trans_lt (hn.trans_le (min_le_right _ _)))
    rw [Real.dist_eq, abs_sub_comm] at hc
    have he : |f x₁ - f x₀| ≤ |f x₁ - f (wordMap (List.ofFn v) x)| +
        |f (wordMap (List.ofFn v) x) - f x₀| := by
      calc
        _ = |(f x₁ - f (wordMap (List.ofFn v) x)) +
            (f (wordMap (List.ofFn v) x) - f x₀)| := by rw [sub_add_sub_cancel]
        _ ≤ _ := abs_add_le _ _
    dsimp only [ε] at hc ⊢
    linarith
  have hbottom {w : Fin n → Fin 8} {t : I} (hw : bottomPoint t ∈ range (wordMap (List.ofFn w))) :
      gridCoordinate (List.ofFn w) 1 = 0 := by
    have h := (gridCoordinate_bounds hw 1).1
    change (gridCoordinate (List.ofFn w) 1 : ℝ) ≤ (3 : ℝ) ^ n * 0 at h
    rw [mul_zero] at h
    exact Nat.le_zero.mp (by exact_mod_cast h)
  have huv : gridCoordinate (List.ofFn u) 0 < gridCoordinate (List.ofFn v) 0 := by
    by_contra! h
    have hU := (gridCoordinate_bounds hu 0).1
    have hV := (gridCoordinate_bounds hv 0).2
    change (gridCoordinate (List.ofFn u) 0 : ℝ) ≤ (3 : ℝ) ^ n * (t₀ : ℝ) at hU
    change (3 : ℝ) ^ n * (t₁ : ℝ) ≤ (gridCoordinate (List.ofFn v) 0 : ℝ) + 1 at hV
    have hl := mul_lt_mul_of_pos_left hn' (by positivity : 0 < (3 : ℝ) ^ n)
    have hp : (3 : ℝ) ^ n * (1 / 3 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    rw [hp, mul_sub] at hl
    have h' : (gridCoordinate (List.ofFn v) 0 : ℝ) ≤ gridCoordinate (List.ofFn u) 0 := by
      exact_mod_cast h
    linarith
  exact Q.exists_profile_of_bottom_plateaus hh (List.length_ofFn.trans List.length_ofFn.symm)
    (hbottom hu) (hbottom hv) huv h₀ h₁

private def symmetryFromBottom (j a : Fin 2) : SquareSymmetry :=
  (decide (j = 0), fun k ↦ decide (k = j ∧ a = 1))

private theorem symmetryFromBottom_coord (j a : Fin 2) (x : CarpetPoints) :
    (carpetSymmetry (symmetryFromBottom j a) x : Plane) j =
      if a = 1 then 1 - (x : Plane) 1 else (x : Plane) 1 := by
  fin_cases j <;> fin_cases a <;> rfl

/-- Lemma 6.4. A continuous kernel function that is nonconstant on any
exterior side yields a kernel profile separating left and right. -/
theorem exists_profile_of_nonconstant_side
    {f : C(CarpetPoints, ℝ)} (hf : f ∈ Q.continuousKernel) (j a : Fin 2)
    (x y : CarpetPoints) (hx : (x : Plane) j = (a.val : ℝ))
    (hy : (y : Plane) j = (a.val : ℝ)) (hne : f x ≠ f y) :
    ∃ g ∈ Q.continuousKernel,
      (∀ x : CarpetPoints, (x : Plane) 0 = 0 → g x = 0) ∧
      (∀ x : CarpetPoints, (x : Plane) 0 = 1 → g x = 1) := by
  let sref := symmetryFromBottom j a
  let h := f.comp ⟨carpetSymmetry sref, continuous_carpetSymmetry sref⟩
  have hh : h ∈ Q.continuousKernel := Q.continuousKernel_comp_symmetry hf sref
  have witness (x : CarpetPoints) (hx : (x : Plane) j = (a.val : ℝ)) :
      ∃ t : I, carpetSymmetry sref (bottomPoint t) = x := by
    obtain ⟨z, rfl⟩ := (bijective_carpetSymmetry sref).2 x
    suffices hz : z ∈ carpetBottom by
      rw [carpetBottom_eq_range] at hz
      obtain ⟨t, rfl⟩ := hz
      exact ⟨t, rfl⟩
    change (z : Plane) 1 = 0
    change (carpetSymmetry (symmetryFromBottom j a) z : Plane) j = (a.val : ℝ) at hx
    rw [symmetryFromBottom_coord] at hx
    fin_cases a
    · exact hx
    · change 1 - (z : Plane) 1 = 1 at hx
      linarith
  obtain ⟨s, hs⟩ := witness x hx
  obtain ⟨t, ht⟩ := witness y hy
  have hst : h (bottomPoint s) ≠ h (bottomPoint t) := by
    change f (carpetSymmetry sref (bottomPoint s)) ≠ f (carpetSymmetry sref (bottomPoint t))
    rwa [hs, ht]
  have hn : (s : ℝ) ≠ (t : ℝ) := fun he ↦ hst (congrArg (fun r : I ↦ h (bottomPoint r)) (Subtype.ext he))
  rcases lt_or_gt_of_ne hn with hl | hr
  · exact Q.exists_profile_of_bottom_ordered_values hh s t hl hst
  · exact Q.exists_profile_of_bottom_ordered_values hh t s hr hst.symm

/-- A nonconstant continuous kernel function yields the profile in the
first part of the proof of Theorem 6.6. -/
theorem exists_profile_of_nonconstant_kernel
    {f : C(CarpetPoints, ℝ)} (hf : f ∈ Q.continuousKernel)
    (hne : ∃ x y : CarpetPoints, f x ≠ f y) :
    ∃ g ∈ Q.continuousKernel,
      (∀ x : CarpetPoints, (x : Plane) 0 = 0 → g x = 0) ∧
      (∀ x : CarpetPoints, (x : Plane) 0 = 1 → g x = 1) := by
  have hw : ∃ (w : List (Fin 8)) (j a : Fin 2) (x y : CarpetPoints),
      (x : Plane) j = (a.val : ℝ) ∧ (y : Plane) j = (a.val : ℝ) ∧
      f (wordMap w x) ≠ f (wordMap w y) := by
    by_contra! h
    obtain ⟨x, y, hxy⟩ := hne
    have hc := constant_of_constant_on_word_sides f
      (fun w j a x y hx hy ↦ h w j a x y hx hy)
    exact hxy ((hc x).trans (hc y).symm)
  obtain ⟨w, j, a, x, y, hx, hy, hxy⟩ := hw
  exact Q.exists_profile_of_nonconstant_side (Q.continuousKernel_comp_wordMap hf w)
    j a x y hx hy hxy

end CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent
