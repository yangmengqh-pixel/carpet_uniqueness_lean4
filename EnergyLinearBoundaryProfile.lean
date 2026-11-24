import CarpetCoordinateInterpolation
import EnergyBoundarySeries

/-!
# A profile with linear traces

Successive coordinate interpolants differ on the bottom side by a
scaled copy of a fixed difference. Place those differences in boundary
strips and sum them in the graph norm. Reflection supplies the same
linear trace on the top side.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CarpetEnergy

/-- The preimage of an exterior side lies on the same exterior side. -/
theorem wordMap_preimage_side {n : ℕ} (w : Fin n → Fin 8) (j a : Fin 2)
    (x : CarpetPoints) (hx : (wordMap (List.ofFn w) x : Plane) j = a.val) :
    (x : Plane) j = a.val ∧ (gridCoordinate (List.ofFn w) j : ℝ) =
      ((3 : ℝ) ^ n - 1) * a.val := by
  have he := wordMap_scaled_coord (List.ofFn w) x j
  rw [List.length_ofFn, hx] at he
  have hgrid := gridCoordinate_lt (List.ofFn w) j
  rw [List.length_ofFn] at hgrid
  have hg₁ : (gridCoordinate (List.ofFn w) j : ℝ) + 1 ≤ (3 : ℝ) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt hgrid
  have hg₀ : 0 ≤ (gridCoordinate (List.ofFn w) j : ℝ) := Nat.cast_nonneg _
  have hb := carpet_coord_mem_Icc x j
  fin_cases a
  · change (3 : ℝ) ^ n * 0 = _ at he
    change (x : Plane) j = 0 ∧ (gridCoordinate (List.ofFn w) j : ℝ) = (3 ^ n - 1) * 0
    exact ⟨by linarith [hb.1], by linarith [hb.1]⟩
  · change (3 : ℝ) ^ n * 1 = _ at he
    change (x : Plane) j = 1 ∧ (gridCoordinate (List.ofFn w) j : ℝ) = (3 ^ n - 1) * 1
    exact ⟨by linarith [hb.2], by linarith [hb.2]⟩

namespace SelfSimilarPEnergy

open SelfSimilarComponent SelfSimilarComponent.CornerProfile

variable {p : ℝ} (E : SelfSimilarPEnergy p)

theorem coordinate_interp_side {Q : E.SelfSimilarComponent} (P : Q.CornerProfile)
    (n : ℕ) (g : C(CarpetPoints, ℝ))
    (hg : ∀ (w : Fin n → Fin 8) x, g (wordMap (List.ofFn w) x) =
      ((gridCoordinate (List.ofFn w) 0 : ℝ) + P.toContinuousMap x) / (3 : ℝ) ^ n)
    (a : Fin 2) (z : CarpetPoints) (hz : (z : Plane) 0 = a.val) :
    g z = a.val := by
  obtain ⟨w, x, rfl⟩ := exists_wordMap_range n z
  obtain ⟨hx, hgrid⟩ := wordMap_preimage_side w 0 a x hz
  rw [hg, hgrid, P.side a x hx]
  apply (div_eq_iff (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0))).mpr
  ring

private theorem strip_correction_zero_on_other_sides
    (d : C(CarpetPoints, ℝ))
    (hd : ∀ x : CarpetPoints,
      (x : Plane) 0 = 0 ∨ (x : Plane) 0 = 1 ∨ (x : Plane) 1 = 1 → d x = 0)
    (n : ℕ) (g : C(CarpetPoints, ℝ))
    (hg : ∀ (w : Fin n → Fin 8) x, g (wordMap (List.ofFn w) x) =
      if gridCoordinate (List.ofFn w) 1 = 0 then ((3 : ℝ) ^ n)⁻¹ * d x else 0)
    (z : CarpetPoints)
    (hz : (z : Plane) 0 = 0 ∨ (z : Plane) 0 = 1 ∨ (z : Plane) 1 = 1) :
    g z = 0 := by
  obtain ⟨w, x, rfl⟩ := exists_wordMap_range n z
  rw [hg]
  split_ifs
  · rw [hd x ?_, mul_zero]
    rcases hz with hz | hz | hz
    · exact Or.inl (wordMap_preimage_side w 0 0 x hz).1
    · exact Or.inr (Or.inl (wordMap_preimage_side w 0 1 x hz).1)
    · exact Or.inr (Or.inr (wordMap_preimage_side w 1 1 x hz).1)
  · rfl

/-- An opposite-side profile whose restriction to each horizontal
exterior side is the horizontal coordinate. -/
theorem exists_cornerProfile_linear_traces :
    ∃ P : E.zeroComponent.CornerProfile,
      ∀ z : CarpetPoints, (z : Plane) 1 = 0 ∨ (z : Plane) 1 = 1 →
        P.toContinuousMap z = (z : Plane) 0 := by
  let Q := E.zeroComponent
  obtain ⟨P⟩ := E.exists_zeroCornerProfile
  choose g hmem hg using P.exists_coordinate_interp
  have hgs (n : ℕ) (a : Fin 2) (z : CarpetPoints) (hz : (z : Plane) 0 = a.val) :
      g n z = a.val := E.coordinate_interp_side P n (g n) (hg n) a z hz
  let d : C(CarpetPoints, ℝ) :=
    (g 1 - P.toContinuousMap) * (ContinuousMap.const CarpetPoints 1 - P.vertical)
  have hm : d ∈ Q.continuousKernel := Q.continuousKernel_mul
    (Q.continuousKernel_sub (hmem 1) P.mem_kernel)
    (Q.continuousKernel_sub (Q.continuousKernel_const 1) P.vertical_mem_kernel)
  have hd := hm.choose
  have hdz (z : CarpetPoints)
      (hz : (z : Plane) 0 = 0 ∨ (z : Plane) 0 = 1 ∨ (z : Plane) 1 = 1) : d z = 0 := by
    change (g 1 z - P.toContinuousMap z) * (1 - P.vertical z) = 0
    rcases hz with hz | hz | hz
    · rw [hgs 1 0 z hz, P.side 0 z hz, sub_self, zero_mul]
    · rw [hgs 1 1 z hz, P.side 1 z hz, sub_self, zero_mul]
    · rw [P.vertical_side 1 z hz]
      norm_num
  have hdb (z : CarpetPoints) (hz : (z : Plane) 1 = 0) : d z = g 1 z - P.toContinuousMap z := by
    change (g 1 z - P.toContinuousMap z) * (1 - P.vertical z) = _
    rw [P.vertical_side 0 z hz]
    norm_num
  choose u hu hcell hnorm henergy using E.exists_bottom_strip_correction d hd hdz
  obtain ⟨v, hv, hsv⟩ := E.exists_hasSum_bottom_strips d hd u hu hnorm henergy
  have hvz (z : CarpetPoints)
      (hz : (z : Plane) 0 = 0 ∨ (z : Plane) 0 = 1 ∨ (z : Plane) 1 = 1) : v z = 0 := by
    have h := (ContinuousMap.evalCLM ℝ z).hasSum hsv
    have hu' (n : ℕ) : u n z = 0 :=
      strip_correction_zero_on_other_sides d hdz n (u n) (hcell n) z hz
    exact h.unique (by simpa only [ContinuousMap.evalCLM_apply, hu'] using
      (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0))
  have hub (n : ℕ) (z : CarpetPoints) (hz : (z : Plane) 1 = 0) :
      u n z = g (n + 1) z - g n z := by
    obtain ⟨w, x, rfl⟩ := exists_wordMap_range n z
    obtain ⟨hx, hw⟩ := wordMap_preimage_side w 1 0 x hz
    have hw' : gridCoordinate (List.ofFn w) 1 = 0 := by
      have hh : (gridCoordinate (List.ofFn w) 1 : ℝ) = 0 := by
        exact hw.trans (mul_zero _)
      exact_mod_cast hh
    rw [hcell, ite_eq_left hw', hdb x hx, hg n,
      coordinate_interp_succ P n (hg 1) (hg (n + 1)) w x, ← sub_div, add_sub_add_left_eq_sub,
      div_eq_mul_inv, mul_comm]
  have hvb (z : CarpetPoints) (hz : (z : Plane) 1 = 0) : v z = (z : Plane) 0 - P.toContinuousMap z := by
    have vsum := (ContinuousMap.evalCLM ℝ z).hasSum hsv
    have hl₁ : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, u k z) atTop (𝓝 (v z)) :=
      vsum.tendsto_sum_nat
    have htel (n : ℕ) : (∑ k ∈ Finset.range n, u k z) = g n z - g 0 z := by
      simp_rw [fun k ↦ hub k z hz]
      exact Finset.sum_range_sub (fun k ↦ g k z) n
    have ht : Tendsto (fun n : ℕ ↦ ((3 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      simpa only [inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (3 : ℝ)⁻¹ by norm_num) (by norm_num))
    have hg_lim : Tendsto (fun n : ℕ ↦ g n z) atTop (𝓝 ((z : Plane) 0)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ ↦ norm_nonneg _) (fun n ↦ by
          rw [Real.norm_eq_abs]
          exact coordinate_interp_abs_sub_le P n (g n) (hg n) z)
    have hg₀ : g 0 z = P.toContinuousMap z := by
      have hh := hg 0 (fun j ↦ Fin.elim0 j) z
      simpa only [List.ofFn_zero, wordMap, id_eq, gridCoordinate, Nat.cast_zero,
        zero_add, pow_zero, div_one] using hh
    exact tendsto_nhds_unique (by simpa only [htel] using hl₁)
      (by simpa only [hg₀] using hg_lim.sub_const (g 0 z))
  let flip : C(CarpetPoints, CarpetPoints) := ⟨carpetSymmetry verticalFlip, continuous_carpetSymmetry _⟩
  have hflip₀ (z : CarpetPoints) : (flip z : Plane) 0 = (z : Plane) 0 := rfl
  have hflip₁ (z : CarpetPoints) : (flip z : Plane) 1 = 1 - (z : Plane) 1 := rfl
  have hflipflip (z : CarpetPoints) : flip (flip z) = z :=
    carpetSymmetry_leftInverse verticalFlip z
  let t := P.toContinuousMap + v + v.comp flip
  have htv : v ∈ Q.continuousKernel := ⟨hv, rfl⟩
  have ht : t ∈ Q.continuousKernel :=
    Q.continuousKernel_add (Q.continuousKernel_add P.mem_kernel htv)
      (Q.continuousKernel_comp_symmetry htv verticalFlip)
  have htL (a : Fin 2) (z : CarpetPoints) (hz : (z : Plane) 0 = a.val) : t z = a.val := by
    have h (x : CarpetPoints) (hx : (x : Plane) 0 = a.val) : v x = 0 := by
      fin_cases a
      · exact hvz x (Or.inl hx)
      · exact hvz x (Or.inr (Or.inl hx))
    change P.toContinuousMap z + v z + v (flip z) = _
    rw [P.side a z hz, h z hz, h (flip z) ((hflip₀ z).trans hz), add_zero, add_zero]
  have htB (z : CarpetPoints) (hz : (z : Plane) 1 = 0 ∨ (z : Plane) 1 = 1) :
      t z = (z : Plane) 0 := by
    change P.toContinuousMap z + v z + v (flip z) = _
    rcases hz with hz | hz
    · rw [hvb z hz, hvz (flip z) (Or.inr (Or.inr (by rw [hflip₁, hz, sub_zero])))]
      ring
    · rw [hvz z (Or.inr (Or.inr hz)), hvb (flip z) (by rw [hflip₁, hz, sub_self]),
        hflip₀, show P.toContinuousMap (flip z) = P.toContinuousMap z from P.flip z]
      ring
  let φ (s : ℝ) := min (max s 0) 1
  have hφ : LipschitzWith 1 φ := (LipschitzWith.id.max_const (0 : ℝ)).min_const 1
  let a := (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp t
  have hφfix {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : φ s = s :=
    congrArg (fun z : ℝ ↦ min z 1) (max_eq_left hs.1) |>.trans (min_eq_left hs.2)
  refine ⟨⟨a, Q.continuousKernel_comp ht hφ,
    fun z ↦ ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩,
    fun b z hz ↦ ?_, fun z ↦ ?_⟩, fun z hz ↦ ?_⟩
  · change φ (t z) = _
    rw [htL b z hz]
    exact hφfix (hz ▸ carpet_coord_mem_Icc z 0)
  · change φ (t (flip z)) = φ (t z)
    congr 1
    change P.toContinuousMap (flip z) + v (flip z) + v (flip (flip z)) =
      P.toContinuousMap z + v z + v (flip z)
    rw [hflipflip, show P.toContinuousMap (flip z) = P.toContinuousMap z from P.flip z]
    ring
  · change φ (t z) = _
    rw [htB z hz]
    exact hφfix (carpet_coord_mem_Icc z 0)

end SelfSimilarPEnergy
end CarpetEnergy
