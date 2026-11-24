import CarpetFolding
import EnergyVanishing
import EnergyContraction
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Opposite-side capacity

A left-to-right profile can be compressed into the two middle-column cells,
leaving the three left cells at zero and the three right cells at one. Its
energy becomes twice the scaling factor times its original energy.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

/-- A continuous finite-energy competitor taking boundary values zero and one. -/
structure LeftRightProfile where
  toContinuousMap : C(CarpetPoints, ℝ)
  mem_domain : continuousLp p toContinuousMap ∈ E.domain
  left : ∀ x : CarpetPoints, (x : Plane) 0 = 0 → toContinuousMap x = 0
  right : ∀ x : CarpetPoints, (x : Plane) 0 = 1 → toContinuousMap x = 1
  bounds : ∀ x : CarpetPoints, 0 ≤ toContinuousMap x ∧ toContinuousMap x ≤ 1

namespace LeftRightProfile

/-- The associated element of the energy domain. -/
noncomputable def toDomain (u : E.LeftRightProfile) : E.domain :=
  ⟨continuousLp p u.toContinuousMap, u.mem_domain⟩

end LeftRightProfile

private theorem first_coord_cellMap (i : Fin 8) (x : CarpetPoints) :
    ((cellMap i x : CarpetPoints) : Plane) 0 = ((x : Plane) 0 + (cellDigit i 0 : ℕ)) / 3 := by
  change cellSimilarity i x 0 = _
  rw [cellSimilarity_coord, ← cellDigit_cast]

private theorem continuous_horizontal_coord : Continuous (fun x : CarpetPoints ↦ (x : Plane) 0) :=
  (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_subtypeVal

private noncomputable def splice (u : E.LeftRightProfile) (x : CarpetPoints) : ℝ :=
  if (x : Plane) 0 ≤ 1 / 3 then 0
  else if 2 / 3 ≤ (x : Plane) 0 then 1
  else u.toContinuousMap (cellFoldingMap 1 x)

private theorem splice_eq_one (u : E.LeftRightProfile) {x : CarpetPoints}
    (hx : 2 / 3 ≤ (x : Plane) 0) : splice E u x = 1 := by
  rw [splice, ite_eq_right (by linarith), ite_eq_left hx]

private theorem splice_eq_fold (u : E.LeftRightProfile) {x : CarpetPoints}
    (hx : (x : Plane) 0 ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    splice E u x = u.toContinuousMap (cellFoldingMap 1 x) := by
  rcases lt_or_eq_of_le hx.1 with h₁ | h₁
  · rcases lt_or_eq_of_le hx.2 with h₂ | h₂
    · rw [splice, ite_eq_right h₁.not_ge, ite_eq_right h₂.not_ge]
    · rw [splice_eq_one E u h₂.ge]
      symm
      apply u.right
      rw [cellFoldingMap_one_first_coord x hx, h₂]
      norm_num
  · rw [splice, ite_eq_left h₁.ge]
    symm
    apply u.left
    rw [cellFoldingMap_one_first_coord x hx, ← h₁]
    norm_num

private theorem continuous_splice (u : E.LeftRightProfile) : Continuous (splice E u) := by
  let c (x : CarpetPoints) := (x : Plane) 0
  let L := c ⁻¹' Iic (1 / 3)
  let M := c ⁻¹' Icc (1 / 3) (2 / 3)
  let R := c ⁻¹' Ici (2 / 3)
  have hz : Continuous c := continuous_horizontal_coord
  have hL : IsClosed L := isClosed_Iic.preimage hz
  have hM : IsClosed M := isClosed_Icc.preimage hz
  have hR : IsClosed R := isClosed_Ici.preimage hz
  have hcL : ContinuousOn (splice E u) L := continuous_const.continuousOn.congr
    (fun _ hx ↦ ite_eq_left hx)
  have hcM : ContinuousOn (splice E u) M :=
    (u.toContinuousMap.continuous.comp (cellFoldingMap 1).continuous).continuousOn.congr
      (fun _ hx ↦ splice_eq_fold E u hx)
  have hcR : ContinuousOn (splice E u) R := continuous_const.continuousOn.congr
    (fun _ hx ↦ splice_eq_one E u hx)
  have hcover : L ∪ M ∪ R = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hl : c x ≤ 1 / 3
    · exact Or.inl (Or.inl hl)
    by_cases hr : 2 / 3 ≤ c x
    · exact Or.inr hr
    exact Or.inl (Or.inr ⟨(not_le.mp hl).le, (not_le.mp hr).le⟩)
  have h := (hcL.union_of_isClosed hcM hL hM).union_of_isClosed hcR (hL.union hM) hR
  rwa [hcover, continuousOn_univ] at h

private theorem splice_cell_eq (u : E.LeftRightProfile) (i : Fin 8) (x : CarpetPoints) :
    splice E u (cellMap i x) =
      if cellDigit i 0 = 1 then u.toContinuousMap x
      else if cellDigit i 0 = 0 then 0 else 1 := by
  have hx := carpet_coord_mem_Icc x 0
  have hi := first_coord_cellMap i x
  have hcases : cellDigit i 0 = 0 ∨ cellDigit i 0 = 1 ∨ cellDigit i 0 = 2 := by
    fin_cases i <;> decide
  rcases hcases with h | h | h
  · rw [h] at hi ⊢
    norm_num only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.zero_ne_one, ite_false, ite_eq_left rfl]
      at hi ⊢
    exact ite_eq_left (by linarith [hx.2])
  · rw [h] at hi
    simp only [Fin.val_one, Nat.cast_one] at hi
    rw [ite_eq_left h]
    rw [splice_eq_fold E u (by exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)]
    have hm : ∀ i : Fin 8, cellDigit i 0 = 1 → i = 1 ∨ i = 5 := by decide
    rcases hm i h with rfl | rfl
    · rw [cellFoldingMap_leftInverse 1 x]
    · rw [cellFoldingMap_one_leftInverse_five x]
  · rw [h] at hi ⊢
    norm_num only [Fin.val_two, Nat.cast_ofNat] at hi
    have h1 : (2 : Fin 3) ≠ 1 := by decide
    have h0 : (2 : Fin 3) ≠ 0 := by decide
    rw [ite_eq_right h1, ite_eq_right h0, splice_eq_one E u (by linarith [hx.1])]

private theorem continuousLp_const_eq (a : ℝ) :
    continuousLp p (ContinuousMap.const CarpetPoints a) = constantLp p a := by
  apply Lp.ext
  exact (continuousLp_ae_eq p _).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a).symm

/-- Compress a profile to the middle column, filling the other cells with constants. -/
noncomputable def spliceProfile (u : E.LeftRightProfile) : E.LeftRightProfile := by
  let v : C(CarpetPoints, ℝ) := ⟨splice E u, continuous_splice E u⟩
  refine ⟨v, (E.continuous_gluing v).mpr ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : cellDigit i 0 = 1
    · have hval : v.comp ⟨cellMap i, continuous_cellMap i⟩ = u.toContinuousMap := by
        ext x
        exact (splice_cell_eq E u i x).trans (ite_eq_left hi)
      rw [hval]
      exact u.mem_domain
    · let a : ℝ := if cellDigit i 0 = 0 then 0 else 1
      have hval : v.comp ⟨cellMap i, continuous_cellMap i⟩ = ContinuousMap.const _ a := by
        ext x
        exact (splice_cell_eq E u i x).trans (ite_eq_right hi)
      rw [hval, continuousLp_const_eq]
      exact E.constant_mem a
  · intro x hx
    exact ite_eq_left (hx.symm ▸ (by norm_num : (0 : ℝ) ≤ 1 / 3))
  · intro x hx
    exact splice_eq_one E u (hx.symm ▸ (by norm_num : (2 / 3 : ℝ) ≤ 1))
  · intro x
    change 0 ≤ splice E u x ∧ splice E u x ≤ 1
    unfold splice
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact u.bounds _

theorem spliceProfile_eq_zero (u : E.LeftRightProfile) (x : CarpetPoints)
    (hx : (x : Plane) 0 ≤ 1 / 3) : (E.spliceProfile u).toContinuousMap x = 0 :=
  ite_eq_left hx

theorem spliceProfile_eq_one (u : E.LeftRightProfile) (x : CarpetPoints)
    (hx : 2 / 3 ≤ (x : Plane) 0) : (E.spliceProfile u).toContinuousMap x = 1 :=
  splice_eq_one E u hx

theorem energy_spliceProfile (u : E.LeftRightProfile) :
    (E.energy ((E.spliceProfile u).toDomain E) : ℝ) =
      2 * E.scalingFactor * (E.energy (u.toDomain E) : ℝ) := by
  let v := E.spliceProfile u
  have hcell (i : Fin 8) :
      E.energy (E.pullback i (v.toDomain E)) =
        if cellDigit i 0 = 1 then E.energy (u.toDomain E) else 0 := by
    by_cases hi : cellDigit i 0 = 1
    · have heq : E.pullback i (v.toDomain E) = u.toDomain E := by
        apply Subtype.ext
        change cellPullback i (continuousLp p v.toContinuousMap) = continuousLp p u.toContinuousMap
        rw [cellPullback_continuousLp]
        congr 1
        ext x
        exact (splice_cell_eq E u i x).trans (ite_eq_left hi)
      rw [heq, ite_eq_left hi]
    · rw [ite_eq_right hi]
      apply (E.zero_iff_constant _).mpr
      let a : ℝ := if cellDigit i 0 = 0 then 0 else 1
      refine ⟨a, ?_⟩
      change cellPullback i (continuousLp p v.toContinuousMap) = constantLp p a
      rw [cellPullback_continuousLp, ← continuousLp_const_eq]
      congr 1
      ext x
      exact (splice_cell_eq E u i x).trans (ite_eq_right hi)
  change (E.energy (v.toDomain E) : ℝ) = _
  rw [E.isScalingFactor_scalingFactor.2 (v.toDomain E)]
  simp only [hcell]
  norm_num [Fin.sum_univ_succ, cellDigit, Fin.reduceFinMk]
  ring

private theorem exists_profile_of_sides (u : C(CarpetPoints, ℝ))
    (hu : continuousLp p u ∈ E.domain)
    (hL : ∀ x : CarpetPoints, (x : Plane) 0 = 0 → u x ≤ 0)
    (hR : ∀ x : CarpetPoints, (x : Plane) 0 = 1 → 1 ≤ u x) :
    ∃ v : E.LeftRightProfile, E.energy (v.toDomain E) ≤ E.energy ⟨continuousLp p u, hu⟩ := by
  let v : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ min (max (u x) 0) 1, (u.continuous.max continuous_const).min continuous_const⟩
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let g := E.unitTruncation f
  have heq : continuousLp p v = (g : CarpetLp p) := by
    apply Lp.ext
    have hr : (g : CarpetLp p) =ᵐ[carpetMeasure] v :=
      (E.unitTruncation_ae f).trans ((continuousLp_ae_eq p u).mono fun x hx ↦
        congrArg (fun t : ℝ ↦ min (max t 0) 1) hx)
    exact (continuousLp_ae_eq p v).trans hr.symm
  have hv : continuousLp p v ∈ E.domain := heq.symm ▸ g.property
  let V : E.LeftRightProfile :=
    { toContinuousMap := v
      mem_domain := hv
      left := fun x hx ↦ by change min (max (u x) 0) 1 = 0; rw [max_eq_right (hL x hx), min_eq_left zero_le_one]
      right := fun x hx ↦ min_eq_right ((hR x hx).trans (le_max_left _ _))
      bounds := fun _ ↦ ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩ }
  have hV : V.toDomain E = g := Subtype.ext heq
  refine ⟨V, ?_⟩
  rw [hV]
  exact E.energy_unitTruncation_le f

theorem nonempty_leftRightProfile : Nonempty E.LeftRightProfile := by
  let c : C(CarpetPoints, ℝ) := ⟨fun x ↦ (x : Plane) 0, continuous_horizontal_coord⟩
  obtain ⟨u, hu, hdist⟩ := E.regular_sup c (1 / 4) (by norm_num)
  let v : C(CarpetPoints, ℝ) :=
    ⟨fun x ↦ 2 * u x - 1 / 2, (continuous_const.mul u.continuous).sub continuous_const⟩
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let b : E.domain := ⟨constantLp p (-1 / 2), E.constant_mem (-1 / 2)⟩
  have heq : (continuousLp p v : CarpetLp p) = (((2 : ℝ) • f + b : E.domain) : CarpetLp p) := by
    apply Lp.ext
    filter_upwards [continuousLp_ae_eq p v, continuousLp_ae_eq p u,
      Lp.coeFn_smul (2 : ℝ) (f : CarpetLp p),
      Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure (-1 / 2 : ℝ),
      Lp.coeFn_add (((2 : ℝ) • f : E.domain) : CarpetLp p) (b : CarpetLp p)] with x h₁ h₂ h₃ h₄ h₅
    change continuousLp p v x = 2 * u x - 1 / 2 at h₁
    change (f : CarpetLp p) x = u x at h₂
    change (((2 : ℝ) • f : E.domain) : CarpetLp p) x = 2 * (f : CarpetLp p) x at h₃
    change (b : CarpetLp p) x = -1 / 2 at h₄
    change (((2 : ℝ) • f + b : E.domain) : CarpetLp p) x =
      (((2 : ℝ) • f : E.domain) : CarpetLp p) x + (b : CarpetLp p) x at h₅
    rw [h₁, h₅, h₃, h₂, h₄]
    ring
  have hv : continuousLp p v ∈ E.domain := heq.symm ▸ ((2 : ℝ) • f + b : E.domain).property
  have happrox (x : CarpetPoints) : |u x - (x : Plane) 0| < 1 / 4 := by
    have h := ((u - c).norm_coe_le_norm x).trans_lt hdist
    change ‖u x - (x : Plane) 0‖ < 1 / 4 at h
    simpa only [Real.norm_eq_abs] using h
  obtain ⟨V, _⟩ := E.exists_profile_of_sides v hv
    (fun x hx ↦ by
      have h := (abs_lt.mp (happrox x)).2
      change 2 * u x - 1 / 2 ≤ 0
      linarith only [h, hx])
    (fun x hx ↦ by
      have h := (abs_lt.mp (happrox x)).1
      change 1 ≤ 2 * u x - 1 / 2
      linarith only [h, hx])
  exact ⟨V⟩

private theorem not_tendsto_energy_spliceProfile_zero (u : ℕ → E.LeftRightProfile) :
    ¬ Tendsto (fun n ↦ (E.energy ((E.spliceProfile (u n)).toDomain E) : ℝ)) atTop (𝓝 0) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  let A := range (cellMap 0)
  let B := range (cellMap 2)
  have hA : carpetMeasure A ≠ 0 := by
    change carpetMeasure (range (wordMap [0])) ≠ 0
    rw [carpetMeasure_range_wordMap]
    norm_num
  have hB : carpetMeasure B ≠ 0 := by
    change carpetMeasure (range (wordMap [2])) ≠ 0
    rw [carpetMeasure_range_wordMap]
    norm_num
  have hBm : MeasurableSet B := (measurableEmbedding_cellMap 2).measurableSet_range
  let g (n : ℕ) := E.spliceProfile (u n)
  let f (n : ℕ) := (g n).toDomain E
  have hf (n : ℕ) : (f n : CarpetLp p) =ᵐ[carpetMeasure] (g n).toContinuousMap :=
    continuousLp_ae_eq p _
  have hp (n : ℕ) : ∀ᵐ x ∂carpetMeasure, 0 ≤ (f n : CarpetLp p) x ∧ (f n : CarpetLp p) x ≤ 1 :=
    (hf n).mono fun x hx ↦ hx ▸ (g n).bounds x
  have hzero (n : ℕ) : (f n : CarpetLp p) =ᵐ[carpetMeasure.restrict A] fun _ ↦ 0 := by
    filter_upwards [ae_restrict_of_ae (hf n), ae_restrict_mem (measurableEmbedding_cellMap 0).measurableSet_range]
      with x hx hxA
    obtain ⟨y, rfl⟩ := hxA
    exact hx.trans ((splice_cell_eq E (u n) 0 y).trans (by norm_num [cellDigit, Fin.reduceFinMk]))
  let b := indicatorConstLp (ENNReal.ofReal p) hBm (measure_ne_top carpetMeasure B) (1 : ℝ)
  have hb : 0 < ‖b‖ := by
    change 0 < ‖indicatorConstLp (ENNReal.ofReal p) hBm (measure_ne_top carpetMeasure B) (1 : ℝ)‖
    rw [norm_indicatorConstLp (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans E.one_lt_p))
      ENNReal.ofReal_ne_top, norm_one, one_mul]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hB (measure_ne_top _ _)) _
  have hb_le (n : ℕ) : ‖b‖ ≤ ‖(f n : CarpetLp p)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    have hbc : b =ᵐ[carpetMeasure] B.indicator fun _ ↦ (1 : ℝ) := indicatorConstLp_coeFn
    filter_upwards [hbc, hf n] with x hbx hfx
    change b x = B.indicator (fun _ ↦ (1 : ℝ)) x at hbx
    rw [hbx, hfx]
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      obtain ⟨y, rfl⟩ := hx
      have hsplice : (g n).toContinuousMap (cellMap 2 y) = 1 :=
        (splice_cell_eq E (u n) 2 y).trans (by norm_num [cellDigit, Fin.reduceFinMk])
      rw [hsplice]
    · rw [indicator_of_notMem hx, norm_zero]
      exact norm_nonneg _
  intro h
  have ht := E.tendsto_norm_zero_of_energy_tendsto_zero_of_ae_zero A hA zero_lt_one f hp hzero h
  exact hb.not_ge (le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hb_le))

private theorem exists_pos_le_energy_profile :
    ∃ c > 0, ∀ u : E.LeftRightProfile, c ≤ (E.energy (u.toDomain E) : ℝ) := by
  by_contra! h
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose u hu using fun n : ℕ ↦ h (ε n) (hε n)
  have hlim : Tendsto (fun n ↦ (E.energy ((u n).toDomain E) : ℝ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n ↦ (E.energy ((u n).toDomain E)).property) (fun n ↦ (hu n).le)
  apply E.not_tendsto_energy_spliceProfile_zero u
  simpa only [E.energy_spliceProfile, mul_zero] using hlim.const_mul (2 * E.scalingFactor)

/-- The opposite-side capacity with boundary conditions (f≤0) and (1≤f),
as in the first line of (3.1). -/
noncomputable def leftRightCapacity : ℝ :=
  sInf {e : ℝ | ∃ u : C(CarpetPoints, ℝ), ∃ hu : continuousLp p u ∈ E.domain,
    (∀ x : CarpetPoints, (x : Plane) 0 = 0 → u x ≤ 0) ∧
    (∀ x : CarpetPoints, (x : Plane) 0 = 1 → 1 ≤ u x) ∧
    e = (E.energy ⟨continuousLp p u, hu⟩ : ℝ)}

theorem leftRightCapacity_eq_sInf_profile :
    E.leftRightCapacity = sInf (range fun u : E.LeftRightProfile ↦ (E.energy (u.toDomain E) : ℝ)) := by
  let P := range fun u : E.LeftRightProfile ↦ (E.energy (u.toDomain E) : ℝ)
  have hP : P.Nonempty := by
    obtain ⟨u⟩ := E.nonempty_leftRightProfile
    exact ⟨_, mem_range_self u⟩
  have hB : BddBelow P := ⟨0, by rintro _ ⟨u, rfl⟩; exact (E.energy (u.toDomain E)).property⟩
  let Q : Set ℝ := {e : ℝ | ∃ u : C(CarpetPoints, ℝ), ∃ hu : continuousLp p u ∈ E.domain,
    (∀ x : CarpetPoints, (x : Plane) 0 = 0 → u x ≤ 0) ∧
    (∀ x : CarpetPoints, (x : Plane) 0 = 1 → 1 ≤ u x) ∧
    e = (E.energy ⟨continuousLp p u, hu⟩ : ℝ)}
  have hQ : P ⊆ Q := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u.toContinuousMap, u.mem_domain,
      fun x hx ↦ (u.left x hx).le, fun x hx ↦ (u.right x hx).ge, rfl⟩
  have hBQ : BddBelow Q := ⟨0, by
    rintro _ ⟨u, hu, _, _, rfl⟩
    exact (E.energy ⟨continuousLp p u, hu⟩).property⟩
  change sInf Q = sInf P
  apply le_antisymm (le_csInf hP fun _ h ↦ csInf_le hBQ (hQ h))
  apply le_csInf (hP.mono hQ)
  rintro _ ⟨u, hu, hl, hr, rfl⟩
  obtain ⟨v, hv⟩ := E.exists_profile_of_sides u hu hl hr
  exact (csInf_le hB (mem_range_self v)).trans (by exact_mod_cast hv)

theorem leftRightCapacity_eq_sInf_prescribed_values :
    E.leftRightCapacity = sInf {e : ℝ | ∃ u : C(CarpetPoints, ℝ),
      ∃ hu : continuousLp p u ∈ E.domain,
        (∀ x : CarpetPoints, (x : Plane) 0 = 0 → u x = 0) ∧
        (∀ x : CarpetPoints, (x : Plane) 0 = 1 → u x = 1) ∧
        e = (E.energy ⟨continuousLp p u, hu⟩ : ℝ)} := by
  obtain ⟨v⟩ := E.nonempty_leftRightProfile
  let P : Set ℝ := {e : ℝ | ∃ u : C(CarpetPoints, ℝ), ∃ hu : continuousLp p u ∈ E.domain,
    (∀ x : CarpetPoints, (x : Plane) 0 = 0 → u x = 0) ∧
    (∀ x : CarpetPoints, (x : Plane) 0 = 1 → u x = 1) ∧
    e = (E.energy ⟨continuousLp p u, hu⟩ : ℝ)}
  have hp (u : E.LeftRightProfile) : (E.energy (u.toDomain E) : ℝ) ∈ P :=
    ⟨u.toContinuousMap, u.mem_domain, u.left, u.right, rfl⟩
  have hB : BddBelow P := ⟨0, by
    rintro _ ⟨u, hu, _, _, rfl⟩
    exact (E.energy ⟨continuousLp p u, hu⟩).property⟩
  change E.leftRightCapacity = sInf P
  apply le_antisymm
  · unfold leftRightCapacity
    apply le_csInf ⟨_, hp v⟩
    rintro _ ⟨u, hu, hL, hR, rfl⟩
    refine csInf_le ⟨0, ?_⟩ ⟨u, hu, fun x hx ↦ (hL x hx).le, fun x hx ↦ (hR x hx).ge, rfl⟩
    rintro _ ⟨g, hg, _, _, rfl⟩
    exact (E.energy ⟨continuousLp p g, hg⟩).property
  · rw [E.leftRightCapacity_eq_sInf_profile]
    apply le_csInf ⟨_, mem_range_self v⟩
    rintro _ ⟨u, rfl⟩
    exact csInf_le hB (hp u)

theorem leftRightCapacity_pos : 0 < E.leftRightCapacity := by
  obtain ⟨b, hb, h⟩ := E.exists_pos_le_energy_profile
  obtain ⟨u⟩ := E.nonempty_leftRightProfile
  rw [E.leftRightCapacity_eq_sInf_profile]
  exact hb.trans_le (le_csInf ⟨_, mem_range_self u⟩ (by rintro _ ⟨v, rfl⟩; exact h v))

theorem leftRightCapacity_le_energy (u : E.LeftRightProfile) :
    E.leftRightCapacity ≤ (E.energy (u.toDomain E) : ℝ) := by
  rw [E.leftRightCapacity_eq_sInf_profile]
  exact csInf_le ⟨0, by rintro _ ⟨v, rfl⟩; exact (E.energy (v.toDomain E)).property⟩
    (mem_range_self u)

/-- The capacity lower bound forces the scaling factor bound in Lemma 3.1. -/
theorem half_le_scalingFactor : (1 / 2 : ℝ) ≤ E.scalingFactor := by
  by_contra! h
  have hpos := E.leftRightCapacity_pos
  let a := 2 * E.scalingFactor
  have ha : 0 < a := mul_pos zero_lt_two E.isScalingFactor_scalingFactor.1
  have halt : a < 1 := by dsimp [a]; linarith only [h]
  have hsmall : E.leftRightCapacity < E.leftRightCapacity / a := by
    apply (lt_div_iff₀ ha).mpr
    exact mul_lt_of_lt_one_right hpos halt
  let P := range fun u : E.LeftRightProfile ↦ (E.energy (u.toDomain E) : ℝ)
  have hInf : E.leftRightCapacity = sInf P := E.leftRightCapacity_eq_sInf_profile
  obtain ⟨u₀⟩ := E.nonempty_leftRightProfile
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := exists_lt_of_csInf_lt
    (show P.Nonempty from ⟨_, mem_range_self u₀⟩) (hInf ▸ hsmall)
  have hB : BddBelow P := ⟨0, by rintro _ ⟨v, rfl⟩; exact (E.energy (v.toDomain E)).property⟩
  have hs : E.leftRightCapacity ≤ (E.energy ((E.spliceProfile u).toDomain E) : ℝ) :=
    hInf.trans_le (csInf_le hB (mem_range_self (E.spliceProfile u)))
  rw [E.energy_spliceProfile] at hs
  exact not_lt_of_ge hs (by
    have h' : (E.energy (u.toDomain E) : ℝ) * a < sInf P := (lt_div_iff₀ ha).mp hu
    change a * (E.energy (u.toDomain E) : ℝ) < E.leftRightCapacity
    rw [mul_comm a, hInf]
    exact h')

end CarpetEnergy.SelfSimilarPEnergy
