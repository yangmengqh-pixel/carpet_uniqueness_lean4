import CarpetCellCrossings
import CarpetCrossingCapacity

/-!
# Energy of two components crossing the corner cells

Each component crossing all four corner interiors crosses at least three
side cells. Two such components share at least two side cells. Capacity on
those two cells gives the energy lower bound in Lemma 3.9.
-/

open Function MeasureTheory Set
open scoped BigOperators NNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem exists_two_common_of_pairwise_or {P Q : Fin 4 → Prop}
    (hP : ∀ i j, i ≠ j → P i ∨ P j) (hQ : ∀ i j, i ≠ j → Q i ∨ Q j) :
    ∃ i j, i ≠ j ∧ (P i ∧ Q i) ∧ (P j ∧ Q j) := by
  classical
  let bad (R : Fin 4 → Prop) := Finset.univ.filter fun i ↦ ¬ R i
  have hbad (R : Fin 4 → Prop) (hR : ∀ i j, i ≠ j → R i ∨ R j) : (bad R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra h
    exact (hR i j h).elim (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  let B := bad P ∪ bad Q
  let G := Finset.univ \ B
  have hB : B.card ≤ 2 :=
    (Finset.card_union_le _ _).trans (add_le_add (hbad P hP) (hbad Q hQ))
  have hc : G.card + B.card = 4 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < G.card by omega)
  have good {i} (hi : i ∈ G) : P i ∧ Q i := by
    have hi' := (Finset.mem_sdiff.mp hi).2
    simpa only [B, Finset.mem_union, bad, Finset.mem_filter, Finset.mem_univ, true_and,
      not_or, not_not] using hi'
  exact ⟨i, j, hij, good hi, good hj⟩

private theorem lipschitzWith_rescale (a : ℝ) {d : ℝ} (hd : 0 < d) :
    LipschitzWith d⁻¹.toNNReal (fun t : ℝ ↦ (t - a) / d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.mpr hd.le)]
  rw [show (x - a) / d - (y - a) / d = d⁻¹ * (x - y) by ring,
    abs_mul, abs_of_pos (inv_pos.mpr hd)]

private theorem orientedSidePullback_energy (f : C(CarpetPoints, ℝ))
    (hf : continuousLp p f ∈ E.domain) (i : Fin 4) :
    ∃ h : continuousLp p (f.comp ⟨orientedSideMap i, continuous_orientedSideMap i⟩) ∈ E.domain,
      E.energy ⟨continuousLp p (f.comp ⟨orientedSideMap i, continuous_orientedSideMap i⟩), h⟩ =
        E.energy (E.pullback (sideCell i) ⟨continuousLp p f, hf⟩) := by
  let v : C(CarpetPoints, ℝ) := f.comp ⟨cellMap (sideCell i), continuous_cellMap (sideCell i)⟩
  let g := E.pullback (sideCell i) ⟨continuousLp p f, hf⟩
  have hg : (g : CarpetLp p) = continuousLp p v := cellPullback_continuousLp p _ f
  obtain ⟨u, hu, heu⟩ := E.symmetry (sideOrientation i) g
  let w : C(CarpetPoints, ℝ) := f.comp ⟨orientedSideMap i, continuous_orientedSideMap i⟩
  have hwu : continuousLp p w = (u : CarpetLp p) := by
    apply Lp.ext
    have hv := (measurePreserving_carpetSymmetry (sideOrientation i)).quasiMeasurePreserving.ae_eq_comp
      (continuousLp_ae_eq p v)
    rw [← hg] at hv
    exact (continuousLp_ae_eq p w).trans (hu.trans hv).symm
  have hw := hwu.symm ▸ u.property
  exact ⟨hw, (congrArg E.energy (Subtype.ext hwu)).trans heu⟩

private theorem sideCrossings_energy_lower_bound
    (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain)
    {a b : ℝ} (hab : a < b) (i : Fin 4)
    (hA : HasSideCrossing {x | b < f x} i) (hZ : HasSideCrossing {x | f x < a} i) :
    (b - a) ^ p * E.leftRightCapacity ≤
      (E.energy (E.pullback (sideCell i) ⟨continuousLp p f, hf⟩) : ℝ) := by
  let d := b - a
  have hd : 0 < d := sub_pos.mpr hab
  let T := orientedSideMap i
  let v := f.comp ⟨T, continuous_orientedSideMap i⟩
  obtain ⟨hv, hve⟩ := E.orientedSidePullback_energy f hf i
  let φ (t : ℝ) := min (max ((t - a) / d) 0) 1
  have hφ : LipschitzWith d⁻¹.toNNReal φ := (lipschitzWith_rescale a hd).max_const 0 |>.min_const 1
  obtain ⟨u, hu, huv, hue⟩ := E.exists_continuous_comp_energy_le_mul v hv hφ
  obtain ⟨A, hA, hAc, hAp, ⟨lA, hlA, hlFace⟩, ⟨rA, hrA, hrFace⟩⟩ := hA
  obtain ⟨Z, hZ, hZc, hZp, ⟨lZ, hlZ, hlZFace⟩, ⟨rZ, hrZ, hrZFace⟩⟩ := hZ
  have hTem : Topology.IsClosedEmbedding T :=
    (continuous_orientedSideMap i).isClosedEmbedding (injective_orientedSideMap i)
  have hAT : A ⊆ range T := by rw [show range T = _ from range_orientedSideMap i]; exact hA.trans inter_subset_right
  have hZT : Z ⊆ range T := by rw [show range T = _ from range_orientedSideMap i]; exact hZ.trans inter_subset_right
  obtain ⟨l, hl⟩ := hAT hlA
  obtain ⟨r, hr⟩ := hAT hrA
  obtain ⟨l', hl'⟩ := hZT hlZ
  obtain ⟨r', hr'⟩ := hZT hrZ
  have face {x y : CarpetPoints} {k : Fin 2} (hxy : T x = y) (hy : y ∈ sideFace i k) :
      (x : Plane) 0 = (k.val : ℝ) := by
    apply (orientedSideMap_mem_sideFace_iff i k x).mp
    change T x ∈ sideFace i k
    rwa [hxy]
  have huA (x : CarpetPoints) (hx : x ∈ T ⁻¹' A) : u x = 1 := by
    have hh : b < v x := (hA hx).1
    have hdiv : 1 ≤ (v x - a) / d := (le_div_iff₀ hd).mpr (by dsimp only [d]; linarith)
    rw [huv]
    exact min_eq_right (hdiv.trans (le_max_left _ _))
  have huZ (x : CarpetPoints) (hx : x ∈ T ⁻¹' Z) : u x = 0 := by
    have hh : v x < a := (hZ hx).1
    have hdiv : (v x - a) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh.le) hd.le
    rw [huv]
    change min (max ((v x - a) / d) 0) 1 = 0
    rw [max_eq_right hdiv, min_eq_left zero_le_one]
  have hcapacity := E.leftRightCapacity_le_of_crossing_sets u hu
    (hTem.isCompact_preimage hAc) (hTem.isCompact_preimage hZc)
    (hAp.preimage_of_isClosedMap hTem.injective hTem.isClosedMap hAT)
    (hZp.preimage_of_isClosedMap hTem.injective hTem.isClosedMap hZT)
    (show T l ∈ A from hl.symm ▸ hlA) (show T r ∈ A from hr.symm ▸ hrA)
    (show T l' ∈ Z from hl'.symm ▸ hlZ) (show T r' ∈ Z from hr'.symm ▸ hrZ)
    (by simpa using face hl hlFace) (by simpa using face hr hrFace)
    (by simpa using face hl' hlZFace) (by simpa using face hr' hrZFace) huA huZ
  have hreal := hcapacity.trans hue
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hd.le), Real.inv_rpow hd.le, hve, ← div_eq_inv_mul] at hreal
  simpa only [mul_comm E.leftRightCapacity (d ^ p)] using
    (le_div_iff₀ (Real.rpow_pos_of_pos hd p)).mp hreal

/-- Lemma 3.9. Components of the upper and lower level sets that each meet all
four corner interiors force a positive energy lower bound. -/
theorem energy_ge_of_opposite_components (f : C(CarpetPoints, ℝ))
    (hf : continuousLp p f ∈ E.domain) {a b : ℝ} (hab : a < b) (x y : CarpetPoints)
    (hx : ∀ k : Fin 4, (connectedComponentIn {x | b < f x} x ∩ cellOpenPart (cornerCell k)).Nonempty)
    (hy : ∀ k : Fin 4, (connectedComponentIn {x | f x < a} y ∩ cellOpenPart (cornerCell k)).Nonempty) :
    2 * E.scalingFactor * (b - a) ^ p * E.leftRightCapacity ≤
      (E.energy ⟨continuousLp p f, hf⟩ : ℝ) := by
  let U := connectedComponentIn {x | b < f x} x
  let V := connectedComponentIn {x | f x < a} y
  have hU : IsOpen U := (isOpen_lt continuous_const f.continuous).connectedComponentIn
  have hV : IsOpen V := (isOpen_lt f.continuous continuous_const).connectedComponentIn
  obtain ⟨i, j, hij, ⟨hiU, hiV⟩, ⟨hjU, hjV⟩⟩ := exists_two_common_of_pairwise_or
    (fun _ _ h ↦ hasSideCrossing_or_of_isOpen hU isPreconnected_connectedComponentIn hx h)
    (fun _ _ h ↦ hasSideCrossing_or_of_isOpen hV isPreconnected_connectedComponentIn hy h)
  have lift {A B : Set CarpetPoints} {i : Fin 4} (hAB : A ⊆ B) (h : HasSideCrossing A i) :
      HasSideCrossing B i := by
    obtain ⟨K, hK, hc, hp, h₀, h₁⟩ := h
    exact ⟨K, hK.trans (inter_subset_inter_left _ hAB), hc, hp, h₀, h₁⟩
  have lower (i : Fin 4) (hiU : HasSideCrossing U i) (hiV : HasSideCrossing V i) :=
    E.sideCrossings_energy_lower_bound f hf hab i
      (lift (connectedComponentIn_subset _ _) hiU) (lift (connectedComponentIn_subset _ _) hiV)
  let g (k : Fin 8) := (E.energy (E.pullback k ⟨continuousLp p f, hf⟩) : ℝ)
  have hg : ∀ k : Fin 8, 0 ≤ g k := fun _ ↦ NNReal.coe_nonneg _
  have hpair : g (sideCell i) + g (sideCell j) ≤ ∑ k, g k := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({sideCell i, sideCell j} : Finset (Fin 8)))
      (fun k _ _ ↦ hg k)
    rwa [Finset.sum_pair (fun h ↦ hij (sideCell_injective h))] at hle
  have hsum : (b - a) ^ p * E.leftRightCapacity + (b - a) ^ p * E.leftRightCapacity ≤ ∑ k, g k :=
    (add_le_add (lower i hiU hiV) (lower j hjU hjV)).trans hpair
  have hρ := E.isScalingFactor_scalingFactor
  rw [hρ.2]
  calc
    _ = E.scalingFactor * ((b - a) ^ p * E.leftRightCapacity +
        (b - a) ^ p * E.leftRightCapacity) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hρ.1.le

end CarpetEnergy.SelfSimilarPEnergy
