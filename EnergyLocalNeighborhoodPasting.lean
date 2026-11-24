import EnergyLocalContinuousPullback

/-!
# Pasting a locally continuous domain profile

The actual paste uses only the inner cells. An identification of
the larger neighborhoods still records the pullback correspondence
needed when testing harmonicity.
-/

open Function Set

namespace CarpetEnergy

/-- The larger neighborhood identification maps each smaller
neighborhood to its counterpart. -/
noncomputable def neighborhoodInnerImage {n m r s : ℕ}
    (w : Fin n → Fin 8) (u : Fin m → Fin 8) (h : neighborhoodShape w r = neighborhoodShape u r)
    (hs : s ≤ r) (a : {a // a ∈ cellNeighborhood w s}) : {a // a ∈ cellNeighborhood u s} :=
  let a' := ⟨a.val, cellNeighborhood_mono w hs a.property⟩
  ⟨(neighborhoodEquiv w u h a').val, neighborhoodEquiv_mem_cellNeighborhood w u h hs a' a.property⟩

namespace SelfSimilarPEnergy

open SelfSimilarComponent MeasureTheory

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 2100000 in
theorem exists_neighborhood_paste_local {n m r s : ℕ}
    (w : Fin n → Fin 8) (u : Fin m → Fin 8) (h : neighborhoodShape w r = neighborhoodShape u r)
    (hs : s ≤ r) (f : E.domain) (F : C(wordCellUnion (cellNeighborhood u s), ℝ))
    (hF : ∀ᵐ x ∂carpetMeasure.restrict (wordCellUnion (cellNeighborhood u s)),
      ∀ hx : x ∈ wordCellUnion (cellNeighborhood u s), F ⟨x, hx⟩ = (f : CarpetLp p) x)
    (k : E.continuousCore) (hk : ∀ x ∉ wordNeighborhoodOpen w s, k.val x = 0) :
    ∃ (g : E.continuousCore) (P : {b // b ∈ cellNeighborhood u s} → E.continuousCore),
      (∀ b, E.continuousCoreToDomain (P b) = E.pullbackWord (List.ofFn b.val) f) ∧
      (∀ b x, (P b).val x = F ⟨wordMap (List.ofFn b.val) x, mem_iUnion.mpr
        ⟨b.val, mem_iUnion.mpr ⟨b.property, mem_range_self x⟩⟩⟩) ∧
      (∀ a : {a // a ∈ cellNeighborhood w s}, E.wordPullbackCore (List.ofFn a.val) g =
        E.mulCore (E.wordPullbackCore (List.ofFn a.val) k) (P (neighborhoodInnerImage w u h hs a))) ∧
      (∀ a ∉ cellNeighborhood w s, E.wordPullbackCore (List.ofFn a) g = 0) := by
  classical
  let W := wordCellUnion (cellNeighborhood u s)
  have hsub (b : {b // b ∈ cellNeighborhood u s}) : range (wordMap (List.ofFn b.val)) ⊆ W :=
    fun _ hx ↦ mem_iUnion.mpr ⟨b.val, mem_iUnion.mpr ⟨b.property, hx⟩⟩
  choose P hP hPv using fun b : {b // b ∈ cellNeighborhood u s} ↦
    E.exists_core_pullback_of_local_version (measurableSet_wordCellUnion _) f F hF
      (List.ofFn b.val) (hsub b)
  let e (a : {a // a ∈ cellNeighborhood w s}) := neighborhoodInnerImage w u h hs a
  let profile (a : Fin n → Fin 8) : E.continuousCore :=
    if ha : a ∈ cellNeighborhood w s then
      E.mulCore (E.wordPullbackCore (List.ofFn a) k) (P (e ⟨a, ha⟩))
    else 0
  have hp (a : {a // a ∈ cellNeighborhood w s}) (x : CarpetPoints) :
      (profile a.val).val x =
        k.val (wordMap (List.ofFn a.val) x) * F ⟨wordMap (List.ofFn (e a).val) x,
          hsub (e a) (mem_range_self x)⟩ := by
    dsimp only [profile]
    rw [dite_eq_left a.property, E.mulCore_apply, E.wordPullbackCore_apply, hPv]
  have hz (a : Fin n → Fin 8) (ha : a ∉ cellNeighborhood w s) (x : CarpetPoints) :
      (profile a).val x = 0 := by
    dsimp only [profile]
    rw [dite_eq_right ha]
    rfl
  have hglue (a b : Fin n → Fin 8) (x y : CarpetPoints)
      (he : wordMap (List.ofFn a) x = wordMap (List.ofFn b) y) :
      (profile a).val x = (profile b).val y := by
    by_cases ha : a ∈ cellNeighborhood w s
    · rw [hp ⟨a, ha⟩ x]
      by_cases hb : b ∈ cellNeighborhood w s
      · rw [hp ⟨b, hb⟩ y, he]
        let a' : {a // a ∈ cellNeighborhood w r} := ⟨a, cellNeighborhood_mono w hs ha⟩
        let b' : {a // a ∈ cellNeighborhood w r} := ⟨b, cellNeighborhood_mono w hs hb⟩
        have hr := congrArg (fun z : CarpetPoints ↦ neighborhoodRescale w u z) he
        rw [neighborhoodRescale_wordMap w u h a' x, neighborhoodRescale_wordMap w u h b' y] at hr
        have hEq :
            (⟨wordMap (List.ofFn (e ⟨a, ha⟩).val) x, hsub _ (mem_range_self x)⟩ : W) =
              ⟨wordMap (List.ofFn (e ⟨b, hb⟩).val) y, hsub _ (mem_range_self y)⟩ :=
          Subtype.ext (Subtype.ext hr)
        rw [hEq]
      · rw [he, hk _ (wordMap_notMem_wordNeighborhoodOpen hb y), zero_mul, hz b hb y]
    · rw [hz a ha x]
      by_cases hb : b ∈ cellNeighborhood w s
      · rw [hp ⟨b, hb⟩ y, ← he, hk _ (wordMap_notMem_wordNeighborhoodOpen ha x), zero_mul]
      · rw [hz b hb y]
  obtain ⟨g, hg, hprofile⟩ := E.zeroComponent.exists_continuousKernel_cellwise n
    (fun a ↦ (profile a).val) (fun a ↦ ⟨(profile a).property, rfl⟩) hglue
  let G : E.continuousCore := ⟨g, hg.choose⟩
  have hw (a : Fin n → Fin 8) : E.wordPullbackCore (List.ofFn a) G = profile a := by
    apply Subtype.ext
    ext x
    exact hprofile a x
  refine ⟨G, P, hP, hPv, fun a ↦ ?_, fun a ha ↦ ?_⟩
  · rw [hw]
    exact dite_eq_left a.property
  · rw [hw]
    exact dite_eq_right ha

end SelfSimilarPEnergy

end CarpetEnergy
