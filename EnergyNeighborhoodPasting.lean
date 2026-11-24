import CarpetNeighborhoodRescaling
import EnergyCoreProduct
import EnergyLocalMidpointDeficit

/-!
# Pasting profiles across equal-shape neighborhoods

Corresponding cell pullbacks are transferred without an orientation
change. Multiplying by a cutoff makes the paste compatible with all
cells outside the target neighborhood.
-/

open Set

namespace CarpetEnergy.SelfSimilarPEnergy

open SelfSimilarComponent

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1000000 in
/-- Rescale a source profile into an equal-shape target neighborhood
and multiply it by a target cutoff. -/
theorem exists_neighborhood_paste {n m r : ℕ} (w : Fin n → Fin 8) (u : Fin m → Fin 8)
    (h : neighborhoodShape w r = neighborhoodShape u r)
    (f k : E.continuousCore) (hk : ∀ x ∉ wordNeighborhoodOpen w r, k.val x = 0) :
    ∃ g : E.continuousCore,
      (∀ v : {v // v ∈ cellNeighborhood w r},
        E.wordPullbackCore (List.ofFn v.val) g =
          E.mulCore (E.wordPullbackCore (List.ofFn v.val) k)
            (E.wordPullbackCore (List.ofFn (neighborhoodEquiv w u h v).val) f)) ∧
      (∀ v ∉ cellNeighborhood w r, E.wordPullbackCore (List.ofFn v) g = 0) := by
  classical
  let profile (v : Fin n → Fin 8) : E.continuousCore :=
    if hv : v ∈ cellNeighborhood w r then
      E.mulCore (E.wordPullbackCore (List.ofFn v) k)
        (E.wordPullbackCore (List.ofFn (neighborhoodEquiv w u h ⟨v, hv⟩).val) f)
    else 0
  have hp (v : {v // v ∈ cellNeighborhood w r}) (x : CarpetPoints) :
      (profile v.val).val x = k.val (wordMap (List.ofFn v.val) x) *
        f.val (wordMap (List.ofFn (neighborhoodEquiv w u h v).val) x) := by
    dsimp only [profile]
    rw [dite_eq_left v.property, E.mulCore_apply, E.wordPullbackCore_apply, E.wordPullbackCore_apply]
  have hz (v : Fin n → Fin 8) (hv : v ∉ cellNeighborhood w r) (x : CarpetPoints) :
      (profile v).val x = 0 := by
    dsimp only [profile]
    rw [dite_eq_right hv]
    rfl
  have heq (a b : Fin n → Fin 8) (x y : CarpetPoints)
      (he : wordMap (List.ofFn a) x = wordMap (List.ofFn b) y) :
      (profile a).val x = (profile b).val y := by
    by_cases ha : a ∈ cellNeighborhood w r
    · rw [hp ⟨a, ha⟩ x]
      by_cases hb : b ∈ cellNeighborhood w r
      · rw [hp ⟨b, hb⟩ y, he]
        have hr := congrArg (fun z : CarpetPoints ↦ neighborhoodRescale w u z) he
        rw [neighborhoodRescale_wordMap w u h ⟨a, ha⟩ x,
          neighborhoodRescale_wordMap w u h ⟨b, hb⟩ y] at hr
        rw [show wordMap (List.ofFn (neighborhoodEquiv w u h ⟨a, ha⟩).val) x =
          wordMap (List.ofFn (neighborhoodEquiv w u h ⟨b, hb⟩).val) y from Subtype.ext hr]
      · rw [he, hk _ (wordMap_notMem_wordNeighborhoodOpen hb y), zero_mul, hz b hb y]
    · rw [hz a ha x]
      by_cases hb : b ∈ cellNeighborhood w r
      · rw [hp ⟨b, hb⟩ y, ← he, hk _ (wordMap_notMem_wordNeighborhoodOpen ha x), zero_mul]
      · rw [hz b hb y]
  obtain ⟨g, hg, hprofile⟩ := E.zeroComponent.exists_continuousKernel_cellwise n
    (fun v ↦ (profile v).val) (fun v ↦ ⟨(profile v).property, rfl⟩) heq
  let G : E.continuousCore := ⟨g, hg.choose⟩
  have hw (v : Fin n → Fin 8) : E.wordPullbackCore (List.ofFn v) G = profile v := by
    apply Subtype.ext
    ext x
    exact hprofile v x
  refine ⟨G, ?_, ?_⟩
  · intro v
    rw [hw]
    exact dite_eq_left v.property
  · intro v hv
    rw [hw]
    exact dite_eq_right hv

end CarpetEnergy.SelfSimilarPEnergy
