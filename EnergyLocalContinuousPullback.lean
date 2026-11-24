import EnergyNeighborhoodPasting

/-!
# Pulling back a local continuous version to a cell

A continuous version on a measurable set containing a cell
represents the word pullback, by quasi-measure preservation.
-/

open Filter Function MeasureTheory Set

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

set_option maxHeartbeats 1050000 in
theorem exists_core_pullback_of_local_version {W : Set CarpetPoints} (hW : MeasurableSet W)
    (f : E.domain) (F : C(W, ℝ))
    (hF : ∀ᵐ x ∂carpetMeasure.restrict W, ∀ hx : x ∈ W, F ⟨x, hx⟩ = (f : CarpetLp p) x)
    (w : List (Fin 8)) (hw : range (wordMap w) ⊆ W) :
    ∃ u : E.continuousCore, E.continuousCoreToDomain u = E.pullbackWord w f ∧
      ∀ x, u.val x = F ⟨wordMap w x, hw (mem_range_self x)⟩ := by
  let T : C(CarpetPoints, W) :=
    ⟨fun x ↦ ⟨wordMap w x, hw (mem_range_self x)⟩, (continuous_wordMap w).subtype_mk _⟩
  let u := F.comp T
  have hu : continuousLp p u = (E.pullbackWord w f : CarpetLp p) := by
    apply Lp.ext
    have h := (quasiMeasurePreserving_wordMap w).ae ((ae_restrict_iff' hW).mp hF)
    filter_upwards [h, continuousLp_ae_eq p u, E.pullbackWord_isLpPullback w f] with x hx hu hf
    exact hu.trans ((hx (hw (mem_range_self x)) (hw (mem_range_self x))).trans hf.symm)
  have hm : continuousLp p u ∈ E.domain := hu.symm ▸ (E.pullbackWord w f).property
  let v : E.continuousCore := ⟨u, hm⟩
  exact ⟨v, Subtype.ext hu, fun _ ↦ rfl⟩

end CarpetEnergy.SelfSimilarPEnergy
