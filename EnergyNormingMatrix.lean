import EnergyRootUniformConvex

/-!
# Strict cross bounds for norming functionals

A norming functional cannot also attain its norm at an independent
unit profile. The two off-diagonal entries of the normalized
first-variation matrix therefore have product of absolute value
strictly less than one.
-/

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private noncomputable def continuousCoreRoot : Seminorm ℝ E.continuousCore :=
  E.rootSeminorm.comp E.continuousCoreToDomain

private theorem continuousCoreRoot_mid_lt (f g : E.continuousCore)
    (hf : E.continuousCoreRoot f ≤ 1) (hg : E.continuousCoreRoot g ≤ 1)
    (h : 0 < E.continuousCoreRoot (f - g)) :
    E.continuousCoreRoot ((1 / 2 : ℝ) • (f + g)) < 1 :=
  E.root_midpoint_lt_one f g hf hg h

theorem abs_linear_le_root_strict (f g : E.continuousCore)
    (ℓ : E.continuousCore →ₗ[ℝ] ℝ)
    (hf : E.rootSeminorm (E.continuousCoreToDomain f) ≤ 1)
    (hg : E.rootSeminorm (E.continuousCoreToDomain g) ≤ 1)
    (h₀ : 0 < E.rootSeminorm (E.continuousCoreToDomain (f - g)))
    (h₁ : 0 < E.rootSeminorm (E.continuousCoreToDomain (f + g)))
    (hn : ℓ f = 1)
    (hℓ : ∀ z, |ℓ z| ≤ E.rootSeminorm (E.continuousCoreToDomain z)) :
    |ℓ g| < 1 := by
  let R := E.continuousCoreRoot
  have hbound : |ℓ g| ≤ 1 := (hℓ g).trans hg
  by_contra! h
  have he : |ℓ g| = 1 := le_antisymm hbound h
  have hsign : ℓ g = 1 ∨ ℓ g = -1 := by
    rcases le_total 0 (ℓ g) with hpos | hneg
    · exact Or.inl (by rwa [abs_of_nonneg hpos] at he)
    · exact Or.inr (by rw [abs_of_nonpos hneg] at he; linarith)
  have impossible (z : E.continuousCore) (hz : R z ≤ 1) (hd : 0 < R (f - z))
      (hz' : ℓ z = 1) : False := by
    have hr := E.continuousCoreRoot_mid_lt f z hf hz hd
    have hm := hℓ ((1 / 2 : ℝ) • (f + z))
    change |ℓ ((1 / 2 : ℝ) • (f + z))| ≤ R ((1 / 2 : ℝ) • (f + z)) at hm
    rw [map_smul, map_add, hn, hz', smul_eq_mul, show (1 / 2 : ℝ) * (1 + 1) = 1 by norm_num,
      abs_one] at hm
    exact hr.not_ge hm
  rcases hsign with hpos | hneg
  · exact impossible g hg h₀ hpos
  · apply impossible (-g)
    · rw [map_neg_eq_map R]
      exact hg
    · rw [sub_neg_eq_add]
      exact h₁
    · simp [hneg]

/-- The determinant of the two normalized first-variation rows is
nonzero whenever the two unit profiles are independent. -/
theorem norming_matrix_det_ne_zero (f g : E.continuousCore)
    (ℓ₁ ℓ₂ : E.continuousCore →ₗ[ℝ] ℝ)
    (hf : E.rootSeminorm (E.continuousCoreToDomain f) ≤ 1)
    (hg : E.rootSeminorm (E.continuousCoreToDomain g) ≤ 1)
    (h₀ : 0 < E.rootSeminorm (E.continuousCoreToDomain (f - g)))
    (h₁ : 0 < E.rootSeminorm (E.continuousCoreToDomain (f + g)))
    (hn₁ : ℓ₁ f = 1) (hn₂ : ℓ₂ g = 1)
    (hℓ₁ : ∀ z, |ℓ₁ z| ≤ E.rootSeminorm (E.continuousCoreToDomain z))
    (hℓ₂ : ∀ z, |ℓ₂ z| ≤ E.rootSeminorm (E.continuousCoreToDomain z)) :
    ℓ₁ f * ℓ₂ g - ℓ₁ g * ℓ₂ f ≠ 0 := by
  have h₁₂ := E.abs_linear_le_root_strict f g ℓ₁ hf hg h₀ h₁ hn₁ hℓ₁
  let R := E.continuousCoreRoot
  have h₀' : 0 < R (g - f) := by rw [map_sub_rev]; exact h₀
  have h₁' : 0 < R (g + f) := by rw [add_comm]; exact h₁
  have h₂₁ := E.abs_linear_le_root_strict g f ℓ₂ hg hf h₀' h₁' hn₂ hℓ₂
  have hp : |ℓ₁ g * ℓ₂ f| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right h₁₂.le (abs_nonneg _)).trans_lt (by rwa [one_mul])
  intro h
  rw [hn₁, hn₂, one_mul] at h
  rw [← sub_eq_zero.mp h, abs_one] at hp
  exact lt_irrefl _ hp

end CarpetEnergy.SelfSimilarPEnergy
