import EnergyVariationCells
import EnergyCoreProduct
import EnergyGlobalNormalization
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Product first variations via cell refinement

On a small cell the product differs from its affine expansion by the
product of the two oscillations. The summed variation of that error
tends to zero.
-/

open Filter Set
open scoped BigOperators Topology ENNReal

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem rootSeminorm_add_constant (f : E.domain) (a : ℝ) :
    E.rootSeminorm (f + ⟨constantLp p a, E.constant_mem a⟩) = E.rootSeminorm f := by
  rw [E.rootSeminorm_apply, E.add_constant, ← E.rootSeminorm_apply]

private theorem variation_constCore_eq_zero (h : E.HasLinearFirstVariations)
    (f : E.domain) (a : ℝ) :
    E.variation h f (E.continuousCoreToDomain (E.constCore a)) = 0 := by
  have hr : E.rootSeminorm (E.continuousCoreToDomain (E.constCore a)) = 0 := by
    rw [E.continuousCoreToDomain_constCore, E.rootSeminorm_apply,
      (E.zero_iff_constant _).mpr ⟨a, rfl⟩, NNReal.coe_zero,
      Real.zero_rpow (inv_ne_zero (zero_lt_one.trans E.one_lt_p).ne')]
  have hb := E.abs_variation_le h f (E.continuousCoreToDomain (E.constCore a))
  rw [hr, mul_zero] at hb
  exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))

private theorem rootSeminorm_sub_constCore (f : E.continuousCore) (a : ℝ) :
    E.rootSeminorm (E.continuousCoreToDomain (f - E.constCore a)) =
      E.rootSeminorm (E.continuousCoreToDomain f) := by
  have he : f - E.constCore a = f + E.constCore (-a) := by
    apply Subtype.ext
    ext x
    change f.val x - a = f.val x + -a
    exact sub_eq_add_neg _ _
  rw [he, map_add, E.continuousCoreToDomain_constCore, E.rootSeminorm_add_constant]

/-- Replacing a product on a cell by its first-order expansion has a
first-variation error controlled by the two oscillations. -/
theorem abs_variation_product_error_le (h : E.HasLinearFirstVariations)
    (f : E.domain) (g k : E.continuousCore) (a b : ℝ) :
    |E.variation h f (E.continuousCoreToDomain (E.mulCore g k)) -
        (a * E.variation h f (E.continuousCoreToDomain k) +
          b * E.variation h f (E.continuousCoreToDomain g))| ≤
      (E.rootSeminorm f) ^ (p - 1) *
        (2 * (‖(k - E.constCore b).val‖ * E.rootSeminorm (E.continuousCoreToDomain g) +
          ‖(g - E.constCore a).val‖ * E.rootSeminorm (E.continuousCoreToDomain k))) := by
  let G := g - E.constCore a
  let K := k - E.constCore b
  have he : E.mulCore G K =
      E.mulCore g k - (a • k + b • g) + E.constCore (a * b) := by
    apply Subtype.ext
    ext x
    change (g.val x - a) * (k.val x - b) =
      g.val x * k.val x - (a * k.val x + b * g.val x) + a * b
    ring
  have hh := E.abs_variation_le h f (E.continuousCoreToDomain (E.mulCore G K))
  have hb := E.rootSeminorm_mulCore_le_cross G K
  change E.rootSeminorm (E.continuousCoreToDomain (E.mulCore G K)) ≤
    2 * (‖K.val‖ * E.rootSeminorm (E.continuousCoreToDomain (g - E.constCore a)) +
      ‖G.val‖ * E.rootSeminorm (E.continuousCoreToDomain (k - E.constCore b))) at hb
  rw [E.rootSeminorm_sub_constCore, E.rootSeminorm_sub_constCore] at hb
  have hbound := hh.trans (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (apply_nonneg _ _) _))
  rw [he] at hbound
  simp only [map_add, map_sub, map_smul, smul_eq_mul, E.variation_constCore_eq_zero h f, add_zero] at hbound
  exact hbound

end CarpetEnergy.SelfSimilarPEnergy
