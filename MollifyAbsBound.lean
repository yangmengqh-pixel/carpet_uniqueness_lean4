import SmoothMollification

/-!
# Absolute values under a nonnegative mollifier
-/

open ContinuousLinearMap Filter MeasureTheory
open scoped Convolution

namespace CarpetEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] 
  [HasContDiffBump X] [MeasurableSpace X]
variable {μ : Measure X}

theorem abs_mollify_le_mollify_abs {f : X → ℝ}
    (n : ℕ) (x : X) :
    |mollify μ n f x| ≤ mollify μ n (fun y ↦ |f y|) x := by
  let K := (mollifierBump (X := X) n).normed μ
  have hK (y : X) : 0 ≤ K y := (mollifierBump n).nonneg_normed y
  change |∫ y, K y * f (x - y) ∂μ| ≤ ∫ y, K y * |f (x - y)| ∂μ
  refine abs_integral_le_integral_abs.trans_eq ?_
  exact integral_congr_ae (Eventually.of_forall fun y ↦ by
    change |K y * f (x - y)| = K y * |f (x - y)|
    rw [abs_mul, abs_of_nonneg (hK y)])

end CarpetEnergy
