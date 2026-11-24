import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Finite mixed inequalities for nonnegative arrays

Minkowski gives subadditivity above exponent one. Applying it to
transposed arrays of powers gives superadditivity below exponent
one. These are the two finite summation inequalities for generalized
p-contractions.
-/

open scoped BigOperators

namespace CarpetEnergy

variable {I J : Type*} [Fintype I]

/-- The power sum to the reciprocal exponent, for nonnegative data. -/
noncomputable def finitePowerSum (r : ℝ) (a : I → ℝ) : ℝ :=
  (∑ i, a i ^ r) ^ r⁻¹

theorem continuous_finitePowerSum {r : ℝ} (hr : 0 ≤ r) :
    Continuous (finitePowerSum (I := I) r) :=
  (Real.continuous_rpow_const (inv_nonneg.mpr hr)).comp
    (continuous_finsetSum _ fun i _ ↦ (Real.continuous_rpow_const hr).comp (continuous_apply i))

theorem finitePowerSum_nonneg (r : ℝ) {a : I → ℝ} (ha : ∀ i, 0 ≤ a i) :
    0 ≤ finitePowerSum r a :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i) _) _

theorem finitePowerSum_mono {r : ℝ} (hr : 0 < r) {a b : I → ℝ}
    (ha : ∀ i, 0 ≤ a i) (h : ∀ i, a i ≤ b i) :
    finitePowerSum r a ≤ finitePowerSum r b := by
  unfold finitePowerSum
  exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i) _)
    (Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (ha i) (h i) hr.le) (inv_nonneg.mpr hr.le)

theorem finitePowerSum_mul_const {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c)
    {a : I → ℝ} (ha : ∀ i, 0 ≤ a i) :
    finitePowerSum r (fun i ↦ c * a i) = c * finitePowerSum r a := by
  unfold finitePowerSum
  simp_rw [Real.mul_rpow hc (ha _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg hc _) (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i) _),
    Real.rpow_rpow_inv hc hr.ne']

theorem finitePowerSum_sum_le {r : ℝ} (hr : 1 ≤ r) (s : Finset J) (a : J → I → ℝ)
    (ha : ∀ j i, 0 ≤ a j i) :
    finitePowerSum r (fun i ↦ ∑ j ∈ s, a j i) ≤ ∑ j ∈ s, finitePowerSum r (a j) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, finitePowerSum, Real.zero_rpow (zero_lt_one.trans_le hr).ne',
      Real.zero_rpow (inv_ne_zero (zero_lt_one.trans_le hr).ne'), Finset.sum_const_zero, le_rfl]
  | insert j s hjs ih =>
    simp only [Finset.sum_insert hjs]
    apply le_trans _ (add_le_add le_rfl ih)
    unfold finitePowerSum
    have h := Real.Lp_add_le_of_nonneg (Finset.univ : Finset I) (f := a j)
      (g := fun i ↦ ∑ k ∈ s, a k i) hr (fun i _ ↦ ha j i)
      (fun i _ ↦ Finset.sum_nonneg fun k _ ↦ ha k i)
    simpa only [one_div] using h

theorem sum_finitePowerSum_le {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (s : Finset J) (a : J → I → ℝ) (ha : ∀ j i, 0 ≤ a j i) :
    (∑ j ∈ s, finitePowerSum r (a j)) ≤ finitePowerSum r (fun i ↦ ∑ j ∈ s, a j i) := by
  classical
  let T := {j : J // j ∈ s}
  let b (i : I) (j : T) : ℝ := a j.val i ^ r
  have hB (i : I) (j : T) : 0 ≤ b i j := Real.rpow_nonneg (ha _ _) _
  have h := finitePowerSum_sum_le (I := T) (J := I) (r := r⁻¹)
    (one_le_inv₀ hr |>.mpr hr₁) Finset.univ b hB
  have hs (f : J → ℝ) : (∑ j : T, f j.val) = ∑ j ∈ s, f j :=
    (Finset.sum_subtype s (fun _ ↦ Iff.rfl) f).symm
  have he (i : I) (j : T) : (b i j) ^ r⁻¹ = a j.val i :=
    Real.rpow_rpow_inv (ha _ _) hr.ne'
  have h₁ (i : I) : finitePowerSum r⁻¹ (b i) = (∑ j ∈ s, a j i) ^ r := by
    unfold finitePowerSum
    simp only [he, inv_inv]
    exact congrArg (fun t : ℝ ↦ t ^ r) (hs (fun j ↦ a j i))
  have h₂ : finitePowerSum r⁻¹ (fun j : T ↦ ∑ i, b i j) =
      (∑ j ∈ s, finitePowerSum r (a j)) ^ r := by
    unfold finitePowerSum
    dsimp only [b]
    rw [inv_inv]
    exact congrArg (fun t : ℝ ↦ t ^ r) (hs (fun j ↦ (∑ i, a j i ^ r) ^ r⁻¹))
  rw [h₂] at h
  simp only [h₁] at h
  have hnonneg : 0 ≤ ∑ j ∈ s, finitePowerSum r (a j) :=
    Finset.sum_nonneg fun j _ ↦ finitePowerSum_nonneg _ (ha j)
  rw [finitePowerSum]
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hnonneg _) h (inv_nonneg.mpr hr.le)
  rwa [Real.rpow_rpow_inv hnonneg hr.ne'] at hh

/-- A pointwise mixed contraction is preserved by summing the
nonnegative vectors over a finite index. -/
theorem finitePowerSum_sum_of_pointwise_le {O : Type*} [Fintype O]
    {r t : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (ht : 1 ≤ t)
    (s : Finset J) (a : J → I → ℝ) (b : J → O → ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hb : ∀ j i, 0 ≤ b j i)
    (h : ∀ j ∈ s, finitePowerSum t (b j) ≤ finitePowerSum r (a j)) :
    finitePowerSum t (fun i ↦ ∑ j ∈ s, b j i) ≤ finitePowerSum r (fun i ↦ ∑ j ∈ s, a j i) :=
  (finitePowerSum_sum_le ht s b hb).trans
    ((Finset.sum_le_sum h).trans (sum_finitePowerSum_le hr hr₁ s a ha))


theorem finitePowerSum_weighted_sum_le {O : Type*} [Fintype O]
    {r t : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (ht : 1 ≤ t)
    (s : Finset J) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (a : J → I → ℝ) (b : J → O → ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hb : ∀ j i, 0 ≤ b j i)
    (h : ∀ j ∈ s, finitePowerSum t (b j) ≤ finitePowerSum r (a j)) :
    finitePowerSum t (fun i ↦ ∑ j ∈ s, w j * b j i) ≤
      finitePowerSum r (fun i ↦ ∑ j ∈ s, w j * a j i) := by
  apply finitePowerSum_sum_of_pointwise_le hr hr₁ ht s
    (fun j i ↦ w j * a j i) (fun j i ↦ w j * b j i)
    (fun j i ↦ mul_nonneg (hw j) (ha j i)) (fun j i ↦ mul_nonneg (hw j) (hb j i))
  intro j hj
  rw [finitePowerSum_mul_const (zero_lt_one.trans_le ht) (hw j) (hb j),
    finitePowerSum_mul_const hr (hw j) (ha j)]
  exact mul_le_mul_of_nonneg_left (h j hj) (hw j)

end CarpetEnergy
