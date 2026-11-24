import FiniteMixedNorm
import CarpetDiscreteEnergy

/-!
# Generalized contraction of graph edge differences

The pointwise mixed contraction of a vector map applies to each
oriented edge. The finite mixed summation inequalities combine the
edges with their nonnegative weights.
-/

open Function Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace CarpetEnergy

variable {I O A : Type*} [Fintype I] [Fintype O]

theorem finitePowerSum_rpow_div {X : Type*} [Fintype X] {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (x : X → ℝ) (hx : ∀ i, 0 ≤ x i) :
    finitePowerSum (q / p) (fun i ↦ x i ^ p) = (finitePowerSum q x) ^ p := by
  unfold finitePowerSum
  simp_rw [← Real.rpow_mul (hx _)]
  have hpq : p * (q / p) = q := by field_simp
  rw [hpq]
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hx i) _)]
  congr 1
  field_simp [hp.ne', hq.ne']

theorem weighted_rpow_mixed_contraction {p q₁ q₂ : ℝ}
    (hp : 0 < p) (h₁ : 0 < q₁) (h₁p : q₁ ≤ p) (h₂p : p ≤ q₂)
    (s : Finset A) (w : A → ℝ) (hw : ∀ e, 0 ≤ w e)
    (a : A → I → ℝ) (b : A → O → ℝ)
    (ha : ∀ e i, 0 ≤ a e i) (hb : ∀ e i, 0 ≤ b e i)
    (h : ∀ e ∈ s, finitePowerSum q₂ (b e) ≤ finitePowerSum q₁ (a e)) :
    finitePowerSum (q₂ / p) (fun i ↦ ∑ e ∈ s, w e * b e i ^ p) ≤
      finitePowerSum (q₁ / p) (fun i ↦ ∑ e ∈ s, w e * a e i ^ p) := by
  have h₂ : 0 < q₂ := hp.trans_le h₂p
  apply finitePowerSum_sum_of_pointwise_le (div_pos h₁ hp) ((div_le_one hp).mpr h₁p)
    ((one_le_div hp).mpr h₂p) s (fun e i ↦ w e * a e i ^ p) (fun e i ↦ w e * b e i ^ p)
    (fun e i ↦ mul_nonneg (hw e) (Real.rpow_nonneg (ha e i) _))
    (fun e i ↦ mul_nonneg (hw e) (Real.rpow_nonneg (hb e i) _))
  intro e he
  rw [finitePowerSum_mul_const (div_pos h₂ hp) (hw e) (fun i ↦ Real.rpow_nonneg (hb e i) _),
    finitePowerSum_mul_const (div_pos h₁ hp) (hw e) (fun i ↦ Real.rpow_nonneg (ha e i) _),
    finitePowerSum_rpow_div hp h₂ _ (hb e), finitePowerSum_rpow_div hp h₁ _ (ha e)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (finitePowerSum_nonneg _ (hb e))
    (h e he) hp.le) (hw e)

/-- Generalized p-contractivity for finite exponent pairs, applied to
the graph of intersecting carpet cells. -/
theorem discreteCellEnergy_mixed_contraction
    {p ρ q₁ q₂ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (hρ : 0 ≤ ρ) (h₁ : 0 < q₁) (h₁p : q₁ ≤ p) (h₂p : p ≤ q₂)
    (n : ℕ) (T : (I → ℝ) → O → ℝ)
    (hT : ∀ x y, finitePowerSum q₂ (fun i ↦ |T x i - T y i|) ≤
        finitePowerSum q₁ (fun i ↦ |x i - y i|))
    (f : I → CarpetLp p) (g : O → CarpetLp p)
    (hg : ∀ w : Fin n → Fin 8, ∀ i, ambientWordMean p (List.ofFn w) (g i) =
      T (fun j ↦ ambientWordMean p (List.ofFn w) (f j)) i) :
    finitePowerSum (q₂ / p) (fun i ↦ (discreteCellEnergy p ρ n (g i)).toReal) ≤
      finitePowerSum (q₁ / p) (fun i ↦ (discreteCellEnergy p ρ n (f i)).toReal) := by
  classical
  let W := Fin n → Fin 8
  let es := (Finset.univ : Finset (W × W)).filter fun e ↦ e.2 ∈ gridNeighbors e.1
  let wt (_ : W × W) := ρ ^ n / 2
  let d (u : CarpetLp p) (e : W × W) :=
    |ambientWordMean p (List.ofFn e.1) u - ambientWordMean p (List.ofFn e.2) u|
  have hwt (e : W × W) : 0 ≤ wt e := by dsimp only [wt]; positivity
  have he (u : CarpetLp p) : (discreteCellEnergy p ρ n u).toReal =
      ∑ e ∈ es, wt e * d u e ^ p := by
    rw [discreteCellEnergy_eq_grid (ρ := ρ) hp, ENNReal.toReal_ofReal
      (by exact mul_nonneg (div_nonneg (pow_nonneg hρ _) (by norm_num)) (Finset.sum_nonneg fun w _ ↦ Finset.sum_nonneg fun v _ ↦
        Real.rpow_nonneg (abs_nonneg _) _))]
    dsimp only [es, wt]
    rw [← Finset.mul_sum, Finset.sum_filter]
    congr 1
    rw [← Finset.univ_product_univ, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro w _
    simp only [d]
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext v; simp) (fun _ _ ↦ rfl)
  simp only [he]
  apply weighted_rpow_mixed_contraction hp h₁ h₁p h₂p es wt hwt
    (fun e i ↦ d (f i) e) (fun e i ↦ d (g i) e)
    (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ abs_nonneg _)
  intro e _
  simp only [d, hg]
  exact hT _ _


/-- A map obeying a finite mixed contraction is componentwise Lipschitz
for the product norm used in the pointwise Lp operation. -/
theorem exists_lipschitzWith_mixed_components {q₁ q₂ : ℝ}
    (h₁ : 0 < q₁) (h₂ : 0 < q₂) (T : (I → ℝ) → O → ℝ)
    (hT : ∀ x y, finitePowerSum q₂ (fun i ↦ |T x i - T y i|) ≤
        finitePowerSum q₁ (fun i ↦ |x i - y i|)) :
    ∃ L : ℝ≥0, ∀ i, LipschitzWith L (fun x ↦ T x i) := by
  let L : ℝ≥0 := ⟨(Fintype.card I : ℝ) ^ q₁⁻¹, Real.rpow_nonneg (Nat.cast_nonneg _) _⟩
  refine ⟨L, fun i ↦ lipschitzWith_iff_dist_le_mul.mpr fun x y ↦ ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  have hlow : |T x i - T y i| ≤ finitePowerSum q₂ (fun j ↦ |T x j - T y j|) := by
    unfold finitePowerSum
    rw [← Real.rpow_rpow_inv (abs_nonneg (T x i - T y i)) h₂.ne']
    apply Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) _ (inv_nonneg.mpr h₂.le)
    exact Finset.single_le_sum (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
  have hhi : finitePowerSum q₁ (fun j ↦ |x j - y j|) ≤ (L : ℝ) * ‖x - y‖ := by
    have hb (j : I) : |x j - y j| ≤ ‖x - y‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm (x - y) j
    have hh : (∑ j : I, |x j - y j| ^ q₁) ≤ (Fintype.card I : ℝ) * ‖x - y‖ ^ q₁ := by
      calc
        _ ≤ ∑ _ : I, ‖x - y‖ ^ q₁ :=
          Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hb j) h₁.le
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold finitePowerSum
    apply (Real.rpow_le_rpow (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg _) _) hh
      (inv_nonneg.mpr h₁.le)).trans_eq
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
      Real.rpow_rpow_inv (norm_nonneg _) h₁.ne']
    rfl
  exact hlow.trans ((hT x y).trans hhi)

end CarpetEnergy
