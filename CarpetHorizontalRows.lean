import EnergyQuasiUniqueness

/-!
# Parallel horizontal rows in the level grid

Every row whose ternary height digits are either zero or two contains all
columns. Summing the costs of the disjoint left-to-right chains bounds the
renormalization factor strictly below the threshold for boundary energy.
-/

open Function Set
open scoped BigOperators Topology

namespace CarpetEnergy

private def rowCell (a : Fin 2) (k : ℕ) : Fin 8 :=
  if a = 0 then ![0, 1, 2] (Fin.ofNat 3 k) else ![6, 5, 4] (Fin.ofNat 3 k)

private theorem rowCell_first (a : Fin 2) {k : ℕ} (hk : k < 3) :
    (cellDigit (rowCell a k) 0 : ℕ) = k := by
  have h : ∀ (a : Fin 2) (b : Fin 3),
      (cellDigit (if a = 0 then ![0, 1, 2] b else ![6, 5, 4] b) 0 : ℕ) = b.val := by decide
  exact (h a (Fin.ofNat 3 k)).trans (Nat.mod_eq_of_lt hk)

private theorem rowCell_second (a : Fin 2) (k : ℕ) :
    (cellDigit (rowCell a k) 1 : ℕ) = 2 * a.val := by
  have h : ∀ (a : Fin 2) (b : Fin 3),
      (cellDigit (if a = 0 then ![0, 1, 2] b else ![6, 5, 4] b) 1 : ℕ) = 2 * a.val := by decide
  exact h a (Fin.ofNat 3 k)

private def rowList : List (Fin 2) → ℕ → List (Fin 8)
  | [], _ => []
  | a :: r, k => rowCell a (k / 3 ^ r.length) :: rowList r (k % 3 ^ r.length)

private theorem length_rowList (r : List (Fin 2)) (k : ℕ) : (rowList r k).length = r.length := by
  induction r generalizing k with
  | nil => rfl
  | cons a r ih => simp only [rowList, List.length_cons, ih]

private theorem gridCoordinate_rowList_first (r : List (Fin 2)) {k : ℕ} (hk : k < 3 ^ r.length) :
    gridCoordinate (rowList r k) 0 = k := by
  induction r generalizing k with
  | nil =>
    simp only [List.length_nil, pow_zero] at hk
    change 0 = k
    omega
  | cons a r ih =>
    have ht : 0 < 3 ^ r.length := by positivity
    have hq : k / 3 ^ r.length < 3 := (Nat.div_lt_iff_lt_mul ht).mpr (by
      simpa only [List.length_cons, pow_succ'] using hk)
    rw [rowList, gridCoordinate, length_rowList, rowCell_first a hq, ih (Nat.mod_lt _ ht),
      Nat.mul_comm, Nat.div_add_mod]

private theorem gridCoordinate_rowList_second (r : List (Fin 2)) (k l : ℕ) :
    gridCoordinate (rowList r k) 1 = gridCoordinate (rowList r l) 1 := by
  induction r generalizing k l with
  | nil => rfl
  | cons a r ih =>
    simp only [rowList, gridCoordinate, length_rowList, rowCell_second]
    rw [ih (k % 3 ^ r.length) (l % 3 ^ r.length)]

private def rowProjection (i : Fin 8) : Fin 2 :=
  if cellDigit i 1 = 2 then 1 else 0

private theorem map_rowProjection (r : List (Fin 2)) (k : ℕ) :
    (rowList r k).map rowProjection = r := by
  induction r generalizing k with
  | nil => rfl
  | cons a r ih =>
    simp only [rowList, List.map_cons, ih, List.cons.injEq, and_true]
    have h (j : ℕ) : rowProjection (rowCell a j) = a := by
      unfold rowProjection
      have h := rowCell_second a j
      fin_cases a
      · have h0 : cellDigit (rowCell 0 j) 1 = 0 := Fin.ext h
        simp [h0]
      · have h2 : cellDigit (rowCell 1 j) 1 = 2 := Fin.ext h
        simp [h2]
    exact h _

private def rowWord {n : ℕ} (r : Fin n → Fin 2) (k : Fin (3 ^ n)) : Fin n → Fin 8 :=
  fun j ↦ (rowList (List.ofFn r) k.val).get
    (Fin.cast (by rw [length_rowList, List.length_ofFn]) j)

private theorem ofFn_rowWord {n : ℕ} (r : Fin n → Fin 2) (k : Fin (3 ^ n)) :
    List.ofFn (rowWord r k) = rowList (List.ofFn r) k.val := by
  apply List.ext_get
  · rw [List.length_ofFn, length_rowList, List.length_ofFn]
  · intro j hj hj'
    rw [List.get_ofFn]
    rfl

private theorem gridCoordinate_rowWord_first {n : ℕ} (r : Fin n → Fin 2) (k : Fin (3 ^ n)) :
    gridCoordinate (List.ofFn (rowWord r k)) 0 = k.val := by
  rw [ofFn_rowWord]
  exact gridCoordinate_rowList_first _ (by simpa only [List.length_ofFn] using k.isLt)

private theorem gridCoordinate_rowWord_second {n : ℕ} (r : Fin n → Fin 2) (k l : Fin (3 ^ n)) :
    gridCoordinate (List.ofFn (rowWord r k)) 1 = gridCoordinate (List.ofFn (rowWord r l)) 1 := by
  rw [ofFn_rowWord, ofFn_rowWord]
  exact gridCoordinate_rowList_second _ _ _

private theorem rowWord_injective (n : ℕ) :
    Injective (fun a : (Fin n → Fin 2) × Fin (3 ^ n) ↦ rowWord a.1 a.2) := by
  rintro ⟨r, k⟩ ⟨s, l⟩ he
  have hw := congrArg List.ofFn he
  change List.ofFn (rowWord r k) = List.ofFn (rowWord s l) at hw
  have hk : k = l := Fin.ext ((gridCoordinate_rowWord_first r k).symm.trans
    ((congrArg (fun w ↦ gridCoordinate w 0) hw).trans (gridCoordinate_rowWord_first s l)))
  rw [ofFn_rowWord, ofFn_rowWord] at hw
  have hr : r = s := List.ofFn_injective (by
    simpa only [map_rowProjection] using congrArg (List.map rowProjection) hw)
  exact Prod.ext hr hk

private theorem rowWord_mem_gridNeighbors {n : ℕ} (r : Fin n → Fin 2)
    (k l : Fin (3 ^ n)) (h : l.val = k.val + 1) :
    rowWord r l ∈ gridNeighbors (rowWord r k) := by
  apply mem_gridNeighbors.mpr
  intro j
  fin_cases j
  · change gridCoordinate (List.ofFn (rowWord r k)) 0 ≤
        gridCoordinate (List.ofFn (rowWord r l)) 0 + 1 ∧
      gridCoordinate (List.ofFn (rowWord r l)) 0 ≤ gridCoordinate (List.ofFn (rowWord r k)) 0 + 1
    rw [gridCoordinate_rowWord_first, gridCoordinate_rowWord_first]
    omega
  · change gridCoordinate (List.ofFn (rowWord r k)) 1 ≤
        gridCoordinate (List.ofFn (rowWord r l)) 1 + 1 ∧
      gridCoordinate (List.ofFn (rowWord r l)) 1 ≤ gridCoordinate (List.ofFn (rowWord r k)) 1 + 1
    rw [gridCoordinate_rowWord_second r k l]
    omega

private theorem rowWord_touches_side {n : ℕ} (r : Fin n → Fin 2) (k : Fin (3 ^ n))
    (a : Fin 2) (hk : (k.val : ℝ) = ((3 : ℝ) ^ n - 1) * a.val) :
    ∃ z ∈ range (wordMap (List.ofFn (rowWord r k))), (z : Plane) 0 = a.val := by
  refine ⟨_, mem_range_self (cornerPoint a 0), ?_⟩
  have h := wordMap_scaled_coord (List.ofFn (rowWord r k)) (cornerPoint a 0) 0
  rw [List.length_ofFn, gridCoordinate_rowWord_first r k, cornerPoint_first, hk] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (show (3 : ℝ) ≠ 0 by norm_num)) (h.trans (by ring))

private theorem sum_chain_rpow_ge {p : ℝ} (hp : 1 ≤ p)
    (N : ℕ) (m : ℕ → ℝ) (h0 : m 0 = 0) (hN : m N = 1) :
    1 ≤ (N : ℝ) ^ (p - 1) * ∑ k ∈ Finset.range N, |m (k + 1) - m k| ^ p := by
  have ht : ∑ k ∈ Finset.range N, (m (k + 1) - m k) = 1 := by
    rw [Finset.sum_range_sub, h0, hN, sub_zero]
  have hsum : 1 ≤ ∑ k ∈ Finset.range N, |m (k + 1) - m k| := by
    have h := Finset.abs_sum_le_sum_abs (s := Finset.range N) (fun k ↦ m (k + 1) - m k)
    simpa only [ht, abs_one] using h
  calc
    1 = (1 : ℝ) ^ p := (Real.one_rpow _).symm
    _ ≤ (∑ k ∈ Finset.range N, |m (k + 1) - m k|) ^ p :=
      Real.rpow_le_rpow zero_le_one hsum (zero_le_one.trans hp)
    _ ≤ _ := by
      simpa only [Finset.card_range] using
        Real.rpow_sum_le_const_mul_sum_rpow (Finset.range N) (fun k ↦ m (k + 1) - m k) hp

namespace SelfSimilarPEnergy

open MeasureTheory Filter

variable {p : ℝ} (E : SelfSimilarPEnergy p)

private theorem row_cost_lower (n : ℕ) (u : E.LeftRightProfile) (r : Fin (n + 1) → Fin 2) :
    ((3 : ℝ) ^ (n + 1)) ^ (1 - p) ≤
      ∑ k : Fin (3 ^ (n + 1)), ∑ v ∈ gridNeighbors (rowWord r k),
        |continuousWordMean (E.spliceProfile u).toContinuousMap (List.ofFn (rowWord r k)) -
          continuousWordMean (E.spliceProfile u).toContinuousMap (List.ofFn v)| ^ p := by
  classical
  let N : ℕ := 3 ^ (n + 1)
  have hN : 0 < N := by dsimp [N]; positivity
  let f := (E.spliceProfile u).toContinuousMap
  let m (w : Fin (n + 1) → Fin 8) := continuousWordMean f (List.ofFn w)
  let a (k : ℕ) := if h : k < N then m (rowWord r ⟨k, h⟩) else 0
  have h0 : a 0 = 0 := by
    dsimp only [a]
    rw [dite_eq_left hN]
    obtain ⟨z, hz, hza⟩ := rowWord_touches_side r (⟨0, hN⟩ : Fin N) 0 (by
      change (0 : ℝ) = (3 ^ (n + 1) - 1) * 0
      ring)
    exact splice_mean_eq_side E u n _ 0 hz hza
  have hlast : a (N - 1) = 1 := by
    have hlt : N - 1 < N := by omega
    dsimp only [a]
    rw [dite_eq_left hlt]
    have he : ((N - 1 : ℕ) : ℝ) = ((3 : ℝ) ^ (n + 1) - 1) * ((1 : Fin 2).val : ℝ) := by
      change ((N - 1 : ℕ) : ℝ) = ((3 : ℝ) ^ (n + 1) - 1) * 1
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      push_cast
      simp [N]
    obtain ⟨z, hz, hza⟩ := rowWord_touches_side r (⟨N - 1, hlt⟩ : Fin N) 1 he
    exact splice_mean_eq_side E u n _ 1 hz hza
  let S := ∑ j ∈ Finset.range (N - 1), |a (j + 1) - a j| ^ p
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hc : ((N : ℝ) ^ (1 - p)) ≤ S := by
    have hle := sum_chain_rpow_ge E.one_lt_p.le (N - 1) a h0 hlast
    have hle' : ((N - 1 : ℕ) : ℝ) ^ (p - 1) ≤ (N : ℝ) ^ (p - 1) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le N 1) (sub_nonneg.mpr E.one_lt_p.le)
    have hpos : 0 < (N : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
    rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg (Nat.cast_nonneg _)]
    apply (inv_le_iff_one_le_mul₀ hpos).mpr
    rw [mul_comm S]
    exact hle.trans (mul_le_mul_of_nonneg_right hle' hS)
  have hcost : S ≤ ∑ k : Fin N, ∑ v ∈ gridNeighbors (rowWord r k), |m (rowWord r k) - m v| ^ p := by
    let i : Fin (N - 1) ↪ Fin N :=
      ⟨fun k ↦ ⟨k.val, lt_trans k.isLt (by omega)⟩, fun _ _ h ↦ Fin.ext (congrArg (fun z : Fin N ↦ z.val) h)⟩
    let G (k : Fin N) := ∑ v ∈ gridNeighbors (rowWord r k), |m (rowWord r k) - m v| ^ p
    have hG (k : Fin N) : 0 ≤ G k := Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    calc
      S = ∑ k : Fin (N - 1), |a (k.val + 1) - a k.val| ^ p := (Fin.sum_univ_eq_sum_range _ _).symm
      _ ≤ ∑ k : Fin (N - 1), G (i k) := by
        apply Finset.sum_le_sum
        intro k _
        let l : Fin N := ⟨k.val + 1, by have hk := k.isLt; omega⟩
        have h := rowWord_mem_gridNeighbors r (i k) l rfl
        have hk : k.val < N := (i k).isLt
        dsimp only [a]
        rw [dite_eq_left l.isLt, dite_eq_left hk, abs_sub_comm]
        exact Finset.single_le_sum (fun v _ ↦ Real.rpow_nonneg (abs_nonneg _) _) h
      _ ≤ _ := by
        rw [← Finset.sum_map]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ ↦ hG k)
  have he : (N : ℝ) = (3 : ℝ) ^ (n + 1) := by push_cast [N]; rfl
  simpa only [he, f, m] using hc.trans hcost

private theorem sum_parallel_rows_le_sum (n : ℕ) (G : (Fin n → Fin 8) → ℝ)
    (hG : ∀ w, 0 ≤ G w) :
    (∑ r : Fin n → Fin 2, ∑ j : Fin (3 ^ n), G (rowWord r j)) ≤ ∑ w, G w := by
  classical
  let I := (Fin n → Fin 2) × Fin (3 ^ n)
  let i : I ↪ (Fin n → Fin 8) := ⟨fun a ↦ rowWord a.1 a.2, rowWord_injective n⟩
  calc
    (∑ r : Fin n → Fin 2, ∑ j : Fin (3 ^ n), G (rowWord r j)) = ∑ a : I, G (i a) :=
      (Fintype.sum_prod_type (fun a : I ↦ G (i a))).symm
    _ ≤ _ := by
      rw [← Finset.sum_map]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ ↦ hG w)

set_option maxHeartbeats 600000 in
/-- The carpet contains enough parallel chains to force
`ρ ≤ 3 ^ (p - 1) / 2`. -/
theorem scalingFactor_le_half_three_rpow :
    E.scalingFactor ≤ (3 : ℝ) ^ (p - 1) / 2 := by
  classical
  obtain ⟨u⟩ := E.nonempty_leftRightProfile
  obtain ⟨C, _, hgrid⟩ := E.exists_gridMean_energy_le
  let f := (E.spliceProfile u).toContinuousMap
  let hf := (E.spliceProfile u).mem_domain
  let B := C * (E.energy ⟨continuousLp p f, hf⟩ : ℝ)
  let M := (3 : ℝ) ^ (p - 1)
  have hM : 0 < M := Real.rpow_pos_of_pos (by norm_num) _
  let q := 2 * E.scalingFactor / M
  have hρ := E.isScalingFactor_scalingFactor.1
  by_contra! hbad
  have hq : 1 < q := (lt_div_iff₀ hM).mpr (by linarith)
  have hb (n : ℕ) : q ^ (n + 1) ≤ B := by
    let k := n + 1
    let m (w : Fin k → Fin 8) := continuousWordMean f (List.ofFn w)
    let G (w : Fin k → Fin 8) := ∑ v ∈ gridNeighbors w, |m w - m v| ^ p
    let S := ∑ w : Fin k → Fin 8, G w
    have hG (w : Fin k → Fin 8) : 0 ≤ G w :=
      Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    have hcost : (2 : ℝ) ^ k * ((3 : ℝ) ^ k) ^ (1 - p) ≤ S := by
      calc
        _ = ∑ _r : Fin k → Fin 2, ((3 : ℝ) ^ k) ^ (1 - p) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        _ ≤ ∑ r : Fin k → Fin 2, ∑ j : Fin (3 ^ k), G (rowWord r j) :=
          Finset.sum_le_sum (fun r _ ↦ E.row_cost_lower n u r)
        _ ≤ S := sum_parallel_rows_le_sum k G hG
    have he : ((3 : ℝ) ^ k) ^ (1 - p) = (M ^ k)⁻¹ := by
      rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg (pow_nonneg (by norm_num) _)]
      dsimp only [M]
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (k : ℝ), Real.rpow_mul_natCast (by norm_num)]
    have hqeq : q ^ k = E.scalingFactor ^ k * ((2 : ℝ) ^ k * ((3 : ℝ) ^ k) ^ (1 - p)) := by
      rw [he, show q = 2 * E.scalingFactor / M from rfl, div_pow, mul_pow, div_eq_mul_inv]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    calc
      q ^ (n + 1) = _ := hqeq
      _ ≤ E.scalingFactor ^ k * S := mul_le_mul_of_nonneg_left hcost (pow_nonneg hρ.le k)
      _ ≤ B := hgrid k f hf
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hq
  exact hn.not_ge ((pow_le_pow_right₀ hq.le (Nat.le_succ n)).trans (hb n))

/-- In particular, the root energies of boundary-scale corrections have
summable geometric bounds. -/
theorem scalingFactor_mul_three_rpow_lt_one :
    E.scalingFactor * (3 : ℝ) ^ (1 - p) < 1 := by
  let M := (3 : ℝ) ^ (p - 1)
  have hM : 0 < M := Real.rpow_pos_of_pos (by norm_num) _
  rw [show (3 : ℝ) ^ (1 - p) = M⁻¹ by
    rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg (by norm_num)]]
  exact (mul_le_mul_of_nonneg_right E.scalingFactor_le_half_three_rpow (inv_nonneg.mpr hM.le)).trans_lt
    (show M / 2 * M⁻¹ < 1 by
      rw [div_mul_eq_mul_div, mul_inv_cancel₀ hM.ne']
      norm_num)

end SelfSimilarPEnergy

end CarpetEnergy
