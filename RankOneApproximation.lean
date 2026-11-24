import RankOneSeminorm

/-!
# Proportionality from pairwise approximate dependence

The rational formulation avoids introducing a measurable family of
completed normed spaces. Approximate null combinations of a pair allow
every vector to be approximated in the seminorm by rational multiples
of a vector with positive seminorm.
-/

open Filter Set
open scoped Topology

namespace CarpetEnergy

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Arbitrarily small normalized rational relations. -/
def HasSmallRationalRelations (R : Seminorm ℚ V) : Prop :=
  ∀ f g : V, ∀ ε > (0 : ℝ), ∃ a b : ℚ, 0 < ‖a‖ + ‖b‖ ∧
    R (a • f + b • g) ≤ ε * (‖a‖ + ‖b‖)

private theorem exists_rat_sub_le_of_small_relations (R : Seminorm ℚ V)
    (h : HasSmallRationalRelations R) (f g : V) (hg : 0 < R g) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℚ, R (f - r • g) ≤ δ := by
  let L := R f + R g
  have hL : 0 < L := add_pos_of_nonneg_of_pos (apply_nonneg R f) hg
  let ε := min (R g / 2) (δ * R g / (2 * L))
  have hε : 0 < ε := lt_min (half_pos hg) (div_pos (mul_pos hδ hg) (by positivity))
  obtain ⟨a, b, hab, he⟩ := h f g ε hε
  let s := ‖a‖ + ‖b‖
  have hb : ‖b‖ * R g ≤ R (a • f + b • g) + ‖a‖ * R f := by
    have hb := map_sub_le_add R (a • f + b • g) (a • f)
    rw [add_sub_cancel_left, map_smul_eq_mul, map_smul_eq_mul] at hb
    exact hb
  have hleft : R g * s / 2 ≤ L * ‖a‖ := by
    have hε₀ : ε ≤ R g / 2 := min_le_left _ _
    have hu := he.trans (mul_le_mul_of_nonneg_right hε₀ hab.le)
    dsimp only [s, L] at *
    nlinarith only [hb, hu]
  have hapos : 0 < ‖a‖ := by
    have hh := (half_pos (mul_pos hg hab)).trans_le hleft
    exact pos_of_mul_pos_right hh hL.le
  have ha : a ≠ 0 := norm_pos_iff.mp hapos
  let r := -b / a
  have hr : a • (f - r • g) = a • f + b • g := by
    rw [smul_sub, smul_smul]
    have heq : a * r = -b := by
      dsimp only [r]
      field_simp
    rw [heq, neg_smul, sub_neg_eq_add]
  have hsmall : R (a • f + b • g) ≤ δ * ‖a‖ := by
    have hε₁ : ε ≤ δ * R g / (2 * L) := min_le_right _ _
    have ht := mul_le_mul_of_nonneg_right hε₁ hab.le
    have haux : (δ * R g / (2 * L)) * s ≤ δ * ‖a‖ := by
      have hl : R g * s / 2 / L ≤ ‖a‖ := (div_le_iff₀ hL).mpr (by
        rwa [mul_comm ‖a‖])
      calc
        _ = δ * (R g * s / 2 / L) := by ring_nf
        _ ≤ _ := mul_le_mul_of_nonneg_left hl hδ.le
    exact he.trans (ht.trans haux)
  rw [← hr, map_smul_eq_mul] at hsmall
  exact ⟨r, le_of_mul_le_mul_left (by simpa only [mul_comm δ] using hsmall) hapos⟩

/-- A seminorm dominated by a nonzero seminorm with pairwise small rational
relations is a single multiple of it. -/
theorem seminorm_eq_mul_of_small_relations (R T : Seminorm ℚ V)
    (h : HasSmallRationalRelations R) {U : ℝ} (hU : 0 ≤ U)
    (hT : ∀ f, T f ≤ U * R f) {g : V} (hg : 0 < R g) (f : V) :
    T f = (T g / R g) * R f := by
  let k := T g / R g
  have hk : 0 ≤ k := div_nonneg (apply_nonneg T g) hg.le
  have he (r : ℚ) : T (r • g) = k * R (r • g) := by
    rw [map_smul_eq_mul, map_smul_eq_mul, mul_left_comm, div_mul_cancel₀ _ hg.ne']
  have hsmall (δ : ℝ) (hδ : 0 < δ) : |T f - k * R f| ≤ (U + k) * δ := by
    obtain ⟨r, hr⟩ := exists_rat_sub_le_of_small_relations R h f g hg δ hδ
    have hR' : |R f - R (r • g)| ≤ δ := (abs_sub_map_le_sub R _ _).trans hr
    have hT' : |T f - T (r • g)| ≤ U * δ :=
      (abs_sub_map_le_sub T _ _).trans ((hT _).trans (mul_le_mul_of_nonneg_left hr hU))
    calc
      |T f - k * R f| = |(T f - T (r • g)) - k * (R f - R (r • g))| := by rw [he]; ring_nf
      _ ≤ |T f - T (r • g)| + |k * (R f - R (r • g))| := abs_sub _ _
      _ ≤ U * δ + k * δ := by
        rw [abs_mul, abs_of_nonneg hk]
        exact add_le_add hT' (mul_le_mul_of_nonneg_left hR' hk)
      _ = _ := (add_mul _ _ _).symm
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hlim : Tendsto (fun n : ℕ ↦ (U + k) * ε n) atTop (𝓝 0) := by
    have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero] using hε.const_mul (U + k)
  have hz : |T f - k * R f| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Eventually.of_forall fun n ↦ hsmall (ε n) (by dsimp [ε]; positivity))
  exact sub_eq_zero.mp (abs_eq_zero.mp (hz.antisymm (abs_nonneg _)))

/-- Taking the p-th power of the proportionality identity bounds the
single multiplier by the original comparison constants. -/
theorem exists_rpow_eq_mul_of_small_relations (R T : Seminorm ℚ V)
    (h : HasSmallRationalRelations R) {p lower upper : ℝ} (hp : 0 < p)
    (hlo : 0 ≤ lower) (hup : 0 ≤ upper)
    (hcompare : ∀ f, lower ^ p⁻¹ * R f ≤ T f ∧ T f ≤ upper ^ p⁻¹ * R f)
    {g : V} (hg : 0 < R g) :
    ∃ c ∈ Icc lower upper, ∀ f, T f ^ p = c * R f ^ p := by
  let b := T g / R g
  have hb : 0 ≤ b := div_nonneg (apply_nonneg T g) hg.le
  have hb₁ : lower ^ p⁻¹ ≤ b := (le_div_iff₀ hg).mpr (hcompare g).1
  have hb₂ : b ≤ upper ^ p⁻¹ := (div_le_iff₀ hg).mpr (hcompare g).2
  have h₁ := Real.rpow_le_rpow (Real.rpow_nonneg hlo _) hb₁ hp.le
  have h₂ := Real.rpow_le_rpow hb hb₂ hp.le
  rw [Real.rpow_inv_rpow hlo hp.ne'] at h₁
  rw [Real.rpow_inv_rpow hup hp.ne'] at h₂
  refine ⟨b ^ p, ⟨h₁, h₂⟩, fun f ↦ ?_⟩
  rw [seminorm_eq_mul_of_small_relations R T h (Real.rpow_nonneg hup _)
    (fun f ↦ (hcompare f).2) hg f,
    Real.mul_rpow hb (apply_nonneg R f)]

end CarpetEnergy
