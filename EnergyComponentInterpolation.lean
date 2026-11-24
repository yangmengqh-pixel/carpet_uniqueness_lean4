import ComponentCornerInterpolation
import EnergyGridComparison

/-!
# Energy control of kernel interpolants

The four local basis functions have fixed energy. Cell averages determine
nodal values, and the discrete energy controls the global interpolant.
-/

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent

variable {p : ℝ} {E : SelfSimilarPEnergy p} {Q : E.SelfSimilarComponent}

noncomputable def continuousLpLinear (p : ℝ) : C(CarpetPoints, ℝ) →ₗ[ℝ] CarpetLp p where
  toFun := continuousLp p
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [continuousLp_ae_eq p (u + v), continuousLp_ae_eq p u, continuousLp_ae_eq p v,
      Lp.coeFn_add (continuousLp p u) (continuousLp p v)] with x h₁ h₂ h₃ h₄
    rw [h₁, h₄, Pi.add_apply, h₂, h₃]
    rfl
  map_smul' := by
    intro a u
    apply Lp.ext
    filter_upwards [continuousLp_ae_eq p (a • u), continuousLp_ae_eq p u,
      Lp.coeFn_smul a (continuousLp p u)] with x h₁ h₂ h₃
    rw [RingHom.id_apply, h₁, h₃, Pi.smul_apply, h₂]
    rfl

private theorem continuousLp_const (a : ℝ) :
    continuousLp p (ContinuousMap.const CarpetPoints a) = constantLp p a := by
  apply Lp.ext
  exact (continuousLp_ae_eq p _).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a).symm

namespace CornerProfile

variable (P : Q.CornerProfile)

private noncomputable def cornerBasis (ij : Fin 2 × Fin 2) : C(CarpetPoints, ℝ) :=
  P.interpolate (fun i j ↦ if (i, j) = ij then 1 else 0)

private theorem interpolate_eq_sum_basis (a : Fin 2 → Fin 2 → ℝ) :
    P.interpolate a = ∑ ij : Fin 2 × Fin 2, (a ij.1 ij.2) • P.cornerBasis ij := by
  ext x
  rw [P.interpolate_apply, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, cornerBasis, P.interpolate_apply]
  ring

private theorem interpolate_sub_constant (a : Fin 2 → Fin 2 → ℝ) (c : ℝ) :
    P.interpolate a = P.interpolate (fun i j ↦ a i j - c) + ContinuousMap.const CarpetPoints c := by
  ext x
  change P.interpolate a x = P.interpolate (fun i j ↦ a i j - c) x + c
  rw [P.interpolate_apply, P.interpolate_apply]
  ring

/-- The p-energy of a local interpolant is bounded by a fixed multiple
of the p-th power of the maximum deviation of its corner data. -/
theorem exists_interpolate_energy_bound :
    ∃ C ≥ (0 : ℝ), ∀ (a : Fin 2 → Fin 2 → ℝ)
      (ha : continuousLp p (P.interpolate a) ∈ E.domain) (c R : ℝ), 0 ≤ R →
      (∀ i j, |a i j - c| ≤ R) →
      (E.energy ⟨continuousLp p (P.interpolate a), ha⟩ : ℝ) ≤ C * R ^ p := by
  classical
  let I := Fin 2 × Fin 2
  let φ (ij : I) := P.cornerBasis ij
  have hφ (ij : I) : continuousLp p (φ ij) ∈ E.domain :=
    (P.interpolate_mem_kernel _).choose
  let ψ (ij : I) : E.domain := ⟨continuousLp p (φ ij), hφ ij⟩
  let B := ∑ ij : I, E.rootSeminorm (ψ ij)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  refine ⟨B ^ p, Real.rpow_nonneg hB _, ?_⟩
  intro a ha c R hR hdata
  let shifted (i j : Fin 2) := a i j - c
  have hs : continuousLp p (P.interpolate shifted) ∈ E.domain := (P.interpolate_mem_kernel shifted).choose
  let u : E.domain := ⟨continuousLp p (P.interpolate a), ha⟩
  let v : E.domain := ⟨continuousLp p (P.interpolate shifted), hs⟩
  have huv : u = v + ⟨constantLp p c, E.constant_mem c⟩ := by
    apply Subtype.ext
    change continuousLpLinear p (P.interpolate a) =
      continuousLpLinear p (P.interpolate shifted) + constantLp p c
    rw [P.interpolate_sub_constant a c, map_add]
    exact congrArg _ (continuousLp_const c)
  have he : E.energy u = E.energy v := by rw [huv, E.add_constant]
  have hv : v = ∑ ij : I, (shifted ij.1 ij.2) • ψ ij := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change continuousLpLinear p (P.interpolate shifted) =
      ∑ ij : I, (shifted ij.1 ij.2) • continuousLpLinear p (φ ij)
    rw [P.interpolate_eq_sum_basis, map_sum]
    exact Finset.sum_congr rfl (fun ij _ ↦ map_smul (continuousLpLinear p) _ _)
  have hr : E.rootSeminorm v ≤ R * B := by
    rw [hv]
    calc
      _ ≤ ∑ ij : I, E.rootSeminorm ((shifted ij.1 ij.2) • ψ ij) :=
        Finset.map_sum_le_sum _ _ _
      _ = ∑ ij : I, |shifted ij.1 ij.2| * E.rootSeminorm (ψ ij) := by
        apply Finset.sum_congr rfl
        intro ij _
        rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ ∑ ij : I, R * E.rootSeminorm (ψ ij) :=
        Finset.sum_le_sum (fun ij _ ↦ mul_le_mul_of_nonneg_right (hdata ij.1 ij.2) (apply_nonneg _ _))
      _ = _ := (Finset.mul_sum ..).symm
  have heq : (E.rootSeminorm v) ^ p = (E.energy v : ℝ) := by
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg (E.energy v)) hp.ne'
  change (E.energy u : ℝ) ≤ _
  rw [he, ← heq]
  calc
    _ ≤ (R * B) ^ p := Real.rpow_le_rpow (apply_nonneg _ _) hr hp.le
    _ = _ := by rw [Real.mul_rpow hR hB, mul_comm]

end CornerProfile

open CornerProfile

noncomputable def incidentWords (n : ℕ) (z : CarpetPoints) : Finset (Fin n → Fin 8) := by
  classical
  exact Finset.univ.filter fun w ↦ z ∈ range (wordMap (List.ofFn w))

theorem mem_incidentWords {n : ℕ} {w : Fin n → Fin 8} {z : CarpetPoints} :
    w ∈ incidentWords n z ↔ z ∈ range (wordMap (List.ofFn w)) := by
  classical
  simp [incidentWords]

private theorem incidentWords_pos (n : ℕ) (z : CarpetPoints) : 0 < (incidentWords n z).card := by
  obtain ⟨w, hw⟩ := exists_wordMap_range n z
  exact Finset.card_pos.mpr ⟨w, mem_incidentWords.mpr hw⟩

noncomputable def cornerAverage (n : ℕ) (m : (Fin n → Fin 8) → ℝ) (z : CarpetPoints) : ℝ :=
  (∑ w ∈ incidentWords n z, m w) / (incidentWords n z).card

theorem abs_cornerAverage_sub_le (n : ℕ) (m : (Fin n → Fin 8) → ℝ) (z : CarpetPoints)
    {c R : ℝ} (h : ∀ w ∈ incidentWords n z, |m w - c| ≤ R) :
    |cornerAverage n m z - c| ≤ R := by
  let W := incidentWords n z
  let k : ℝ := W.card
  have hk : 0 < k := by
    change 0 < ((incidentWords n z).card : ℝ)
    exact_mod_cast incidentWords_pos n z
  have he : cornerAverage n m z - c = (∑ w ∈ W, (m w - c)) / k := by
    change (∑ w ∈ W, m w) / k - c = _
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, sub_div]
    have hh : ((W.card : ℝ) * c) / k = c := by change (k * c) / k = _; field_simp
    rw [hh]
  rw [he, abs_div, abs_of_pos hk]
  apply (div_le_iff₀ hk).mpr
  calc
    _ ≤ ∑ w ∈ W, |m w - c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ W, R := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; exact mul_comm _ _

theorem abs_wordMean_sub_le (f : C(CarpetPoints, ℝ)) (w : List (Fin 8))
    {c R : ℝ} (h : ∀ x, |f (wordMap w x) - c| ≤ R) :
    |continuousWordMean f w - c| ≤ R := by
  have hcont : Continuous (fun x ↦ f (wordMap w x)) := f.continuous.comp (continuous_wordMap w)
  have hint : Integrable (fun x ↦ f (wordMap w x)) carpetMeasure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI : (∫ x, f (wordMap w x) - c ∂carpetMeasure) = continuousWordMean f w - c := by
    rw [integral_sub hint (integrable_const _)]
    simp [continuousWordMean, Measure.real]
  rw [← hI, ← Real.norm_eq_abs]
  have hnorm := norm_integral_le_of_norm_le_const (μ := carpetMeasure)
    (f := fun x ↦ f (wordMap w x) - c) (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact h x)
  simpa [Measure.real] using hnorm

theorem cornerAmplitude_le_neighborEnergy (n : ℕ) (m : (Fin n → Fin 8) → ℝ)
    (w : Fin n → Fin 8) (i j : Fin 2) (hp : 0 < p) :
    let S := ∑ v ∈ gridNeighbors w,
      |m w - m v| ^ p
    |cornerData (cornerAverage n m) (List.ofFn w) i j - m w| ≤
      S ^ p⁻¹ := by
  let w' := List.ofFn w
  let z := wordMap w' (cornerPoint i j)
  let S := ∑ v ∈ gridNeighbors w, |m w - m v| ^ p
  change |cornerAverage n m z - m w| ≤ S ^ p⁻¹
  apply abs_cornerAverage_sub_le
  intro v hv
  have hn : v ∈ gridNeighbors w := mem_gridNeighbors.mpr (gridNear_of_mem_inter
    (by rw [List.length_ofFn, List.length_ofFn]) (mem_range_self (cornerPoint i j)) (mem_incidentWords.mp hv))
  have h : |m w - m v| ^ p ≤ S :=
    Finset.single_le_sum (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) hn
  rw [abs_sub_comm]
  calc
    |m w - m v| = (|m w - m v| ^ p) ^ p⁻¹ := (Real.rpow_rpow_inv (abs_nonneg _) hp.ne').symm
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h (inv_nonneg.mpr hp.le)

theorem continuousLp_interpolate_word_eq
    (g : C(CarpetPoints, ℝ)) (hg : continuousLp p g ∈ E.domain)
    (u : C(CarpetPoints, ℝ)) (w : List (Fin 8)) (he : ∀ x, g (wordMap w x) = u x) :
    continuousLp p u = (E.pullbackWord w ⟨continuousLp p g, hg⟩ : CarpetLp p) := by
  let g' : E.domain := ⟨continuousLp p g, hg⟩
  apply Lp.ext
  refine (continuousLp_ae_eq p u).trans ?_
  have h := ((E.pullbackWord_isLpPullback w g').trans
    ((quasiMeasurePreserving_wordMap w).ae_eq_comp (continuousLp_ae_eq p g))).symm
  exact (funext he : (g : CarpetPoints → ℝ) ∘ wordMap w = u) ▸ h

/-- Interpolate cell values by nodal averaging, controlling the energy
by the discrete differences of the data. -/
theorem CornerProfile.exists_interpolate_cellValues (P : Q.CornerProfile) :
    ∃ C ≥ (0 : ℝ), ∀ (n : ℕ) (m : (Fin n → Fin 8) → ℝ),
      ∃ (g : C(CarpetPoints, ℝ)) (hg : continuousLp p g ∈ E.domain),
        (⟨continuousLp p g, hg⟩ : E.domain) ∈ Q.kernel ∧
        (∀ (w : Fin n → Fin 8) x, g (wordMap (List.ofFn w) x) =
          P.interpolate (cornerData (cornerAverage n m) (List.ofFn w)) x) ∧
        (E.energy ⟨continuousLp p g, hg⟩ : ℝ) ≤ C * (E.scalingFactor ^ n *
          ∑ w : Fin n → Fin 8, ∑ v ∈ gridNeighbors w, |m w - m v| ^ p) := by
  obtain ⟨C, hC, hlocal⟩ := P.exists_interpolate_energy_bound
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  refine ⟨C, hC, fun n m ↦ ?_⟩
  obtain ⟨g, ⟨hg_dom, hg_ker⟩, hG⟩ := P.exists_global_interpolate (cornerAverage n m) n
  let u : E.domain := ⟨continuousLp p g, hg_dom⟩
  refine ⟨g, hg_dom, hg_ker, hG, ?_⟩
  let W := Fin n → Fin 8
  let S (w : W) := ∑ v ∈ gridNeighbors w, |m w - m v| ^ p
  have hS (w : W) : 0 ≤ S w := Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hbound (w : W) : (E.energy (E.pullbackWord (List.ofFn w) u) : ℝ) ≤ C * S w := by
    let a := cornerData (cornerAverage n m) (List.ofFn w)
    let v := P.interpolate a
    have he := continuousLp_interpolate_word_eq g hg_dom v _ (hG w)
    have hv : continuousLp p v ∈ E.domain := he.symm ▸ (E.pullbackWord _ u).property
    have hv' : (⟨continuousLp p v, hv⟩ : E.domain) = E.pullbackWord (List.ofFn w) u :=
      Subtype.ext he
    have hc := hlocal a hv (m w) (S w ^ p⁻¹) (Real.rpow_nonneg (hS w) _)
      (fun i j ↦ cornerAmplitude_le_neighborEnergy n m w i j hp)
    rw [hv', Real.rpow_inv_rpow (hS w) hp.ne'] at hc
    exact hc
  have hρ := E.isScalingFactor_scalingFactor.1
  calc
    _ = E.scalingFactor ^ n * ∑ w : W, (E.energy (E.pullbackWord (List.ofFn w) u) : ℝ) :=
      E.energy_eq_sum_words n u
    _ ≤ E.scalingFactor ^ n * ∑ w : W, C * S w :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ ↦ hbound w)) (pow_nonneg hρ.le n)
    _ = C * (E.scalingFactor ^ n * ∑ w : W, S w) := by rw [← Finset.mul_sum]; ring

/-- Interpolation of cell means stays uniformly bounded and converges in
the ambient space. -/
theorem CornerProfile.cellMeanInterpolation_tendsto (P : Q.CornerProfile)
    (f : C(CarpetPoints, ℝ)) (g : ℕ → C(CarpetPoints, ℝ))
    (hG : ∀ (n : ℕ) (w : Fin n → Fin 8) x, g n (wordMap (List.ofFn w) x) =
      P.interpolate (cornerData (cornerAverage n (fun v ↦ continuousWordMean f (List.ofFn v)))
        (List.ofFn w)) x) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
    (∀ n, ‖continuousLp p (g n)‖ ≤ ‖f‖) ∧
      Tendsto (fun n ↦ continuousLp p (g n)) atTop (𝓝 (continuousLp p f)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have huniform (n : ℕ) (x : CarpetPoints) : |g n x| ≤ ‖f‖ := by
    obtain ⟨w, y, rfl⟩ := exists_wordMap_range n x
    rw [hG]
    have h := P.abs_interpolate_sub_le (cornerData (cornerAverage n (fun v ↦ continuousWordMean f (List.ofFn v))) (List.ofFn w)) y
      (c := 0) (R := ‖f‖) (fun i j ↦ by
        apply abs_cornerAverage_sub_le
        intro v _
        apply abs_wordMean_sub_le
        intro z
        simpa only [sub_zero, Real.norm_eq_abs] using f.norm_coe_le_norm (wordMap (List.ofFn v) z))
    simpa only [sub_zero] using h
  have hclose (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ x, |g n x - f x| ≤ ε := by
    obtain ⟨δ, hδ, hω⟩ :=
      Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
    filter_upwards [tendsto_wordMap_radius.eventually_lt_const (half_pos hδ)] with n hn
    intro x
    obtain ⟨w, y, rfl⟩ := exists_wordMap_range n x
    let x := wordMap (List.ofFn w) y
    rw [hG]
    apply P.abs_interpolate_sub_le
    intro i j
    let z := wordMap (List.ofFn w) (cornerPoint i j)
    apply abs_cornerAverage_sub_le
    intro v hv
    apply abs_wordMean_sub_le
    intro t
    let s := wordMap (List.ofFn v) t
    have hsz := wordMap_dist_le n v (mem_range_self t) (mem_incidentWords.mp hv)
    have hzx := wordMap_dist_le n w (mem_range_self (cornerPoint i j)) (mem_range_self y)
    have hsx : dist s x < δ := (dist_triangle s z x).trans_lt (by linarith)
    exact (by simpa only [Real.dist_eq] using hω hsx : |f s - f x| < ε).le
  refine ⟨fun n ↦ norm_carpetLp_le_of_ae_bound _ (norm_nonneg _)
    ((continuousLp_ae_eq p (g n)).mono
      fun x hx ↦ by rw [hx, Real.norm_eq_abs]; exact huniform n x), ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _), fun ε hε ↦ ?_⟩
  filter_upwards [hclose (ε / 2) (half_pos hε)] with n hn
  have hnorm : ‖continuousLp p (g n) - continuousLp p f‖ ≤ ε / 2 := by
    apply norm_carpetLp_le_of_ae_bound _ (half_pos hε).le
    filter_upwards [Lp.coeFn_sub (continuousLp p (g n)) (continuousLp p f),
      continuousLp_ae_eq p (g n), continuousLp_ae_eq p f] with x hx hy hz
    rw [hx, Pi.sub_apply, hy, hz, Real.norm_eq_abs]
    exact hn x
  linarith

private theorem mem_kernel_of_cornerProfile_continuous (P : Q.CornerProfile)
    (f : C(CarpetPoints, ℝ)) (hf : continuousLp p f ∈ E.domain) :
    (⟨continuousLp p f, hf⟩ : E.domain) ∈ Q.kernel := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt_p.le⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  obtain ⟨C, hC, hinterp⟩ := P.exists_interpolate_cellValues
  obtain ⟨D, hD, hgrid⟩ := E.exists_gridMean_energy_le
  choose g hg_dom hg_ker hG he using fun n ↦
    hinterp n (fun v ↦ continuousWordMean f (List.ofFn v))
  let u (n : ℕ) : E.domain := ⟨continuousLp p (g n), hg_dom n⟩
  let B := C * (D * (E.energy ⟨continuousLp p f, hf⟩ : ℝ))
  have henergy (n : ℕ) : (E.energy (u n) : ℝ) ≤ B :=
    (he n).trans (mul_le_mul_of_nonneg_left (hgrid n f hf) hC)
  obtain ⟨hL, hlim⟩ := P.cellMeanInterpolation_tendsto f g hG
  have hgraph (n : ℕ) : E.graphSeminorm (u n) ≤ ((B ^ p⁻¹) ^ p + ‖f‖ ^ p) ^ p⁻¹ := by
    apply E.graphSeminorm_le_of_le (u n) (hL n)
    rw [E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (henergy n) (inv_nonneg.mpr hp.le)
  have hQ : Q.rootSeminorm ≤ E.graphSeminorm := by
    intro v
    refine le_trans ?_ (E.rootSeminorm_le_graphSeminorm v)
    rw [Q.rootSeminorm_apply, E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr (Q.mass_le_energy _))
      (inv_nonneg.mpr hp.le)
  obtain ⟨v, hv, hvr⟩ := E.exists_domain_of_tendsto_of_seminorm_le Q.rootSeminorm hQ
    u (continuousLp p f) hgraph (R := 0)
    (fun r hr ↦ Eventually.of_forall fun n ↦ ((Q.mass_eq_zero_iff_root_eq_zero _).1
      ((Q.mem_kernel_iff _).1 (hg_ker n))) ▸ hr.le) hlim
  have hv' : v = ⟨continuousLp p f, hf⟩ := Subtype.ext hv
  rw [← hv']
  exact (Q.mem_kernel_iff _).2 ((Q.mass_eq_zero_iff_root_eq_zero _).2 (hvr.antisymm (apply_nonneg _ _)))

/-- Lemma 6.5. A kernel containing an opposite-side profile is the whole
energy domain. -/
theorem mass_eq_zero_of_profile
    {h : C(CarpetPoints, ℝ)} (hh : h ∈ Q.continuousKernel)
    (hL : ∀ x : CarpetPoints, (x : Plane) 0 = 0 → h x = 0)
    (hR : ∀ x : CarpetPoints, (x : Plane) 0 = 1 → h x = 1)
    (f : E.domain) : Q.mass f = 0 := by
  obtain ⟨P⟩ := Q.exists_cornerProfile_of_sides hh hL hR
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  choose u hu happrox using fun n ↦ E.regular_graph f (ε n) (hε n)
  let v (n : ℕ) : E.domain := ⟨continuousLp p (u n), hu n⟩
  have hdom (n : ℕ) : v n ∈ Q.kernel := mem_kernel_of_cornerProfile_continuous P (u n) (hu n)
  have hlim : Tendsto (fun n ↦ E.toGraph (v n)) atTop (𝓝 (E.toGraph f)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    change E.graphSeminorm (v n - f) ≤ ε n
    exact (happrox n).le
  exact (Q.mem_kernel_iff f).1 (Q.isClosed_graph_kernel.mem_of_tendsto hlim (Eventually.of_forall hdom))

/-- Theorem 6.6. Either the component is identically zero or every
continuous function in its kernel is constant. -/
theorem kernel_dichotomy :
    (∀ f ∈ Q.continuousKernel, ∃ a : ℝ, ∀ x : CarpetPoints, f x = a) ∨ ∀ f, Q.mass f = 0 := by
  by_contra! h
  obtain ⟨⟨f, hf, hnc⟩, ⟨g, hg⟩⟩ := h
  have he : ∃ x y : CarpetPoints, f x ≠ f y := by
    obtain ⟨x, hx⟩ := hnc (f (bottomPoint 0))
    exact ⟨x, bottomPoint 0, hx⟩
  obtain ⟨u, hu, hL, hR⟩ := Q.exists_profile_of_nonconstant_kernel hf he
  exact hg (Q.mass_eq_zero_of_profile hu hL hR g)

end CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent
