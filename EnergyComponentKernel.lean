import EnergyComponent
import CarpetConnected

/-!
# Kernels of self-similar components

The kernel is a closed subspace in the graph norm. It is stable under cell
pullbacks, symmetries, and scalar Lipschitz maps, and continuous pieces in
the kernel can be glued along a finite cell level.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent

variable {p : ℝ} {E : SelfSimilarPEnergy p} (Q : E.SelfSimilarComponent)

theorem mass_eq_zero_iff_root_eq_zero (f : E.domain) :
    Q.mass f = 0 ↔ Q.rootSeminorm f = 0 := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt_p
  rw [Q.rootSeminorm_apply]
  constructor
  · intro h
    rw [h, NNReal.coe_zero, Real.zero_rpow (inv_ne_zero hp.ne')]
  · intro h
    by_contra h'
    have hpos : 0 < (Q.mass f : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr h')
    exact (Real.rpow_pos_of_pos hpos p⁻¹).ne' h

/-- The common kernel of the component mass and its root seminorm. -/
def kernel : Submodule ℝ E.domain where
  carrier := {f | Q.mass f = 0}
  zero_mem' := (Q.mass_eq_zero_iff_root_eq_zero _).2 (map_zero _)
  add_mem' := by
    intro f g hf hg
    apply (Q.mass_eq_zero_iff_root_eq_zero _).2
    have h := map_add_le_add Q.rootSeminorm f g
    rw [(Q.mass_eq_zero_iff_root_eq_zero f).1 hf,
      (Q.mass_eq_zero_iff_root_eq_zero g).1 hg, add_zero] at h
    exact h.antisymm (apply_nonneg _ _)
  smul_mem' := by
    intro c f hf
    apply (Q.mass_eq_zero_iff_root_eq_zero _).2
    rw [map_smul_eq_mul, (Q.mass_eq_zero_iff_root_eq_zero f).1 hf, mul_zero]

theorem mem_kernel_iff (f : E.domain) : f ∈ Q.kernel ↔ Q.mass f = 0 := Iff.rfl

theorem constant_mem_kernel (c : ℝ) :
    (⟨constantLp p c, E.constant_mem c⟩ : E.domain) ∈ Q.kernel := by
  let f : E.domain := ⟨constantLp p c, E.constant_mem c⟩
  have hzero := (E.zero_iff_constant f).2 ⟨c, rfl⟩
  exact (Q.mem_kernel_iff f).mpr (nonpos_iff_eq_zero.mp ((Q.mass_le_energy f).trans_eq hzero))

theorem isClosed_graph_kernel :
    IsClosed {x : E.GraphDomain | E.graphToDomain x ∈ Q.kernel} := by
  let T : E.GraphDomain →ₗ[ℝ] E.domain :=
    { toFun := E.graphToDomain, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let r := Q.rootSeminorm.comp T
  have hr : Continuous r := by
    apply Seminorm.continuous_of_le (q := normSeminorm ℝ E.GraphDomain) continuous_norm
    intro z
    change Q.rootSeminorm (E.graphToDomain z) ≤ E.graphSeminorm (E.graphToDomain z)
    refine le_trans ?_ (E.rootSeminorm_le_graphSeminorm _)
    rw [Q.rootSeminorm_apply, E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _)
      (NNReal.coe_le_coe.mpr (Q.mass_le_energy _)) (inv_nonneg.mpr (zero_lt_one.trans E.one_lt_p).le)
  have he : {x : E.GraphDomain | E.graphToDomain x ∈ Q.kernel} = {x | r x = 0} := by
    ext x
    change Q.mass (E.graphToDomain x) = 0 ↔ Q.rootSeminorm (E.graphToDomain x) = 0
    exact Q.mass_eq_zero_iff_root_eq_zero _
  rw [he]
  exact isClosed_eq hr continuous_const

theorem pullback_mem_kernel (i : Fin 8) {f : E.domain} (hf : f ∈ Q.kernel) :
    E.pullback i f ∈ Q.kernel := by
  have h := Q.selfSimilar f
  rw [(Q.mem_kernel_iff f).1 hf, ENNReal.coe_zero] at h
  have hρ : ENNReal.ofReal E.scalingFactor ≠ 0 :=
    (ENNReal.ofReal_pos.mpr E.isScalingFactor_scalingFactor.1).ne'
  have hs := (mul_eq_zero.mp h.symm).resolve_left hρ
  have hi := Finset.single_le_sum
    (fun j _ ↦ show (0 : ℝ≥0∞) ≤ Q.mass (E.pullback j f) from bot_le) (Finset.mem_univ i)
  rw [hs] at hi
  exact (Q.mem_kernel_iff _).2 (ENNReal.coe_eq_zero.mp (nonpos_iff_eq_zero.mp hi))

theorem pullbackWord_mem_kernel (w : List (Fin 8)) {f : E.domain} (hf : f ∈ Q.kernel) :
    E.pullbackWord w f ∈ Q.kernel := by
  induction w generalizing f with
  | nil => exact hf
  | cons i w ih => exact ih (Q.pullback_mem_kernel i hf)

theorem pullbackSymmetry_mem_kernel (σ : SquareSymmetry) {f : E.domain} (hf : f ∈ Q.kernel) :
    E.pullbackSymmetry σ f ∈ Q.kernel :=
  (Q.mem_kernel_iff _).2 ((Q.symmetry σ f).trans ((Q.mem_kernel_iff _).1 hf))

/-- The continuous functions whose Lp classes lie in the component kernel. -/
def continuousKernel : Set C(CarpetPoints, ℝ) :=
  {u | ∃ hu : continuousLp p u ∈ E.domain, (⟨continuousLp p u, hu⟩ : E.domain) ∈ Q.kernel}

theorem continuousKernel_comp {u : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel)
    {φ : ℝ → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp u ∈ Q.continuousKernel := by
  obtain ⟨hu, hQu⟩ := hu
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let v := (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp u
  obtain ⟨g, hg, _⟩ := E.exists_energyMeasure_comp_le hφ f
  have hvg : continuousLp p v = (g : CarpetLp p) := by
    apply Lp.ext
    exact (continuousLp_ae_eq p v).trans
      ((hg.trans ((continuousLp_ae_eq p u).mono (fun _ hx ↦ congrArg φ hx))).symm)
  have hv : continuousLp p v ∈ E.domain := hvg.symm ▸ g.property
  have hv' : (⟨continuousLp p v, hv⟩ : E.domain) = g := Subtype.ext hvg
  refine ⟨hv, ?_⟩
  rw [hv']
  apply (Q.mem_kernel_iff g).2
  have h := Q.contraction hφ f g hg
  rw [(Q.mem_kernel_iff f).1 hQu, mul_zero] at h
  exact nonpos_iff_eq_zero.mp h

theorem continuousKernel_comp_symmetry {u : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel)
    (σ : SquareSymmetry) :
    u.comp ⟨carpetSymmetry σ, continuous_carpetSymmetry σ⟩ ∈ Q.continuousKernel := by
  obtain ⟨hu, hQu⟩ := hu
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let g := E.pullbackSymmetry σ f
  let v : C(CarpetPoints, ℝ) := u.comp ⟨carpetSymmetry σ, continuous_carpetSymmetry σ⟩
  have he : continuousLp p v = (g : CarpetLp p) := by
    apply Lp.ext
    have h := (measurePreserving_carpetSymmetry σ).quasiMeasurePreserving.ae_eq_comp
      (continuousLp_ae_eq p u)
    exact (continuousLp_ae_eq p v).trans ((symmetryPullback_isLpPullback σ (f : CarpetLp p)).trans h).symm
  have hv : continuousLp p v ∈ E.domain := he.symm ▸ g.property
  exact ⟨hv, (show (⟨continuousLp p v, hv⟩ : E.domain) = g from Subtype.ext he).symm ▸
    Q.pullbackSymmetry_mem_kernel σ hQu⟩

theorem continuousKernel_comp_wordMap {u : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel)
    (w : List (Fin 8)) :
    u.comp ⟨wordMap w, continuous_wordMap w⟩ ∈ Q.continuousKernel := by
  obtain ⟨hu, hQu⟩ := hu
  let f : E.domain := ⟨continuousLp p u, hu⟩
  let g := E.pullbackWord w f
  let v : C(CarpetPoints, ℝ) := u.comp ⟨wordMap w, continuous_wordMap w⟩
  have he : continuousLp p v = (g : CarpetLp p) := by
    apply Lp.ext
    have h := (quasiMeasurePreserving_wordMap w).ae_eq_comp (continuousLp_ae_eq p u)
    exact (continuousLp_ae_eq p v).trans ((E.pullbackWord_isLpPullback w f).trans h).symm
  have hv : continuousLp p v ∈ E.domain := he.symm ▸ g.property
  exact ⟨hv, (show (⟨continuousLp p v, hv⟩ : E.domain) = g from Subtype.ext he).symm ▸
    Q.pullbackWord_mem_kernel w hQu⟩

theorem continuousKernel_const (a : ℝ) : ContinuousMap.const CarpetPoints a ∈ Q.continuousKernel := by
  have h : continuousLp p (ContinuousMap.const CarpetPoints a) = constantLp p a := by
    apply Lp.ext
    exact (continuousLp_ae_eq p _).trans (Lp.coeFn_const (ENNReal.ofReal p) carpetMeasure a).symm
  have hm : continuousLp p (ContinuousMap.const CarpetPoints a) ∈ E.domain := h.symm ▸ E.constant_mem a
  exact ⟨hm, (show (⟨_, hm⟩ : E.domain) = ⟨constantLp p a, E.constant_mem a⟩ from
    Subtype.ext h).symm ▸ Q.constant_mem_kernel a⟩

theorem continuousKernel_add {u v : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel)
    (hv : v ∈ Q.continuousKernel) : (u + v) ∈ Q.continuousKernel := by
  obtain ⟨hu, hk⟩ := hu
  obtain ⟨hv, hl⟩ := hv
  have he : continuousLp p (u + v) = continuousLp p u + continuousLp p v := by
    apply Lp.ext
    filter_upwards [continuousLp_ae_eq p (u + v), continuousLp_ae_eq p u, continuousLp_ae_eq p v,
      Lp.coeFn_add (continuousLp p u) (continuousLp p v)] with x h₁ h₂ h₃ h₄
    rw [h₁, h₄, Pi.add_apply, h₂, h₃]
    rfl
  have hm : continuousLp p (u + v) ∈ E.domain := he.symm ▸ E.domain.add_mem hu hv
  have hs : (⟨continuousLp p (u + v), hm⟩ : E.domain) = ⟨continuousLp p u, hu⟩ + ⟨continuousLp p v, hv⟩ :=
    Subtype.ext he
  exact ⟨hm, hs.symm ▸ Q.kernel.add_mem hk hl⟩

theorem continuousKernel_smul (a : ℝ) {u : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel) :
    (a • u) ∈ Q.continuousKernel := by
  obtain ⟨hu, hk⟩ := hu
  have he : continuousLp p (a • u) = a • continuousLp p u := by
    apply Lp.ext
    filter_upwards [continuousLp_ae_eq p (a • u), continuousLp_ae_eq p u,
      Lp.coeFn_smul a (continuousLp p u)] with x h₁ h₂ h₃
    rw [h₁, h₃, Pi.smul_apply, h₂]
    rfl
  have hm : continuousLp p (a • u) ∈ E.domain := he.symm ▸ E.domain.smul_mem a hu
  have hs : (⟨continuousLp p (a • u), hm⟩ : E.domain) = a • ⟨continuousLp p u, hu⟩ := Subtype.ext he
  exact ⟨hm, hs.symm ▸ Q.kernel.smul_mem a hk⟩

theorem continuousKernel_sub {u v : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel)
    (hv : v ∈ Q.continuousKernel) : (u - v) ∈ Q.continuousKernel := by
  simpa only [neg_one_smul, sub_eq_add_neg] using Q.continuousKernel_add hu (Q.continuousKernel_smul (-1) hv)

/-- A globally Lipschitz function agreeing with the square on the given interval. -/
theorem exists_clipped_square (M : ℝ≥0) :
    ∃ φ : ℝ → ℝ, LipschitzWith (2 * M) φ ∧ ∀ t : ℝ, |t| ≤ (M : ℝ) → φ t = t * t := by
  let c (t : ℝ) := min (max t (-(M : ℝ))) M
  have hc : LipschitzWith 1 c := (LipschitzWith.id.max_const (-(M : ℝ))).min_const M
  have hbound (t : ℝ) : |c t| ≤ M := abs_le.mpr
    ⟨le_min (le_max_right _ _) (by linarith [M.coe_nonneg]), min_le_right _ _⟩
  refine ⟨fun t ↦ c t * c t, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hsum : |c x + c y| ≤ (2 : ℝ) * M := by
      exact (abs_add_le _ _).trans (by rw [two_mul]; exact add_le_add (hbound x) (hbound y))
    have hd := hc.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
    rw [Real.dist_eq, show c x * c x - c y * c y = (c x + c y) * (c x - c y) by ring, abs_mul]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, Real.dist_eq] using
      mul_le_mul hsum hd (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * M)
  · intro t ht
    have ht' := abs_le.mp ht
    change c t * c t = t * t
    dsimp only [c]
    rw [max_eq_left ht'.1, min_eq_left ht'.2]

private theorem continuousKernel_square {u : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel) :
    (u * u) ∈ Q.continuousKernel := by
  let M : ℝ≥0 := ⟨‖u‖, norm_nonneg _⟩
  obtain ⟨φ, hφ, he⟩ := exists_clipped_square M
  have hh := Q.continuousKernel_comp hu hφ
  have hv : (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp u = u * u := by
    ext x
    exact he (u x) (by
      change |u x| ≤ ‖u‖
      simpa only [Real.norm_eq_abs] using u.norm_coe_le_norm x)
  exact hv ▸ hh

/-- The continuous kernel is closed under pointwise multiplication. -/
theorem continuousKernel_mul {u v : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel)
    (hv : v ∈ Q.continuousKernel) : (u * v) ∈ Q.continuousKernel := by
  have hsum := Q.continuousKernel_square (Q.continuousKernel_add hu hv)
  have hdiff := Q.continuousKernel_square (Q.continuousKernel_sub hu hv)
  have he : (1 / 4 : ℝ) • ((u + v) * (u + v) - (u - v) * (u - v)) = u * v := by
    ext x
    change (1 / 4 : ℝ) * ((u x + v x) * (u x + v x) - (u x - v x) * (u x - v x)) = u x * v x
    ring
  exact he ▸ Q.continuousKernel_smul (1 / 4) (Q.continuousKernel_sub hsum hdiff)

/-- The continuous kernel is closed under pointwise maximum and minimum. -/
theorem continuousKernel_lattice {u v : C(CarpetPoints, ℝ)} (hu : u ∈ Q.continuousKernel)
    (hv : v ∈ Q.continuousKernel) : (u ⊔ v) ∈ Q.continuousKernel ∧ (u ⊓ v) ∈ Q.continuousKernel := by
  let φ (x : ℝ) := max x 0
  have hφ : LipschitzWith 1 φ := LipschitzWith.id.max_const 0
  let w := (⟨φ, hφ.continuous⟩ : C(ℝ, ℝ)).comp (u - v)
  have hw : w ∈ Q.continuousKernel := Q.continuousKernel_comp (Q.continuousKernel_sub hu hv) hφ
  have hmax : w + v = u ⊔ v := by
    ext x
    change max (u x - v x) 0 + v x = max (u x) (v x)
    by_cases h : v x ≤ u x
    · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h), sub_add_cancel]
    · rw [max_eq_right (le_of_not_ge h), max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), zero_add]
  have hmin : u - w = u ⊓ v := by
    ext x
    change u x - max (u x - v x) 0 = min (u x) (v x)
    by_cases h : v x ≤ u x
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h), sub_sub_cancel]
    · rw [min_eq_left (le_of_not_ge h), max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), sub_zero]
  exact ⟨hmax ▸ Q.continuousKernel_add hw hv, hmin ▸ Q.continuousKernel_sub hu hw⟩

/-- The finite-level gluing assertion for the continuous component kernel. -/
theorem continuousKernel_of_cellwise (u : C(CarpetPoints, ℝ)) (n : ℕ)
    (h : ∀ w : Fin n → Fin 8, u.comp ⟨wordMap (List.ofFn w), continuous_wordMap _⟩ ∈ Q.continuousKernel) :
    u ∈ Q.continuousKernel := by
  induction n generalizing u with
  | zero => exact h Fin.elim0
  | succ n ih =>
    have hcell (i : Fin 8) :
        u.comp ⟨cellMap i, continuous_cellMap i⟩ ∈ Q.continuousKernel := by
      apply ih
      intro w
      have hw := h (Fin.cons i w)
      rw [List.ofFn_cons] at hw
      exact hw
    choose hdom hker using hcell
    have hu : continuousLp p u ∈ E.domain := (E.continuous_gluing u).2 hdom
    let u' : E.domain := ⟨continuousLp p u, hu⟩
    have hmass (i : Fin 8) : Q.mass (E.pullback i u') = 0 := by
      have hi : E.pullback i u' = ⟨_, hdom i⟩ := Subtype.ext (cellPullback_continuousLp p i u)
      rw [hi]
      exact (Q.mem_kernel_iff _).1 (hker i)
    refine ⟨hu, (Q.mem_kernel_iff u').2 ?_⟩
    apply ENNReal.coe_eq_zero.mp
    rw [Q.selfSimilar, Finset.sum_eq_zero (fun i _ ↦ by rw [hmass, ENNReal.coe_zero]), mul_zero]

end CarpetEnergy.SelfSimilarPEnergy.SelfSimilarComponent
