import EnergyPiecewiseHarmonic
import EnergyFoldingAmplification
import EnergySeminorm
import EnergyLocality
import ScalarPowerIncrement
import EnergyLocalMidpointDeficit

/-!
# Local harmonic comparison using clipped tests

The test is half the difference of two continuous profiles, truncated
at the two cutoff levels. Outside the middle region its energy effect
is controlled solely by the cutoff energy.
-/

open MeasureTheory Set

namespace CarpetEnergy.SelfSimilarPEnergy

variable {p : ℝ} (E : SelfSimilarPEnergy p)

noncomputable section

private abbrev mass (f : E.continuousCore) (A : Set CarpetPoints) : ℝ :=
  (E.energyMeasure (E.continuousCoreToDomain f)).real A

private abbrev root (f : E.continuousCore) : ℝ :=
  E.rootSeminorm (E.continuousCoreToDomain f)

/-- A continuous profile minimizes energy under continuous finite-energy
variations vanishing outside the indicated set. -/
def IsHarmonicOn (U : Set CarpetPoints) (f : E.continuousCore) : Prop :=
  ∀ v : E.continuousCore, (∀ x ∉ U, v.val x = 0) →
    E.energy (E.continuousCoreToDomain f) ≤
      E.energy (E.continuousCoreToDomain (f + v))

theorem isHarmonicOn_of_interior {U : Set CarpetPoints} (hU : U ⊆ carpetOuterBoundaryᶜ)
    {f : E.continuousCore} (hf : E.IsInteriorHarmonic (E.continuousCoreToDomain f)) :
    E.IsHarmonicOn U f := by
  intro v hv
  rw [map_add]
  exact hf v.val v.property (fun x hx ↦ hv x (fun hxU ↦ hU hxU hx))

private theorem mass_eq_of_eqOn {A : Set CarpetPoints} (hA : MeasurableSet A)
    {f g : E.continuousCore} (h : EqOn f.val g.val A) : mass E f A = mass E g A := by
  exact congrArg ENNReal.toReal
    (E.energyMeasure_apply_eq_of_sub_constant hA f.val g.val f.property g.property
      (fun x hx ↦ sub_eq_zero.mpr (h hx)))

private theorem domain_mass_le_add_increment {A : Set CarpetPoints} (hA : MeasurableSet A)
    (f g : E.domain) {M b : ℝ} (hf : E.rootSeminorm f ≤ M) (hg : E.rootSeminorm g ≤ b) :
    (E.energyMeasure (f + g)).real A ≤ (E.energyMeasure f).real A + p * b * (M + b) ^ (p - 1) := by
  let S : Seminorm ℝ E.domain := E.energyMeasureSeminorm A hA
  have hpow (u : E.domain) : (S u) ^ p = (E.energyMeasure u).real A := by
    change (E.energyMeasureSeminorm A hA u) ^ p = _
    rw [E.energyMeasureSeminorm_apply]
    exact Real.rpow_inv_rpow ENNReal.toReal_nonneg (zero_lt_one.trans E.one_lt_p).ne'
  have hs (u : E.domain) : S u ≤ E.rootSeminorm u :=
    E.energyMeasureSeminorm_le_rootSeminorm A hA u
  have hfb : S f ≤ M := (hs f).trans hf
  have hgb : S g ≤ b := (hs g).trans hg
  have hb : 0 ≤ b := (apply_nonneg S g).trans hgb
  have hsum : S (f + g) ≤ S f + b :=
    (S.add_le' f g).trans (add_le_add_right hgb (S f))
  have hi := rpow_increment_le E.one_lt_p (apply_nonneg S f) hb hfb
  rw [hpow f] at hi
  calc
    (E.energyMeasure (f + g)).real A = S (f + g) ^ p := (hpow _).symm
    _ ≤ (S f + b) ^ p :=
      Real.rpow_le_rpow (apply_nonneg S _) hsum (zero_lt_one.trans E.one_lt_p).le
    _ ≤ (E.energyMeasure f).real A + p * b * (M + b) ^ (p - 1) := hi

private theorem mass_le_add_increment {A : Set CarpetPoints} (hA : MeasurableSet A)
    (f g : E.continuousCore) {M b : ℝ} (hf : root E f ≤ M) (hg : root E g ≤ b) :
    mass E (f + g) A ≤ mass E f A + p * b * (M + b) ^ (p - 1) := by
  unfold mass
  rw [map_add]
  exact domain_mass_le_add_increment E hA _ _ hf hg

private def coreSup (f g : E.continuousCore) : E.continuousCore :=
  ⟨f.val ⊔ g.val, (E.zeroComponent.continuousKernel_lattice
    ⟨f.property, rfl⟩ ⟨g.property, rfl⟩).1.choose⟩

private def coreInf (f g : E.continuousCore) : E.continuousCore :=
  ⟨f.val ⊓ g.val, (E.zeroComponent.continuousKernel_lattice
    ⟨f.property, rfl⟩ ⟨g.property, rfl⟩).2.choose⟩

/-- Half the difference, clipped by a variable nonnegative cutoff. -/
def clippedTest (f g k : E.continuousCore) : E.continuousCore :=
  (1 / 2 : ℝ) • coreInf E (coreSup E (f - g) (-k)) k

theorem clippedTest_apply (f g k : E.continuousCore) (x : CarpetPoints) :
    (E.clippedTest f g k).val x =
      (1 / 2 : ℝ) * min (max (f.val x - g.val x) (- k.val x)) (k.val x) := rfl

set_option maxHeartbeats 1000000 in
/-- On the middle region the clipped variation takes the harmonic
profile to the midpoint. On the other two regions the energy increment
is bounded by the energy of half the cutoff. -/
theorem clipped_harmonic_mass_le_midpoint {U : Set CarpetPoints} (hU : MeasurableSet U)
    (f g k : E.continuousCore) (hg : E.IsHarmonicOn U g)
    (hk : ∀ x, 0 ≤ k.val x) (hkU : ∀ x ∉ U, k.val x = 0)
    {M b : ℝ} (hgM : root E g ≤ M) (hkb : root E ((1 / 2 : ℝ) • k) ≤ b) :
    let A := U ∩ {x | |f.val x - g.val x| ≤ k.val x}
    mass E g A ≤ mass E ((1 / 2 : ℝ) • (f + g)) A +
      2 * (p * b * (M + b) ^ (p - 1)) := by
  let A := U ∩ {x | |f.val x - g.val x| ≤ k.val x}
  let P := U ∩ {x | k.val x < f.val x - g.val x}
  let N := U ∩ {x | f.val x - g.val x < -k.val x}
  let m := (1 / 2 : ℝ) • (f + g)
  let v := (1 / 2 : ℝ) • k
  let t := E.clippedTest f g k
  let q := g + t
  have hd := f.val.continuous.sub g.val.continuous
  have hA : MeasurableSet A := hU.inter (measurableSet_le hd.abs.measurable k.val.continuous.measurable)
  have hP : MeasurableSet P := hU.inter (measurableSet_lt k.val.continuous.measurable hd.measurable)
  have hN : MeasurableSet N := hU.inter (measurableSet_lt hd.measurable k.val.continuous.neg.measurable)
  have htU (x) (hx : x ∉ U) : t.val x = 0 := by
    dsimp only [t]
    rw [E.clippedTest_apply, hkU x hx, neg_zero, min_eq_right (le_max_right _ _), mul_zero]
  have hq : mass E g U ≤ mass E q U := by
    have h := hg t htU
    have ht : E.energyMeasure (E.continuousCoreToDomain g) univ ≤
        E.energyMeasure (E.continuousCoreToDomain q) univ := by
      rw [E.energyMeasure_univ, E.energyMeasure_univ]
      exact ENNReal.coe_le_coe.mpr h
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) ht
    change mass E g univ ≤ mass E q univ at hh
    have he : mass E q Uᶜ = mass E g Uᶜ :=
      mass_eq_of_eqOn E hU.compl (fun x hx ↦ by
        change g.val x + t.val x = g.val x
        rw [htU x hx, add_zero])
    have hsplit (u : E.continuousCore) : mass E u univ = mass E u U + mass E u Uᶜ := by
      unfold mass
      rw [← union_compl_self U, measureReal_union disjoint_compl_right hU.compl]
    rw [hsplit g, hsplit q, he] at hh
    exact le_of_add_le_add_right hh
  have mid_bounds (x : CarpetPoints) (hx : x ∈ A) :
      -k.val x ≤ f.val x - g.val x ∧ f.val x - g.val x ≤ k.val x :=
    abs_le.mp hx.2
  have pos_bound (x : CarpetPoints) (hx : x ∈ P) : k.val x < f.val x - g.val x := hx.2
  have neg_bound (x : CarpetPoints) (hx : x ∈ N) : f.val x - g.val x < -k.val x := hx.2
  have hAP : Disjoint A P :=
    Set.disjoint_left.mpr (fun {_} hx hy ↦ (mid_bounds _ hx).2.not_gt (pos_bound _ hy))
  have hAN : Disjoint A N :=
    Set.disjoint_left.mpr (fun {_} hx hy ↦ (mid_bounds _ hx).1.not_gt (neg_bound _ hy))
  have hPN : Disjoint P N := Set.disjoint_left.mpr (fun {x} hx hy ↦ by
    linarith only [pos_bound x hx, neg_bound x hy, hk x])
  have hpart : A ∪ P ∪ N = U := by
    ext x
    change ((x ∈ U ∧ |f.val x - g.val x| ≤ k.val x) ∨
      (x ∈ U ∧ k.val x < f.val x - g.val x)) ∨
      (x ∈ U ∧ f.val x - g.val x < -k.val x) ↔ x ∈ U
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hx
      rcases lt_or_ge (f.val x - g.val x) (-k.val x) with h | h
      · exact Or.inr ⟨hx, h⟩
      rcases lt_or_ge (k.val x) (f.val x - g.val x) with h' | h'
      · exact Or.inl (Or.inr ⟨hx, h'⟩)
      exact Or.inl (Or.inl ⟨hx, abs_le.mpr ⟨h, h'⟩⟩)
  have hmid : mass E q A = mass E m A :=
    mass_eq_of_eqOn E hA (fun x hx ↦ by
      change g.val x + (E.clippedTest f g k).val x = (1 / 2 : ℝ) * (f.val x + g.val x)
      rw [E.clippedTest_apply, max_eq_left (mid_bounds x hx).1, min_eq_left (mid_bounds x hx).2]
      ring)
  have hplus : mass E q P = mass E (g + v) P :=
    mass_eq_of_eqOn E hP (fun x hx ↦ by
      change g.val x + (E.clippedTest f g k).val x = g.val x + (1 / 2 : ℝ) * k.val x
      rw [E.clippedTest_apply, min_eq_right ((pos_bound x hx).le.trans (le_max_left _ _))])
  have hminus : mass E q N = mass E (g + (-v)) N :=
    mass_eq_of_eqOn E hN (fun x hx ↦ by
      change g.val x + (E.clippedTest f g k).val x = g.val x + -((1 / 2 : ℝ) * k.val x)
      rw [E.clippedTest_apply, max_eq_right (neg_bound x hx).le, min_eq_left (by linarith only [hk x])]
      ring)
  have hbminus : root E (-v) ≤ b := by
    change E.rootSeminorm (E.continuousCoreToDomain (-v)) ≤ b
    rw [map_neg, map_neg_eq_map]
    exact hkb
  have hp := mass_le_add_increment E hP g v hgM hkb
  have hn := mass_le_add_increment E hN g (-v) hgM hbminus
  have hsplit (u : E.continuousCore) : mass E u U = mass E u A + mass E u P + mass E u N := by
    unfold mass
    rw [← hpart, measureReal_union (disjoint_sup_left.mpr ⟨hAN, hPN⟩) hN,
      measureReal_union hAP hP]
  rw [hsplit g, hsplit q, hmid, hplus, hminus] at hq
  change mass E g A ≤ mass E m A + _
  linarith only [hq, hp, hn]

private theorem mass_le_root_rpow (f : E.continuousCore) (A : Set CarpetPoints) :
    mass E f A ≤ (root E f) ^ p := by
  have h : (root E f) ^ p = (E.energy (E.continuousCoreToDomain f) : ℝ) := by
    unfold root
    rw [E.rootSeminorm_apply]
    exact Real.rpow_inv_rpow (NNReal.coe_nonneg _) (zero_lt_one.trans E.one_lt_p).ne'
  rw [h]
  have hm := measureReal_mono (μ := E.energyMeasure (E.continuousCoreToDomain f)) (subset_univ A)
  unfold mass
  refine hm.trans (le_of_eq ?_)
  rw [Measure.real, E.energyMeasure_univ, ENNReal.coe_toReal]

set_option maxHeartbeats 800000 in
/-- Harmonic profiles of bounded energy that are close on a Borel set
have a small energy difference there. The two error terms can be made
small by first choosing the midpoint tolerance and then the cutoff size. -/
theorem exists_harmonic_mass_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ {U V : Set CarpetPoints} (_hU : MeasurableSet U) (_hVU : V ⊆ U)
      (f g k : E.continuousCore) (_hf : E.IsHarmonicOn U f) (_hg : E.IsHarmonicOn U g)
      (_hk : ∀ x, 0 ≤ k.val x) (_hkU : ∀ x ∉ U, k.val x = 0)
      (_hV : ∀ x ∈ V, |f.val x - g.val x| ≤ k.val x)
      {M b : ℝ} (_hfM : root E f ≤ M) (_hgM : root E g ≤ M)
      (_hkb : root E ((1 / 2 : ℝ) • k) ≤ b),
      mass E (f - g) V ≤ 2 * ε * M ^ p + 2 * C * (p * b * (M + b) ^ (p - 1)) := by
  obtain ⟨C, hC, hmid⟩ := E.exists_energyMeasure_midpoint_deficit ε hε
  refine ⟨C, hC, ?_⟩
  intro U V hU hVU f g k hf hg hk hkU hV M b hfM hgM hkb
  let A := U ∩ {x | |f.val x - g.val x| ≤ k.val x}
  let m := (1 / 2 : ℝ) • (f + g)
  let D := p * b * (M + b) ^ (p - 1)
  have hA : MeasurableSet A := hU.inter
    (measurableSet_le (f.val.continuous.sub g.val.continuous).abs.measurable k.val.continuous.measurable)
  have hga : mass E g A ≤ mass E m A + 2 * D :=
    E.clipped_harmonic_mass_le_midpoint hU f g k hg hk hkU hgM hkb
  have hfa : mass E f A ≤ mass E m A + 2 * D := by
    have h := E.clipped_harmonic_mass_le_midpoint hU g f k hf hk hkU hfM hkb
    change mass E f (U ∩ {x | |g.val x - f.val x| ≤ k.val x}) ≤
      mass E ((1 / 2 : ℝ) • (g + f)) (U ∩ {x | |g.val x - f.val x| ≤ k.val x}) + 2 * D at h
    have hset : U ∩ {x | |g.val x - f.val x| ≤ k.val x} = A := by
      ext x
      change (x ∈ U ∧ |g.val x - f.val x| ≤ k.val x) ↔ (x ∈ U ∧ |f.val x - g.val x| ≤ k.val x)
      rw [abs_sub_comm (g.val x) (f.val x)]
    rw [hset, add_comm g f] at h
    exact h
  have hfinite (u : E.continuousCore) : E.energyMeasure (E.continuousCoreToDomain u) A ≠ ⊤ :=
    measure_ne_top _ _
  have hm := Measure.le_iff'.mp (hmid f g) A
  simp only [add_apply, smul_apply, smul_eq_mul] at hm
  have hsum : E.energyMeasure (E.continuousCoreToDomain f) A +
    E.energyMeasure (E.continuousCoreToDomain g) A ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinite f, hfinite g⟩
  have hcoef : 0 ≤ ε + C / 2 := by positivity
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum) hm
  rw [ENNReal.toReal_add (hfinite (f - g)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite m)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_ofReal hcoef, ENNReal.toReal_add (hfinite f) (hfinite g)] at hr
  change mass E (f - g) A + C * mass E m A ≤
    (ε + C / 2) * (mass E f A + mass E g A) at hr
  have hdiff : (mass E f A + mass E g A) / 2 - mass E m A ≤ 2 * D := by
    linarith only [hfa, hga]
  have hprod := mul_le_mul_of_nonneg_left hdiff hC
  have hp := (zero_lt_one.trans E.one_lt_p).le
  have hfb := (mass_le_root_rpow E f A).trans
    (Real.rpow_le_rpow (apply_nonneg E.rootSeminorm _) hfM hp)
  have hgb := (mass_le_root_rpow E g A).trans
    (Real.rpow_le_rpow (apply_nonneg E.rootSeminorm _) hgM hp)
  have hsum' : mass E f A + mass E g A ≤ 2 * M ^ p := by linarith only [hfb, hgb]
  have hsmall := mul_le_mul_of_nonneg_left hsum' hε.le
  have hsub : V ⊆ A := fun x hx ↦ ⟨hVU hx, hV x hx⟩
  have hv : mass E (f - g) V ≤ mass E (f - g) A :=
    measureReal_mono hsub (hfinite (f - g))
  change mass E (f - g) V ≤ 2 * ε * M ^ p + 2 * C * D
  nlinarith only [hr, hprod, hsmall, hv]

end

end CarpetEnergy.SelfSimilarPEnergy
