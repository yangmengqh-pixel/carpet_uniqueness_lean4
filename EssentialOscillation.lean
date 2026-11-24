import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Essential oscillation from two-sided Harnack bounds

Applying the Harnack inequality to the distances from the endpoints
of an enclosing interval contracts the essential oscillation.
-/

open Filter MeasureTheory Set

namespace CarpetEnergy

theorem essSup_sub_essInf_le_of_ae_pairwise_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [NeZero μ] {u : X → ℝ} {a b d : ℝ}
    (h : ∀ᵐ x ∂μ, u x ∈ Icc a b)
    (hd : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, u x - u y ≤ d) :
    essSup u μ - essInf u μ ≤ d := by
  have ha : IsBoundedUnder (· ≥ ·) (ae μ) u :=
    ⟨a, h.mono fun _ hx ↦ hx.1⟩
  have hb : IsBoundedUnder (· ≤ ·) (ae μ) u :=
    ⟨b, h.mono fun _ hx ↦ hx.2⟩
  have lower : ∀ᵐ x ∂μ, u x - d ≤ essInf u μ := by
    filter_upwards [hd] with x hx
    exact le_essInf_of_ae_le _ (hx.mono fun y hy ↦ by linarith)
      hb.isCoboundedUnder_flip
  have upper : essSup u μ ≤ essInf u μ + d :=
    essSup_le_of_ae_le _ (lower.mono fun x hx ↦ by linarith) ha.isCoboundedUnder_flip
  linarith only [upper]

theorem essSup_sub_essInf_le_of_ae_harnack {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ]
    {u : X → ℝ} (hu : Measurable u) {a b H : ℝ} (hH : 1 ≤ H)
    (h : ∀ᵐ x ∂μ, u x ∈ Icc a b)
    (hlo : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, u x - a ≤ H * (u y - a))
    (hhi : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, b - u x ≤ H * (b - u y)) :
    essSup u μ - essInf u μ ≤ ((H - 1) / (H + 1)) * (b - a) := by
  have hm : MeasurableSet {z : X × X | b - u z.1 ≤ H * (b - u z.2)} :=
    measurableSet_le (measurable_const.sub (hu.comp measurable_fst))
      (measurable_const.mul (measurable_const.sub (hu.comp measurable_snd)))
  have hhi' := (Measure.ae_ae_comm (μ := μ) (ν := μ) hm).mp hhi
  apply essSup_sub_essInf_le_of_ae_pairwise_le h
  filter_upwards [hlo, hhi'] with x hx h'x
  filter_upwards [hx, h'x] with y hy h'y
  have hH' : 0 < H + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hH']
  linarith only [hy, h'y]

end CarpetEnergy
