import PlanarMaximalMollification
import SmoothFiniteMaximum
import MollifyAbsBound
import WeakDerivativeMollification

/-!
# Smooth maxima of Sobolev mollifications with uniform moment bounds
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace CarpetEnergy

set_option maxHeartbeats 3300000 in
theorem exists_uniform_planar_smooth_maximal_profiles {p : ℝ} (hp : 1 < p)
    {u : PlanarCoordinates → ℝ} (hu : Measurable u) (hu₀ : ∀ x, 0 ≤ u x)
    (huI : Integrable u volume) (huP : Integrable (fun x ↦ u x ^ p) volume)
    (v : Fin 2 → PlanarCoordinates → ℝ)
    (hv : ∀ i, Measurable (v i)) (hvI : ∀ i, Integrable (v i) volume)
    (hvP : ∀ i, Integrable (fun x ↦ |v i x| ^ p) volume)
    (hD : ∀ i, HasWeakDirectionalDerivative volume u (v i) (planarDirection i)) :
    ∃ C > (0 : ℝ), ∀ (S : Finset ℕ), S.Nonempty →
      ∃ f : PlanarCoordinates → ℝ, ContDiff ℝ 1 f ∧ (∀ x, 0 ≤ f x) ∧
        (∀ n ∈ S, ∀ x, mollify volume n u x - 1 ≤ f x) ∧
        Integrable (fun x ↦ f x ^ p) volume ∧ (∫ x, f x ^ p ∂volume) ≤ C ∧
        ∀ i : Fin 2, Integrable (fun x ↦ |fderiv ℝ f x (planarDirection i)| ^ p) volume ∧
          (∫ x, |fderiv ℝ f x (planarDirection i)| ^ p ∂volume) ≤ C := by
  classical
  obtain ⟨A, hA, hLp⟩ := exists_planar_maximal_mollify_integral_bound hp
  let U := ∫ x, u x ^ p ∂volume
  let V (i : Fin 2) := ∫ x, |v i x| ^ p ∂volume
  let C := A * (1 + U + V 0 + V 1)
  have hU : 0 ≤ U := integral_nonneg fun x ↦ Real.rpow_nonneg (hu₀ x) _
  have hV (i : Fin 2) : 0 ≤ V i := integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hC : 0 < C := mul_pos hA (by linarith only [hU, hV 0, hV 1])
  have hUle : A * U ≤ C := mul_le_mul_of_nonneg_left (by linarith only [hV 0, hV 1]) hA.le
  have hVle (i : Fin 2) : A * V i ≤ C := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    fin_cases i
    · change V 0 ≤ 1 + U + V 0 + V 1
      linarith only [hU, hV 1]
    · change V 1 ≤ 1 + U + V 0 + V 1
      linarith only [hU, hV 0]
  refine ⟨C, hC, fun S hS ↦ ?_⟩
  have : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  let w (n : S) := mollify volume n.val u
  obtain ⟨f, hf, hf₀, hf₁, hf₂, hfD⟩ := exists_smooth_finite_maximum w
    (fun _ ↦ contDiff_mollify volume huI) (fun n x ↦ mollify_nonneg volume n.val hu₀ x)
  obtain ⟨hI, hB⟩ := hLp u f hu huI huP hf.continuous.measurable hu₀ hf₀ (fun x ↦ by
    obtain ⟨i, hi⟩ := hf₂ x
    exact ⟨i.val, hi⟩)
  refine ⟨f, hf, hf₀, fun n hn x ↦ hf₁ ⟨n, hn⟩ x, hI, hB.trans hUle, fun i ↦ ?_⟩
  let d (x : PlanarCoordinates) := |fderiv ℝ f x (planarDirection i)|
  have hd : Continuous d := ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).abs
  refine (hLp (fun x ↦ |v i x|) d (continuous_abs.measurable.comp (hv i)) (hvI i).abs
    (hvP i) hd.measurable (fun _ ↦ abs_nonneg _) (fun _ ↦ abs_nonneg _) ?_).imp_right
    (fun h ↦ h.trans (hVle i))
  intro x
  let Q (n : S) := |fderiv ℝ (w n) x (planarDirection i)|
  obtain ⟨n, _, hn⟩ := Finset.exists_max_image (Finset.univ : Finset S) Q Finset.univ_nonempty
  have hh : d x ≤ Q n := hfD x (planarDirection i) (Q n) (fun j ↦ hn j (Finset.mem_univ j))
  refine ⟨n.val, hh.trans ?_⟩
  change |fderiv ℝ (mollify volume n.val u) x (planarDirection i)| ≤ _
  rw [fderiv_mollify_apply_eq_mollify_of_weakDerivative huI (hD i)]
  exact abs_mollify_le_mollify_abs n.val x

end CarpetEnergy
