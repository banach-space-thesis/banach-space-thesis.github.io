import NonCalkinAlgebra.IdempotentResolvent
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open Complex Metric Set
universe u v
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The resolvent derivative. This proof is from Jireh Loreaux's
Mathlib.Analysis.Normed.Algebra.GelfandFormula at the installed mathlib pin
(Apache-2.0); the original file is preserved under source/mathlib-spectral.
Only this lemma is needed, so the unbuilt Gelfand-formula module is not imported. -/
theorem resolvent_hasDerivAt {a : A} {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    HasDerivAt (resolvent a) (-resolvent a z ^ 2) z := by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap ℂ A z - a) :=
    hasFDerivAt_ringInverse (𝕜 := ℂ) hz.unit
  have H₂ : HasDerivAt (fun z => algebraMap ℂ A z - a) 1 z := by
    simpa using (Algebra.linearMap ℂ A).hasDerivAt.sub_const a
  simpa [resolvent, sq, hz.unit_spec, ← Ring.inverse_unit hz.unit] using H₁.comp_hasDerivAt z H₂

/-- The actual normalized resolvent integral. Idempotence is a separate
theorem; it is not built into this definition. -/
def rieszCircle (a : A) (r : ℝ) : A :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0, r), resolvent a z

theorem resolvent_circleIntegrable (a : A) (r : ℝ) (hr : 0 ≤ r)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a) :
    CircleIntegrable (resolvent a) 0 r := by
  apply ContinuousOn.circleIntegrable hr
  intro z hz
  exact (resolvent_hasDerivAt (hcircle z hz)).continuousAt.continuousWithinAt

theorem circleIntegral_inv_outside (w : ℂ) (r : ℝ) (hr : 0 ≤ r) (hw : r < ‖w‖) :
    (∮ z in C(0, r), (z - w)⁻¹) = 0 := by
  have hne (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) : z - w ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hnorm : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    exact hw.not_ge (heq ▸ hnorm)
  have hc : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (closedBall (0 : ℂ) r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr (s := ∅) Set.countable_empty hc
  intro z hz
  exact (differentiableAt_id.sub_const w).inv (hne z (ball_subset_closedBall hz.1))

theorem rieszCircle_of_idempotent (e : A) (he : e * e = e) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) : rieszCircle e r = 1 - e := by
  have hz0 (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : z ≠ 0 := by
    have hn : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    intro heq
    rw [heq, norm_zero] at hn
    exact hr0.ne' hn.symm
  have hz1 (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : z - 1 ≠ 0 := by
    have hn : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    intro heq
    rw [sub_eq_zero.mp heq, norm_one] at hn
    exact hr1.ne hn.symm
  have hc0 : ContinuousOn (fun z : ℂ => z⁻¹) (sphere (0 : ℂ) r) :=
    continuousOn_id.inv₀ hz0
  have hc1 : ContinuousOn (fun z : ℂ => (z - 1)⁻¹) (sphere (0 : ℂ) r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hz1
  have hf0 : CircleIntegrable (fun z : ℂ => z⁻¹ • (1 - e)) 0 r :=
    (hc0.smul continuousOn_const).circleIntegrable hr0.le
  have hf1 : CircleIntegrable (fun z : ℂ => (z - 1)⁻¹ • e) 0 r :=
    (hc1.smul continuousOn_const).circleIntegrable hr0.le
  have hint : (∮ z in C(0, r), resolvent e z) =
      (2 * Real.pi * I : ℂ) • (1 - e) := by
    calc
      (∮ z in C(0, r), resolvent e z) =
          ∮ z in C(0, r), z⁻¹ • (1 - e) + (z - 1)⁻¹ • e := by
        apply circleIntegral.integral_congr hr0.le
        intro z hz
        exact resolvent_idempotent e he z (hz0 z hz) (sub_ne_zero.mp (hz1 z hz))
      _ = (∮ z in C(0, r), z⁻¹) • (1 - e) +
          (∮ z in C(0, r), (z - 1)⁻¹) • e := by
        rw [circleIntegral.integral_add hf0 hf1, circleIntegral.integral_smul_const,
          circleIntegral.integral_smul_const]
      _ = (2 * Real.pi * I : ℂ) • (1 - e) := by
        have hzero : (∮ z in C(0, r), z⁻¹) = (2 * Real.pi * I : ℂ) := by
          simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) hr0.ne'
        rw [hzero, circleIntegral_inv_outside 1 r hr0.le (by simpa only [norm_one] using hr1),
          zero_smul, add_zero]
  rw [rieszCircle, hint, inv_smul_smul₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

theorem continuousLinearMap_circleIntegral {B : Type v}
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (L : A →L[ℂ] B) {f : ℂ → A} {c : ℂ} {r : ℝ} (hf : CircleIntegrable f c r) :
    (∮ z in C(c, r), L (f z)) = L (∮ z in C(c, r), f z) := by
  unfold circleIntegral
  simpa only [map_smul] using L.intervalIntegral_comp_comm hf.out

theorem continuousLinearMap_rieszCircle {B : Type v}
    [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (L : A →L[ℂ] B) (a : A) (b : B) (r : ℝ) (hr : 0 ≤ r)
    (hf : CircleIntegrable (resolvent a) 0 r)
    (hmap : ∀ z ∈ sphere (0 : ℂ) r, L (resolvent a z) = resolvent b z) :
    L (rieszCircle a r) = rieszCircle b r := by
  unfold rieszCircle
  rw [map_smul, ← continuousLinearMap_circleIntegral L hf]
  exact congrArg (fun x : B => (2 * Real.pi * I : ℂ)⁻¹ • x)
    (circleIntegral.integral_congr hr hmap)

end NonCalkinAlgebra
