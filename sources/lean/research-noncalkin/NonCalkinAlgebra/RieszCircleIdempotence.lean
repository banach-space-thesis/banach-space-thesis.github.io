import NonCalkinAlgebra.ResolventIdentity
import NonCalkinAlgebra.RieszCircleAnnulus
import NonCalkinAlgebra.CauchyTransform

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open Complex Metric Set
universe u
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Integrating the second resolvent identity on the outer circle. -/
theorem rieszCircle_mul_resolvent (a : A) (R : ℝ) (hR : 0 < R)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) R, z ∈ resolventSet ℂ a)
    (w : ℂ) (hwin : w ∈ ball (0 : ℂ) R) (hw : w ∈ resolventSet ℂ a) :
    rieszCircle a R * resolvent a w =
      resolvent a w - cauchyTransform (resolvent a) R w := by
  let κ : ℂ := (2 * Real.pi * I)⁻¹
  have htwo : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hκ : κ * (2 * Real.pi * I) = 1 := inv_mul_cancel₀ htwo
  have hzw (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ≠ w := by
    have hnz : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    have hnw : ‖w‖ < R := by simpa only [mem_ball, dist_zero_right] using hwin
    intro heq
    exact hnw.ne (heq ▸ hnz)
  have hk : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere (0 : ℂ) R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => sub_ne_zero.mpr (hzw z hz))
  have hc : ContinuousOn (resolvent a) (sphere (0 : ℂ) R) := by
    intro z hz
    exact (resolvent_hasDerivAt (hcircle z hz)).continuousAt.continuousWithinAt
  have hf := resolvent_circleIntegrable a R hR.le hcircle
  have hkconst : CircleIntegrable (fun z : ℂ => (z - w)⁻¹ • resolvent a w) 0 R :=
    (hk.smul continuousOn_const).circleIntegrable hR.le
  have hkres : CircleIntegrable (fun z : ℂ => (z - w)⁻¹ • resolvent a z) 0 R :=
    (hk.smul hc).circleIntegrable hR.le
  have hprod : (∮ z in C(0, R), resolvent a z) * resolvent a w =
      ∮ z in C(0, R), resolvent a z * resolvent a w :=
    (continuousLinearMap_circleIntegral
      ((ContinuousLinearMap.mul ℂ A).flip (resolvent a w)) hf).symm
  have hpoint : EqOn (fun z => resolvent a z * resolvent a w)
      (fun z => (z - w)⁻¹ • resolvent a w - (z - w)⁻¹ • resolvent a z)
      (sphere (0 : ℂ) R) := by
    intro z hz
    change resolvent a z * resolvent a w =
      (z - w)⁻¹ • resolvent a w - (z - w)⁻¹ • resolvent a z
    rw [resolvent_mul_identity a z w (hcircle z hz) hw (hzw z hz), smul_sub]
  have hscalar : (∮ z in C(0, R), (z - w)⁻¹) = (2 * Real.pi * I : ℂ) :=
    circleIntegral.integral_sub_inv_of_mem_ball hwin
  change (κ • (∮ z in C(0, R), resolvent a z)) * resolvent a w = _
  rw [smul_mul_assoc, hprod, circleIntegral.integral_congr hR.le hpoint,
    circleIntegral.integral_sub hkconst hkres, circleIntegral.integral_smul_const,
    hscalar, smul_sub, smul_smul]
  change (κ * (2 * Real.pi * I)) • resolvent a w -
    cauchyTransform (resolvent a) R w = _
  rw [hκ, one_smul]

/-- Nested resolvent circles give nested projections. The vanishing Cauchy
transform integral supplies the analytic step, without a Fubini assumption. -/
theorem rieszCircle_mul_nested (a : A) (r R : ℝ) (hr : 0 < r) (hrr : r < R)
    (hinner : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a)
    (houter : ∀ z ∈ sphere (0 : ℂ) R, z ∈ resolventSet ℂ a) :
    rieszCircle a R * rieszCircle a r = rieszCircle a r := by
  let κ : ℂ := (2 * Real.pi * I)⁻¹
  have hR : 0 < R := hr.trans hrr
  have hfi := resolvent_circleIntegrable a r hr.le hinner
  have hfo := resolvent_circleIntegrable a R hR.le houter
  have hFint : CircleIntegrable (cauchyTransform (resolvent a) R) 0 r :=
    ((cauchyTransform_continuousOn_innerBall (resolvent a) R r hR hrr hfo).mono
      sphere_subset_closedBall).circleIntegrable hr.le
  have hprod : rieszCircle a R * (∮ w in C(0, r), resolvent a w) =
      ∮ w in C(0, r), rieszCircle a R * resolvent a w :=
    (continuousLinearMap_circleIntegral
      (ContinuousLinearMap.mul ℂ A (rieszCircle a R)) hfi).symm
  have hpoint : EqOn (fun w => rieszCircle a R * resolvent a w)
      (fun w => resolvent a w - cauchyTransform (resolvent a) R w) (sphere (0 : ℂ) r) := by
    intro w hw
    have hwin : w ∈ ball (0 : ℂ) R := by
      have hn : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right] using hw
      simpa only [mem_ball, dist_zero_right, hn] using hrr
    exact rieszCircle_mul_resolvent a R hR houter w hwin (hinner w hw)
  calc
    rieszCircle a R * rieszCircle a r = κ •
        (rieszCircle a R * (∮ w in C(0, r), resolvent a w)) := by
      change rieszCircle a R * (κ • (∮ w in C(0, r), resolvent a w)) = _
      rw [mul_smul_comm]
    _ = κ • (∮ w in C(0, r), resolvent a w - cauchyTransform (resolvent a) R w) := by
      rw [hprod, circleIntegral.integral_congr hr.le hpoint]
    _ = κ • (∮ w in C(0, r), resolvent a w) := by
      rw [circleIntegral.integral_sub hfi hFint,
        cauchyTransform_circleIntegral_zero (resolvent a) R r hR hr.le hrr hfo, sub_zero]
    _ = rieszCircle a r := rfl

/-- A genuine Riesz projection theorem for arbitrary unital complex Banach
algebras, with the actual inherited norm and the actual contour integral. -/
theorem rieszCircle_isIdempotent (a : A) (r : ℝ) (hr : 0 < r)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) r, z ∈ resolventSet ℂ a) :
    rieszCircle a r * rieszCircle a r = rieszCircle a r := by
  obtain ⟨R, hrr, hannulus⟩ := exists_larger_resolvent_annulus a r (fun z hz =>
    hcircle z (by simpa only [mem_sphere, dist_zero_right] using hz))
  have houter : ∀ z ∈ sphere (0 : ℂ) R, z ∈ resolventSet ℂ a := by
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hannulus z (hrr.le.trans_eq hn.symm) hn.le
  have hprod := rieszCircle_mul_nested a r R hr hrr hcircle houter
  rwa [rieszCircle_eq_of_resolvent_annulus a r R hr hrr.le hannulus] at hprod

end NonCalkinAlgebra
