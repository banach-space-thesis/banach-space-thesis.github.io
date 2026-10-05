import ThesisCommon.Analysis.ScalarIsometryTransport
import ThesisCommon.Analysis.LpOperators

/-! Coordinatewise semilinear isometries on every actual Banach-exponent
sequence space, including the bounded-sequence endpoint. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv
variable {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
  {ι X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜' Y]
variable (r : 𝕜 ≃+* 𝕜')
  [RingHomIsometric (RingHomClass.toRingHom r)]
  [RingHomIsometric (RingHomClass.toRingHom r.symm)]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

def lpSemilinearIsometryValue
    (a : X ≃ₛₗᵢ[(RingHomClass.toRingHom r)] Y)
    (x : lp (fun _ : ι => X) p) : lp (fun _ : ι => Y) p :=
  ⟨fun i => a (x i), mem_lp_of_norm_le_mul x (fun i => a (x i)) zero_le_one
    (fun i => by simp only [a.norm_map, one_mul]; exact le_rfl)⟩

theorem lpSemilinearIsometryValue_norm_le
    (a : X ≃ₛₗᵢ[(RingHomClass.toRingHom r)] Y)
    (x : lp (fun _ : ι => X) p) : ‖lpSemilinearIsometryValue r p a x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using lp_norm_le_mul_of_pointwise x
    (lpSemilinearIsometryValue r p a x) zero_le_one
    (fun i => by change ‖a (x i)‖ ≤ 1 * ‖x i‖; simp only [a.norm_map, one_mul]; exact le_rfl)

def lpSemilinearIsometryEquiv
    (a : X ≃ₛₗᵢ[(RingHomClass.toRingHom r)] Y) :
    lp (fun _ : ι => X) p ≃ₛₗᵢ[(RingHomClass.toRingHom r)] lp (fun _ : ι => Y) p where
  toFun := lpSemilinearIsometryValue r p a
  invFun := lpSemilinearIsometryValue r.symm p a.symm
  left_inv x := by apply lp.ext; funext i; exact a.symm_apply_apply (x i)
  right_inv x := by apply lp.ext; funext i; exact a.apply_symm_apply (x i)
  map_add' x y := by apply lp.ext; funext i; exact map_add a (x i) (y i)
  map_smul' c x := by apply lp.ext; funext i; exact map_smulₛₗ a c (x i)
  norm_map' x := by
    letI : RingHomIsometric (RingHomClass.toRingHom r.symm.symm) := by
      simpa only [RingEquiv.symm_symm] using
        (inferInstance : RingHomIsometric (RingHomClass.toRingHom r))
    apply le_antisymm (lpSemilinearIsometryValue_norm_le r p a x)
    have h := lpSemilinearIsometryValue_norm_le r.symm p a.symm
      (lpSemilinearIsometryValue r p a x)
    have heq : lpSemilinearIsometryValue r.symm p a.symm
        (lpSemilinearIsometryValue r p a x) = x := by
      apply lp.ext; funext i; exact a.symm_apply_apply (x i)
    rwa [heq] at h

end ThesisCommon
