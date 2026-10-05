import PFP.CountableOrdinalCoefficientProofs

/-! Scalar-universe transport for actual ordinal continuous-function spaces.
Real and complex proofs suffice for every RCLike field, via the checked
semilinear isometries on continuous functions and on their operators. -/
noncomputable section
namespace PFP
open ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv
universe u

theorem ordinalContinuous_hasUPFP_of_real_complex
    (𝕜 : Type*) [RCLike 𝕜] (α : Ordinal.{u})
    (hR : HasUPFP ℝ (OrdinalContinuous ℝ α))
    (hC : HasUPFP ℂ (OrdinalContinuous ℂ α)) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hr | hc
  · let e := RCLike.realRingEquiv hr
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.realLinearIsometryEquiv hr).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
      simpa only [RingEquiv.symm_symm] using
        (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))
    exact hR.of_semilinearIsometry e.symm
      (continuousMapScalarIsometryEquiv e (OrdinalInterval α)).symm
  · let e := RCLike.complexRingEquiv hc
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.complexLinearIsometryEquiv hc).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
      simpa only [RingEquiv.symm_symm] using
        (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))
    exact hC.of_semilinearIsometry e.symm
      (continuousMapScalarIsometryEquiv e (OrdinalInterval α)).symm

end PFP
