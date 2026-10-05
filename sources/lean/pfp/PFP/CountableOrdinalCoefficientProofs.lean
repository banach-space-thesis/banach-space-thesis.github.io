import Posets.CountableOrdinalUPFPCanonical
import ThesisCommon.Analysis.CountableOrdinalSmallModel
import ThesisCommon.Analysis.ScalarFactorizationTransport
import Mathlib.Analysis.Complex.Basic

/-! Actual UPFP of every infinite countable ordinal coefficient space.
The quantified constants come from the checked ordinal tower construction.
Order homeomorphisms and scalar semilinear isometries remove universe
restrictions from the original Posets construction. -/
noncomputable section
namespace PFP
open ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv
universe u

theorem ordinalContinuous_hasUPFP_of_countable_infinite_smallScalar
    (𝕜 : Type) [RCLike 𝕜] {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) (hαinf : Ordinal.omega0 ≤ α) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) := by
  obtain ⟨β, hcβ, hβ, ⟨e⟩⟩ := exists_countableOrdinal_small_infinite_model hα hαinf
  exact (Posets.countableOrdinal_hasUPFP (𝕜 := 𝕜) β hcβ hβ).of_equiv
    (continuousMapHomeomorphEquiv e.symm)

theorem ordinalContinuous_hasUPFP_of_countable_infinite
    (𝕜 : Type*) [RCLike 𝕜] {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) (hαinf : Ordinal.omega0 ≤ α) :
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
    exact (ordinalContinuous_hasUPFP_of_countable_infinite_smallScalar ℝ hα hαinf).of_semilinearIsometry
      e.symm (continuousMapScalarIsometryEquiv e (OrdinalInterval α)).symm
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
    exact (ordinalContinuous_hasUPFP_of_countable_infinite_smallScalar ℂ hα hαinf).of_semilinearIsometry
      e.symm (continuousMapScalarIsometryEquiv e (OrdinalInterval α)).symm

end PFP
