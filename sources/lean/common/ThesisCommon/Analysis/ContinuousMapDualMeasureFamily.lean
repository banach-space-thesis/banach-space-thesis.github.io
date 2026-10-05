import ThesisCommon.Analysis.ContinuousMapComplexDualMeasureFamily
import ThesisCommon.Analysis.ScalarIsometryTransport
import ThesisCommon.Analysis.SequenceSpaces

/-! Actual finite-measure family representation of C(K)* for every
RCLike scalar field. Real and complex constructions are transported along
the canonical scalar-field isometries. The measures remain on K. -/
noncomputable section
universe u
open MeasureTheory
namespace ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]
variable {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']

def continuousMapDualMeasureFamilyScalarTransport
    (e : 𝕜 ≃+* 𝕜') [RingHomIsometric (RingHomClass.toRingHom e)]
    [RingHomIsometric (RingHomClass.toRingHom e.symm)] {I : Type*} (μ : I → Measure K)
    (d : (C(K, 𝕜') →L[𝕜'] 𝕜') ≃ₗᵢ[𝕜'] lp (fun i => Lp 𝕜' 1 (μ i)) 1) :
    (C(K, 𝕜) →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] lp (fun i => Lp 𝕜 1 (μ i)) 1 :=
  ((continuousMapDualScalarIsometryEquiv e K).trans d).trans
    (lpFamilySemilinearIsometryEquiv e 1 (by norm_num)
      (fun i => measureLpScalarIsometryEquiv e (μ i) 1)).symm

theorem exists_continuousMapDual_measure_family (𝕜 : Type*) [RCLike 𝕜] :
    ∃ (I : Type u) (μ : I → Measure K), (∀ i, IsFiniteMeasure (μ i)) ∧
      Nonempty ((C(K, 𝕜) →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] lp (fun i => Lp 𝕜 1 (μ i)) 1) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hr | hc
  · let e := RCLike.realRingEquiv hr
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.realLinearIsometryEquiv hr).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    obtain ⟨I, μ, hμ, d, _⟩ := exists_ordered_continuousMapDual_measure_family (K := K)
    exact ⟨I, μ, hμ, ⟨continuousMapDualMeasureFamilyScalarTransport e μ d⟩⟩
  · let e := RCLike.complexRingEquiv hc
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.complexLinearIsometryEquiv hc).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    obtain ⟨I, μ, hμ, ⟨d⟩⟩ := exists_continuousMapComplexDual_measure_family (K := K)
    exact ⟨I, μ, hμ, ⟨continuousMapDualMeasureFamilyScalarTransport e μ d⟩⟩

theorem exists_intervalContinuousDual_measure_family (𝕜 : Type*) [RCLike 𝕜] :
    ∃ (I : Type) (μ : I → Measure UnitInterval), (∀ i, IsFiniteMeasure (μ i)) ∧
      Nonempty ((IntervalContinuous 𝕜 →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] lp (fun i => Lp 𝕜 1 (μ i)) 1) :=
  exists_continuousMapDual_measure_family 𝕜

end ThesisCommon
