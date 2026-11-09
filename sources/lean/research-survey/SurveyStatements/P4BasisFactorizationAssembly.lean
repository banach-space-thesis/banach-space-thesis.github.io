import SurveyStatements.P4ReflexiveFDDBridge
import SurveyStatements.P4BlockBasis
import SurveyStatements.P4BasisTransport

/-! Final bounded factor maps through the actual stabilized Schauder space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]

theorem weaklyCompact_basis_factorization_assembled
    {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y]
    (hBAP : HasBoundedApproximationProperty 𝕜 Y)
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T) :
    FactorsThroughReflexiveBasisSpace 𝕜 T := by
  classical
  letI : Module ℝ X := RestrictScalars.module ℝ 𝕜 X
  letI : IsScalarTower ℝ 𝕜 X := RestrictScalars.isScalarTower _ _ _
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars _ 𝕜 _
  letI : Module ℝ Y := RestrictScalars.module ℝ 𝕜 Y
  letI : IsScalarTower ℝ 𝕜 Y := RestrictScalars.isScalarTower _ _ _
  letI : NormedSpace ℝ Y := NormedSpace.restrictScalars _ 𝕜 _
  obtain ⟨D, hD, ⟨FDD⟩, A, B, hBA⟩ := weaklyCompact_reflexive_fdd_factorization hBAP T hT
  obtain ⟨V, J, Q, hQJ⟩ := exists_reflexive_basis_retraction FDD hD
  let W : ReflexiveBanachSpaceWithBasis.{u, max u v w} 𝕜 :=
    ReflexiveBanachSpaceWithBasis.ulift.{u, w, max u v w} V
  let e : W.Carrier ≃L[𝕜] V.Carrier :=
    (LinearIsometryEquiv.ulift (R := 𝕜) (E := V.Carrier)).toContinuousLinearEquiv
  refine ⟨W, e.symm.toContinuousLinearMap.comp (J.comp A),
    B.comp (Q.comp e.toContinuousLinearMap), ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  change B (Q (e (e.symm (J (A x))))) = T x
  rw [e.apply_symm_apply]
  have hQJx := congrArg (fun C : DFJPSpace D →L[𝕜] DFJPSpace D => C (A x)) hQJ
  change Q (J (A x)) = A x at hQJx
  rw [hQJx]
  exact congrArg (fun C : X →L[𝕜] Y => C x) hBA

end SurveyStatements.P4
