import SurveyStatements.P3Converse

noncomputable section
set_option autoImplicit false
namespace SurveyStatements.P3
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Main result of Problem 3: for a bounded operator into a separable Banach
space, strict cosingularity is equivalent to strict singularity of its adjoint.
The two implications use the quotient adjoint and the constructive preadjoint
extraction, respectively. -/
theorem strictlyCosingular_iff_adjoint_strictlySingular
    [CompleteSpace X] [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
    (T : X →L[𝕜] Y) :
    IsStrictlyCosingular T ↔ IsStrictlySingular (adjoint T) := by
  exact ⟨adjoint_strictlySingular_of_strictlyCosingular T,
    strictlyCosingular_of_adjoint_strictlySingular T⟩

end SurveyStatements.P3

