import JFA.TensorCancellation

/-! The scalar component of a projection is a projection. This is the first
operator step in the complemented-subspace classification in Section 4. -/

noncomputable section
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E X : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [SeparableSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem epsilonScalarOperator_projection (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X)
    (P : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 E X) (hP : P.comp P = P) :
    (epsilonScalarOperator hX hfew P).comp (epsilonScalarOperator hX hfew P) =
      epsilonScalarOperator hX hfew P := by
  rw [← epsilonScalarOperator_comp, hP]

end JFA
