import JFA.MainStatements
import JFA.RemainderSeparability
import JFA.DecompositionUniqueness

/-! Theorem 1.1 with a complete proof from the paper's Banach, separability
and few-operator hypotheses. The tensor and separability conclusions are derived. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
open scoped TensorProduct
namespace JFA
universe u
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F X : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem tensorRemainder_separable [SeparableSpace E]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (A : Type u) [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    (ι : E ⊗[𝕜] X →ₗ[𝕜] A) (hι : IsTensorCompletion 𝕜 E X A p ι)
    (T : A →L[𝕜] InjectiveTensor 𝕜 F X) :
    HasSeparableRange 𝕜 A (InjectiveTensor 𝕜 F X) (tensorRemainder hX hfew p ι hι T) := by
  obtain ⟨Y, _, hsep, hY⟩ := tensorRemainder_common_subspace_all_dual hX hfew p ι hι T
  exact hasSeparableRange_of_slices_in_separable_subspace _ Y hsep hY

omit [SeparableSpace F] in
theorem theorem_1_1 [CompleteSpace E] : Theorem_1_1 𝕜 E F X := by
  intro hE hF hX hfew α A instA instSpaceA instCompleteA ι hι T
  letI : SeparableSpace E := hE
  letI : SeparableSpace F := hF
  let p := α.normFor E X
  let U := extractedOperator hX hfew p ι hι T
  let S := tensorRemainder hX hfew p ι hι T
  have hS : HasSeparableRange 𝕜 A (InjectiveTensor 𝕜 F X) S :=
    tensorRemainder_separable hX hfew p A ι hι T
  have hEq : ∀ e x, T (ι (e ⊗ₜ[𝕜] x)) = injectivePure 𝕜 F X (U e) x + S (ι (e ⊗ₜ[𝕜] x)) :=
    tensorRemainder_pure hX hfew p ι hι T
  refine ⟨(U, S), ⟨hS, hEq⟩, ?_⟩
  rintro ⟨V, R⟩ ⟨hR, hV⟩
  obtain ⟨hUV, hSR⟩ := tensor_decomposition_unique hX p ι hι T hS hR hEq hV
  exact Prod.ext hUV.symm hSR.symm

end JFA
