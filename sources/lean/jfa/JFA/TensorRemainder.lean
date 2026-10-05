import JFA.ExtractedOperator
import JFA.TensorExtension

/-! The actual bounded tensor remainder. Its elementary equation and the common
separable subspace containing all countable dual slices are proved. This file
does not assert separability of the entire tensor-valued range. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
open scoped TensorProduct
namespace JFA
universe u
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F X A : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]

def tensorRemainder (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι) (T : A →L[𝕜] InjectiveTensor 𝕜 F X) :
    A →L[𝕜] InjectiveTensor 𝕜 F X :=
  T - tensorExtension p ι hι (extractedOperator hX hfew p ι hι T)

theorem tensorRemainder_pure (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι) (T : A →L[𝕜] InjectiveTensor 𝕜 F X) (e : E) (x : X) :
    T (ι (e ⊗ₜ[𝕜] x)) = injectivePure 𝕜 F X (extractedOperator hX hfew p ι hι T e) x +
      tensorRemainder hX hfew p ι hι T (ι (e ⊗ₜ[𝕜] x)) := by
  simp only [tensorRemainder, ContinuousLinearMap.sub_apply, tensorExtension_pure, add_sub_cancel]

theorem tensorRemainder_slice_separable (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) (p : ReasonableCrossnorm 𝕜 E X)
    (ι : E ⊗[𝕜] X →ₗ[𝕜] A) (hι : IsTensorCompletion 𝕜 E X A p ι)
    (T : A →L[𝕜] InjectiveTensor 𝕜 F X) (e : E) (φ : F →L[𝕜] 𝕜) :
    HasSeparableRange 𝕜 X X
      ((leftSlice φ).comp ((tensorRemainder hX hfew p ι hι T).comp (completionPureMap p ι hι e))) := by
  have heq : (leftSlice φ).comp
      ((tensorRemainder hX hfew p ι hι T).comp (completionPureMap p ι hι e)) =
      sliceOperator (T.comp (completionPureMap p ι hι e)) φ -
        φ (extractedOperator hX hfew p ι hι T e) • ContinuousLinearMap.id 𝕜 X := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, completionPureMap_apply, tensorRemainder,
      ContinuousLinearMap.sub_apply, tensorExtension_pure, map_sub, leftSlice_pure,
      sliceOperator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [heq]
  exact extractedOperator_slice_remainder_separable hX hfew p ι hι T e φ

theorem tensorRemainder_common_subspace [SeparableSpace E]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι) (T : A →L[𝕜] InjectiveTensor 𝕜 F X) :
    ∃ Y : Submodule 𝕜 X, IsClosed (Y : Set X) ∧ IsSeparable (Y : Set X) ∧
      ∀ a n, leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n)
        (tensorRemainder hX hfew p ι hι T a) ∈ Y := by
  let S := tensorRemainder hX hfew p ι hι T
  let R : ℕ × ℕ → X →L[𝕜] X := fun nm =>
    (leftSlice (normingSequence (𝕜 := 𝕜) (E := F) nm.1)).comp
      (S.comp (completionPureMap p ι hι (denseSeq E nm.2)))
  obtain ⟨Y, hclosed, hsep, hY⟩ := exists_common_separable_subspace R
    (fun nm => tensorRemainder_slice_separable hX hfew p ι hι T _ _)
  have hpure : ∀ e x n, leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n)
      (S (ι (e ⊗ₜ[𝕜] x))) ∈ Y := by
    intro e x n
    let f := (leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n)).comp
      (S.comp (completionLeftPureMap p ι hι x))
    change f e ∈ Y
    refine (denseRange_denseSeq E).induction_on e (hclosed.preimage f.continuous) ?_
    intro m
    exact hY (n, m) x
  refine ⟨Y, hclosed, hsep, ?_⟩
  intro a n
  let f := (leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n)).comp S
  change f a ∈ Y
  refine hι.2.1.induction_on a (hclosed.preimage f.continuous) ?_
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using Y.zero_mem
  | tmul e x => exact hpure e x n
  | add z w hz hw => simpa only [map_add] using Y.add_mem hz hw

theorem tensorRemainder_common_subspace_all_dual [SeparableSpace E]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι) (T : A →L[𝕜] InjectiveTensor 𝕜 F X) :
    ∃ Y : Submodule 𝕜 X, IsClosed (Y : Set X) ∧ IsSeparable (Y : Set X) ∧
      ∀ a (φ : F →L[𝕜] 𝕜), leftSlice φ (tensorRemainder hX hfew p ι hι T a) ∈ Y := by
  obtain ⟨Y, hclosed, hsep, hY⟩ := tensorRemainder_common_subspace hX hfew p ι hι T
  refine ⟨Y, hclosed, hsep, ?_⟩
  intro a φ
  apply mem_of_all_annihilators_zero Y hclosed
  intro ψ hψ
  have hz : rightSlice ψ (tensorRemainder hX hfew p ι hι T a) = 0 := by
    apply eq_zero_of_normingSequence_zero (𝕜 := 𝕜)
    intro n
    rw [rightSlice_pairing]
    exact hψ _ (hY a n)
  rw [← rightSlice_pairing, hz, map_zero]

end JFA
