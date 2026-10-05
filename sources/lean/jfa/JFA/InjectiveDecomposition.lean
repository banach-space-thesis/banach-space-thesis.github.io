import JFA.InjectiveFunctor
import JFA.RemainderSeparability

/-! The scalar-plus-separable decomposition on the concrete epsilon products.
This avoids assuming an algebraic crossnorm injectivity lemma merely to apply
the decomposition to the concrete model used in Corollary 1.2. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
open scoped TensorProduct
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F X : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

def epsilonScalarOperator (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) : E →L[𝕜] F :=
  LinearMap.mkContinuous {
    toFun := fun e => scalarExtraction hX hfew (T.comp (injectivePureMap e))
    map_add' := by intro e f; rw [injectivePureMap_add, ContinuousLinearMap.comp_add, scalarExtraction_add]
    map_smul' := by
      intro a e
      rw [injectivePureMap_smul, ContinuousLinearMap.comp_smul, scalarExtraction_smul]
      rfl }
    ‖T‖ (fun e => (norm_scalarExtraction_le hX hfew _).trans
      ((T.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (norm_injectivePureMap_le e) (norm_nonneg T))))

theorem epsilonScalarOperator_spec (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) (e : E) (φ : F →L[𝕜] 𝕜) :
    φ (epsilonScalarOperator hX hfew T e) = scalarCoefficient hX hfew (sliceOperator (T.comp (injectivePureMap e)) φ) :=
  scalarExtraction_spec hX hfew _ φ

def epsilonRemainder (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) :
    InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X :=
  T - injectiveTensorMap (epsilonScalarOperator hX hfew T)

theorem epsilonRemainder_pure (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) (e : E) (x : X) :
    T (injectivePure 𝕜 E X e x) = injectivePure 𝕜 F X (epsilonScalarOperator hX hfew T e) x +
      epsilonRemainder hX hfew T (injectivePure 𝕜 E X e x) := by
  simp only [epsilonRemainder, ContinuousLinearMap.sub_apply, injectiveTensorMap_pure, add_sub_cancel]

theorem epsilonRemainder_slice_separable (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) (e : E) (φ : F →L[𝕜] 𝕜) :
    HasSeparableRange 𝕜 X X
      ((leftSlice φ).comp ((epsilonRemainder hX hfew T).comp (injectivePureMap e))) := by
  have heq : (leftSlice φ).comp ((epsilonRemainder hX hfew T).comp (injectivePureMap e)) =
      scalarRemainder hX hfew (sliceOperator (T.comp (injectivePureMap e)) φ) := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun V : X →L[𝕜] X => V x)
      (scalar_decomposition hX hfew (sliceOperator (T.comp (injectivePureMap e)) φ))
    change leftSlice φ (T (injectivePure 𝕜 E X e x) -
      injectivePure 𝕜 F X (epsilonScalarOperator hX hfew T e) x) = _
    rw [map_sub, leftSlice_pure, epsilonScalarOperator_spec]
    exact sub_eq_iff_eq_add.mpr (by simpa only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, sliceOperator,
      ContinuousLinearMap.comp_apply, injectivePureMap_apply, add_comm] using h)
  rw [heq]
  exact scalarRemainder_separable hX hfew _

theorem epsilonRemainder_separable [SeparableSpace E]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) :
    HasSeparableRange 𝕜 (InjectiveTensor 𝕜 E X) (InjectiveTensor 𝕜 F X) (epsilonRemainder hX hfew T) := by
  let S := epsilonRemainder hX hfew T
  let R : ℕ × ℕ → X →L[𝕜] X := fun nm =>
    (leftSlice (normingSequence (𝕜 := 𝕜) (E := F) nm.1)).comp
      (S.comp (injectivePureMap (denseSeq E nm.2)))
  obtain ⟨Y, hclosed, hsep, hY⟩ := exists_common_separable_subspace R
    (fun nm => epsilonRemainder_slice_separable hX hfew T _ _)
  have hpure : ∀ e x n, leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n)
      (S (injectivePure 𝕜 E X e x)) ∈ Y := by
    intro e x n
    let f := (leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n)).comp (S.comp (injectiveLeftPureMap x))
    change f e ∈ Y
    refine (denseRange_denseSeq E).induction_on e (hclosed.preimage f.continuous) ?_
    intro m
    exact hY (n, m) x
  have hall : ∀ a n, leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n) (S a) ∈ Y := by
    intro a n
    let f := (leftSlice (normingSequence (𝕜 := 𝕜) (E := F) n)).comp S
    change f a ∈ Y
    refine injectiveInclusion_dense.induction_on a (hclosed.preimage f.continuous) ?_
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using Y.zero_mem
    | tmul e x => exact hpure e x n
    | add z w hz hw => simpa only [map_add] using Y.add_mem hz hw
  apply hasSeparableRange_of_slices_in_separable_subspace S Y hsep
  intro a φ
  apply mem_of_all_annihilators_zero Y hclosed
  intro ψ hψ
  have hz : rightSlice ψ (S a) = 0 := by
    apply eq_zero_of_normingSequence_zero (𝕜 := 𝕜)
    intro n
    rw [rightSlice_pairing]
    exact hψ _ (hall a n)
  rw [← rightSlice_pairing, hz, map_zero]

end JFA
