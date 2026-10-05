import ThesisCommon.Analysis.StrictlySingularOperatorCalculus

/-! Nonzero scalar perturbations of a genuinely strictly singular operator
have finite-dimensional kernels, directly from the subspace definition. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem IsStrictlySingularOperator.finiteDimensional_kernel_sub_smul_id
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T) (a : 𝕜) (ha : a ≠ 0) :
    FiniteDimensional 𝕜 (LinearMap.ker (T-a • ContinuousLinearMap.id 𝕜 X).toLinearMap) := by
  apply hT
  refine ⟨‖a‖, norm_pos_iff.mpr ha, ?_⟩
  intro x
  have hx : T x.val = a • x.val := by
    apply sub_eq_zero.mp
    exact x.property
  change ‖a‖*‖x.val‖ ≤ ‖T x.val‖
  rw [hx,norm_smul]

theorem IsStrictlySingularOperator.finiteDimensional_kernel_id_sub
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T) :
    FiniteDimensional 𝕜 (LinearMap.ker (ContinuousLinearMap.id 𝕜 X-T).toLinearMap) := by
  apply hT
  refine ⟨1, by norm_num, ?_⟩
  intro x
  have hx : x.val = T x.val := sub_eq_zero.mp x.property
  change 1*‖x.val‖ ≤ ‖T x.val‖
  rw [one_mul, ← hx]

theorem IsStrictlySingularOperator.finiteDimensional_kernel_id_sub_smul
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T) (t : 𝕜) :
    FiniteDimensional 𝕜 (LinearMap.ker (ContinuousLinearMap.id 𝕜 X-t • T).toLinearMap) :=
  (hT.smul t).finiteDimensional_kernel_id_sub

end ThesisCommon
