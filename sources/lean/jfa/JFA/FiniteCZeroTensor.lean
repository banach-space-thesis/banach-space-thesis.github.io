import JFA.CZeroDiscreteTensor
import JFA.TensorProjectionRange

/-! On a finite discrete set every function vanishes at infinity. Evaluation
and the inverse function constructor identify the actual C₀ norm with the
finite product norm. This gives the finite-power tensor identification used
in the remaining finite-rank projection cases. -/

noncomputable section
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : Type*} [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def finiteCZeroFunction (f : D → X) : C₀(D, X) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by rw [Filter.cocompact_eq_bot]; exact Filter.tendsto_bot

theorem norm_finiteCZeroFunction (f : D → X) : ‖finiteCZeroFunction f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro d
    exact norm_le_pi_norm f d
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (finiteCZeroFunction f))).mpr
    intro d
    exact (finiteCZeroFunction f).toBCF.norm_coe_le_norm d

def finiteCZeroIsometry : (D → X) →ₗᵢ[𝕜] C₀(D, X) where
  toFun := finiteCZeroFunction
  map_add' := by intros; ext d; rfl
  map_smul' := by intros; ext d; rfl
  norm_map' := norm_finiteCZeroFunction

def finiteCZeroEquiv : C₀(D, X) ≃ₗᵢ[𝕜] (D → X) :=
  (LinearIsometryEquiv.ofSurjective (finiteCZeroIsometry (𝕜 := 𝕜) (D := D) (X := X))
    (fun f => ⟨f, by ext d; rfl⟩)).symm

def finitePowerTensorEquiv [CompleteSpace X] :
    InjectiveTensor 𝕜 (D → 𝕜) X ≃L[𝕜] (D → X) :=
  (injectiveTensorEquiv (X := X) (finiteCZeroEquiv (𝕜 := 𝕜) (D := D) (X := 𝕜)).symm.toContinuousLinearEquiv).trans
    ((tensorCzeroDiscreteEquiv (𝕜 := 𝕜) (A := D) (X := X)).toContinuousLinearEquiv.trans
      (finiteCZeroEquiv (𝕜 := 𝕜) (D := D) (X := X)).toContinuousLinearEquiv)

end JFA
