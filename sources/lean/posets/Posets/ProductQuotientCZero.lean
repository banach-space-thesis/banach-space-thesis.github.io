import Posets.ProductQuotientTensor
import Posets.StrongSplitTransport
import PosetsCommon.CZeroSum
import JFA.CZeroDiscreteTensor

/-! Discrete injective tensor products in the c₀-sum coordinates used in §7. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open Filter Topology ThesisCommon TopologicalSpace
open scoped ZeroAtInfty ENNReal
namespace Posets

variable {𝕜 D X : Type} [RCLike 𝕜]
  [TopologicalSpace D] [DiscreteTopology D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def productCZeroToSum (f : C₀(D, X)) : DependentCZeroSum 𝕜 (fun _ : D => X) :=
  ⟨⟨fun d => f d, memℓp_infty ⟨‖f‖, by rintro _ ⟨d, rfl⟩; exact f.toBCF.norm_coe_le_norm d⟩⟩,
    by
      change Tendsto (fun d => ‖f d‖) cofinite (𝓝 0)
      simpa only [Filter.cocompact_eq_cofinite, norm_zero] using (zero_at_infty f).norm⟩

def productCZeroFromSum (x : DependentCZeroSum 𝕜 (fun _ : D => X)) : C₀(D, X) where
  toFun d := x.val d
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite, tendsto_zero_iff_norm_tendsto_zero]
    exact x.property

theorem productCZeroToSum_norm (f : C₀(D, X)) : ‖productCZeroToSum (𝕜 := 𝕜) f‖ = ‖f‖ := by
  apply le_antisymm
  · exact lp.norm_le_of_forall_le (norm_nonneg f) f.toBCF.norm_coe_le_norm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg (productCZeroToSum (𝕜 := 𝕜) f))).mpr
    intro d
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (productCZeroToSum (𝕜 := 𝕜) f).val d

/-- A vector-valued function vanishing at infinity on a discrete set is the
corresponding element of the concrete dependent c₀ sum. -/
def productCZeroSumEquiv : C₀(D, X) ≃ₗᵢ[𝕜] DependentCZeroSum 𝕜 (fun _ : D => X) where
  toFun := productCZeroToSum
  invFun := productCZeroFromSum
  left_inv f := by ext d; rfl
  right_inv x := by apply Subtype.ext; apply lp.ext; rfl
  map_add' f g := by apply Subtype.ext; apply lp.ext; rfl
  map_smul' a f := by apply Subtype.ext; apply lp.ext; rfl
  norm_map' := productCZeroToSum_norm

variable [CompleteSpace X]

def productTensorCZeroSumEquiv : JFA.InjectiveTensor 𝕜 C₀(D, 𝕜) X ≃ₗᵢ[𝕜]
    DependentCZeroSum 𝕜 (fun _ : D => X) :=
  JFA.tensorCzeroDiscreteEquiv.trans productCZeroSumEquiv

variable [Countable D]
  (hX : ¬ SeparableSpace X) (hfew : JFA.HasFewOperators 𝕜 X)

include hX hfew

/-- Full operator algebra quotients on finite or countable repeated sums. -/
theorem exists_productCZero_strongSplit :
    ∃ θ : BoundedHom 𝕜
      (DependentCZeroSum 𝕜 (fun _ : D => X) →L[𝕜] DependentCZeroSum 𝕜 (fun _ : D => X))
      (C₀(D, 𝕜) →L[𝕜] C₀(D, 𝕜)),
    ∃ ρ : BoundedHom 𝕜 (C₀(D, 𝕜) →L[𝕜] C₀(D, 𝕜))
      (DependentCZeroSum 𝕜 (fun _ : D => X) →L[𝕜] DependentCZeroSum 𝕜 (fun _ : D => X)),
      StrongSplit 𝕜 (DependentCZeroSum 𝕜 (fun _ : D => X)) (C₀(D, 𝕜) →L[𝕜] C₀(D, 𝕜)) θ ρ ∧
        Isometry ρ ∧ ‖θ.toContinuousLinearMap‖ ≤ 1 := by
  letI := JFA.czero_countable_discrete_separable (𝕜 := 𝕜) (A := D)
  let e := productTensorCZeroSumEquiv (𝕜 := 𝕜) (D := D) (X := X)
  let c := LinearIsometryEquiv.refl 𝕜 (C₀(D, 𝕜) →L[𝕜] C₀(D, 𝕜))
  have hc : ∀ a b, c (a * b) = c a * c b := fun _ _ => rfl
  refine ⟨transportQuotient e c hc (productTensorQuotient hX hfew),
    transportSection e c hc productTensorSection, ?_, ?_, ?_⟩
  · exact strongSplit_transport e c hc _ _ (productTensor_strongSplit hX hfew)
  · exact isometry_transportSection e c hc _ (productTensorSection_isometry hX hfew)
  · rw [norm_transportQuotient]
    exact productTensorQuotient_norm_le hX hfew

end Posets
