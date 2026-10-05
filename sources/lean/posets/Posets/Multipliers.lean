import Posets.Models

noncomputable section
open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 P : Type*} [RCLike 𝕜]

/-- Pointwise multiplication by a bounded scalar function preserves c₀. -/
def multiplyCZero (a : Discrete P →ᵇ 𝕜) (f : CZeroOn 𝕜 P) : CZeroOn 𝕜 P where
  toFun x := a x * f x
  continuous_toFun := a.continuous.mul f.continuous
  zero_at_infty' := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun x => norm_nonneg _)
      (fun x => (norm_mul (a x) (f x)).le.trans
        (mul_le_mul_of_nonneg_right (a.norm_coe_le_norm x) (norm_nonneg (f x))))
    simpa using (tendsto_const_nhds.mul (zero_at_infty f).norm :
      Tendsto (fun x => ‖a‖ * ‖f x‖) (cocompact (Discrete P)) (𝓝 (‖a‖ * ‖(0 : 𝕜)‖)))

theorem norm_multiplyCZero_le (a : Discrete P →ᵇ 𝕜) (f : CZeroOn 𝕜 P) :
    ‖multiplyCZero a f‖ ≤ ‖a‖ * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg a) (norm_nonneg f))).mpr
  intro x
  change ‖a x * f x‖ ≤ ‖a‖ * ‖f‖
  rw [norm_mul]
  exact mul_le_mul (a.norm_coe_le_norm x) (f.toBCF.norm_coe_le_norm x)
    (norm_nonneg _) (norm_nonneg _)

/-- The genuine diagonal multiplication operator M_a used in Lemma 8.2. -/
def multiplicationOperator (a : Discrete P →ᵇ 𝕜) : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P :=
  ({toFun := multiplyCZero a
    map_add' := by intros; ext; exact mul_add _ _ _
    map_smul' := by intros; ext; exact mul_left_comm _ _ _} :
      CZeroOn 𝕜 P →ₗ[𝕜] CZeroOn 𝕜 P).mkContinuous ‖a‖ (norm_multiplyCZero_le a)

@[simp] theorem multiplicationOperator_apply (a : Discrete P →ᵇ 𝕜)
    (f : CZeroOn 𝕜 P) (x : Discrete P) : multiplicationOperator a f x = a x * f x := rfl

theorem norm_multiplicationOperator_le (a : Discrete P →ᵇ 𝕜) :
    ‖multiplicationOperator a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (norm_multiplyCZero_le a)

end Posets
