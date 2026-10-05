import Posets.OrdinalPrincipalTransfiniteBlockModel
import Posets.OrdinalRegularOmegaAssemblyModels
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! Actual transfinite block factors transported to the fixed ordinal
target.  The original operator is unchanged in this target-only step. -/

noncomputable section
open Set
universe u
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace

local instance transfiniteBridgeSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance transfiniteBridgeSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem ordinalTransfiniteBlocks_factorizationWith320
    {Λ Γ : Ordinal.{u}} (P : OrdinalPrincipalTransfiniteSequence Λ Γ)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F)
    (J : JLMS.CZeroSum 𝕜 (fun i : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint i)) →L[𝕜] E)
    (R : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun i : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint i)))
    (hf : R.comp (A.comp J) = ContinuousLinearMap.id 𝕜 _)
    (hJ : ‖J‖ ≤ 1) (hR : ‖R‖ ≤ 5) :
    FactorsIdentityWith A (JLMS.CZero 𝕜 (Iio Γ)) 320 := by
  have hb : FactorsIdentityWith A
      (JLMS.CZeroSum 𝕜 (fun i : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint i))) 5 := by
    refine ⟨R, J, ?_, ?_⟩
    · simpa only [ContinuousLinearMap.comp_assoc] using hf
    · exact (mul_le_mul hR hJ (norm_nonneg J) (by norm_num)).trans_eq (mul_one _)
  have ht := hb.target_equiv (P.halfOpenBlockSumEquiv (𝕜 := 𝕜)).symm
  apply ht.mono
  have hn : ‖(P.halfOpenBlockSumEquiv (𝕜 := 𝕜)).symm.toContinuousLinearMap‖ *
      ‖(P.halfOpenBlockSumEquiv (𝕜 := 𝕜)).toContinuousLinearMap‖ ≤ 8 * 8 :=
    mul_le_mul P.halfOpenBlockSumEquiv_symm_norm_le P.halfOpenBlockSumEquiv_norm_le
      (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 5)).trans_eq (by norm_num)

theorem ordinalTransfiniteBlocks_full_factorizationWith1280
    {Λ Γ : Ordinal.{u}} (P : OrdinalPrincipalTransfiniteSequence Λ Γ)
    (hΓ : Ordinal.omega0 ≤ Γ)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F)
    (J : JLMS.CZeroSum 𝕜 (fun i : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint i)) →L[𝕜] E)
    (R : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun i : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint i)))
    (hf : R.comp (A.comp J) = ContinuousLinearMap.id 𝕜 _)
    (hJ : ‖J‖ ≤ 1) (hR : ‖R‖ ≤ 5) :
    FactorsIdentityWith A (JLMS.OrdinalC 𝕜 Γ) 1280 := by
  have hb := ordinalTransfiniteBlocks_factorizationWith320 P A J R hf hJ hR
  have ht := hb.target_equiv (ordinalHalfOpenContinuousEquiv (𝕜 := 𝕜) Γ hΓ)
  apply ht.mono
  have hn : ‖(ordinalHalfOpenContinuousEquiv (𝕜 := 𝕜) Γ hΓ).toContinuousLinearMap‖ *
      ‖(ordinalHalfOpenContinuousEquiv (𝕜 := 𝕜) Γ hΓ).symm.toContinuousLinearMap‖ ≤ 2 * 2 :=
    mul_le_mul (ordinalHalfOpenContinuousEquiv_norm_le Γ hΓ)
      (ordinalHalfOpenContinuousEquiv_symm_norm_le Γ hΓ)
      (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 320)).trans_eq (by norm_num)

end Posets

