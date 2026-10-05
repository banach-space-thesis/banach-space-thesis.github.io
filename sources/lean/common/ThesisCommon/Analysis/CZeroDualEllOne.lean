import ThesisCommon.Analysis.CZeroFunctionalRows
import ThesisCommon.Analysis.LpOneFamilyOperators
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! The actual coefficients of a scalar c0 functional form an isometric
linear map into scalar ell-one. Only coordinate evaluations are used. -/
noncomputable section
set_option maxSynthPendingDepth 3
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

local instance cZeroDual_normSMulClass : NormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] 𝕜) :=
  NormedSpace.toNormSMulClass (𝕜 := 𝕜) (E := CZeroSum 𝕜 →L[𝕜] 𝕜)

def cZeroDualToEllOne : (CZeroSum 𝕜 →L[𝕜] 𝕜) →L[𝕜] lp (fun _ : ℕ => 𝕜) 1 := by
  let L : (CZeroSum 𝕜 →L[𝕜] 𝕜) →ₗ[𝕜] lp (fun _ : ℕ => 𝕜) 1 :=
    { toFun := fun φ => ⟨fun n => φ (cZeroSingle n 1),
        memℓp_gen' (by simpa only [ENNReal.toReal_one, Real.rpow_one] using cZero_functional_row_sum_le φ)⟩
      map_add' := by intro φ ψ; apply lp.ext; funext n; rfl
      map_smul' := by intro c φ; apply lp.ext; funext n; rfl }
  refine LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := CZeroSum 𝕜 →L[𝕜] 𝕜) (F := lp (fun _ : ℕ => 𝕜) 1) L 1 ?_
  intro φ
  rw [one_mul]
  exact lp.norm_le_of_forall_sum_le
      (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (norm_nonneg φ)
      (f := L φ) (by simpa only [ENNReal.toReal_one, Real.rpow_one] using cZero_functional_row_sum_le φ)

@[simp] theorem cZeroDualToEllOne_apply (φ : CZeroSum 𝕜 →L[𝕜] 𝕜) (n : ℕ) :
    cZeroDualToEllOne (𝕜 := 𝕜) φ n = φ (cZeroSingle n 1) := rfl

theorem norm_cZeroDualToEllOne_apply (φ : CZeroSum 𝕜 →L[𝕜] 𝕜) :
    ‖cZeroDualToEllOne (𝕜 := 𝕜) φ‖ = ‖φ‖ := by
  rw [cZero_functional_norm_eq_tsum]
  exact (lpOneFamily_hasSum_norm (cZeroDualToEllOne (𝕜 := 𝕜) φ)).tsum_eq.symm

theorem norm_cZeroDualToEllOne_le : ‖cZeroDualToEllOne (𝕜 := 𝕜)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro φ
  rw [norm_cZeroDualToEllOne_apply, one_mul]

end ThesisCommon
