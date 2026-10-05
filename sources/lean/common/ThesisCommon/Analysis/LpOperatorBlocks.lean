import ThesisCommon.Analysis.LpOperatorDiagonals
import ThesisCommon.Analysis.LpOperatorFiniteCorners
import ThesisCommon.Analysis.LpArbitraryProducts
import ThesisCommon.Analysis.OperatorTransportEquiv

/-! Disjoint infinite blocks identify the bounded product of lp operators
with a complemented block-diagonal subspace of the actual operator space. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (p : BanachExponent) (hp : 0 < p.val.toReal)
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def lpBlockOperatorTransport :
    (lp (fun _ : ℕ => lp (fun _ : ℕ => 𝕜) p.val) p.val →L[𝕜]
      lp (fun _ : ℕ => lp (fun _ : ℕ => 𝕜) p.val) p.val) ≃ₗᵢ[𝕜] ScalarLpOperator 𝕜 p :=
  operatorTransportLinearIsometryEquiv
    (lpProductFlattenIsometry (𝕜 := 𝕜) (X := 𝕜) p.val hp Nat.pairEquiv)
    (lpProductFlattenIsometry (𝕜 := 𝕜) (X := 𝕜) p.val hp Nat.pairEquiv)

def lpOperatorBlockInsert :
    lp (fun _ : ℕ => ScalarLpOperator 𝕜 p) ∞ →L[𝕜] ScalarLpOperator 𝕜 p :=
  (lpBlockOperatorTransport (𝕜 := 𝕜) p hp).toLinearIsometry.toContinuousLinearMap.comp
    (lpOperatorDiagonalMap p.val)

def lpOperatorBlockRead :
    ScalarLpOperator 𝕜 p →L[𝕜] lp (fun _ : ℕ => ScalarLpOperator 𝕜 p) ∞ :=
  (lpOperatorDiagonalRead p.val).comp
    (lpBlockOperatorTransport (𝕜 := 𝕜) p hp).symm.toLinearIsometry.toContinuousLinearMap

theorem norm_lpOperatorBlockInsert_le : ‖lpOperatorBlockInsert (𝕜 := 𝕜) p hp‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul
    (lpBlockOperatorTransport (𝕜 := 𝕜) p hp).toLinearIsometry.norm_toContinuousLinearMap_le
    (norm_lpOperatorDiagonalMap_le (𝕜 := 𝕜) (X := lp (fun _ : ℕ => 𝕜) p.val) p.val)
    (norm_nonneg (lpOperatorDiagonalMap (𝕜 := 𝕜) (X := lp (fun _ : ℕ => 𝕜) p.val) p.val)) zero_le_one

theorem norm_lpOperatorBlockRead_le : ‖lpOperatorBlockRead (𝕜 := 𝕜) p hp‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul
    (norm_lpOperatorDiagonalRead_le (𝕜 := 𝕜) (X := lp (fun _ : ℕ => 𝕜) p.val) p.val)
    (lpBlockOperatorTransport (𝕜 := 𝕜) p hp).symm.toLinearIsometry.norm_toContinuousLinearMap_le
    (norm_nonneg (lpBlockOperatorTransport (𝕜 := 𝕜) p hp).symm.toLinearIsometry.toContinuousLinearMap) zero_le_one

theorem lpOperatorBlockRead_comp_insert :
    (lpOperatorBlockRead (𝕜 := 𝕜) p hp).comp (lpOperatorBlockInsert p hp) =
      ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => ScalarLpOperator 𝕜 p) ∞) := by
  apply ContinuousLinearMap.ext
  intro a
  change lpOperatorDiagonalRead p.val
    ((lpBlockOperatorTransport (𝕜 := 𝕜) p hp).symm
      ((lpBlockOperatorTransport (𝕜 := 𝕜) p hp) (lpOperatorDiagonalMap p.val a))) = a
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact DFunLike.congr_fun (lpOperatorDiagonalRead_comp_map
    (𝕜 := 𝕜) (X := lp (fun _ : ℕ => 𝕜) p.val) p.val) a

end ThesisCommon
