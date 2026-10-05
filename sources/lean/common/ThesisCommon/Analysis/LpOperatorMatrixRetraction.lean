import ThesisCommon.Analysis.LpOperatorUltralimit
import ThesisCommon.Analysis.LpInitialCornerLimits
import ThesisCommon.Analysis.MatrixOperatorSequences
import ThesisCommon.Analysis.BoundedProductFamilyMap

/-! Contractive complementary embedding of B(lp) in the actual bounded
product of growing finite matrix spaces. The retraction is an ultralimit
of finite-corner insertions, not an assumed weak-limit operator. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

def lpOperatorInitialCorners (p : BanachExponent) :
    ScalarLpOperator 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p :=
  boundedProductFamilyMap (fun n => lpOperatorToFiniteMatrix (𝕜 := 𝕜) p n)
    1 zero_le_one (norm_lpOperatorToFiniteMatrix_le p)

@[simp] theorem lpOperatorInitialCorners_apply (p : BanachExponent)
    (T : ScalarLpOperator 𝕜 p) (n : ℕ) :
    lpOperatorInitialCorners p T n = lpOperatorToFiniteMatrix p n T := rfl

theorem norm_lpOperatorInitialCorners_le (p : BanachExponent) :
    ‖lpOperatorInitialCorners (𝕜 := 𝕜) p‖ ≤ 1 :=
  norm_boundedProductFamilyMap_le _ _ _ _

def matrixProductOperatorLimit (p : BanachExponent) (hp : 0 < p.val.toReal) :
    FiniteMatrixSum 𝕜 p →L[𝕜] ScalarLpOperator 𝕜 p :=
  (lpOperatorUltralimit p hp (hyperfilter ℕ)).comp (matrixOperatorSequenceInsert p)

theorem norm_matrixProductOperatorLimit_le (p : BanachExponent) (hp : 0 < p.val.toReal) :
    ‖matrixProductOperatorLimit (𝕜 := 𝕜) p hp‖ ≤ 1 := by
  apply ((lpOperatorUltralimit (𝕜 := 𝕜) (E := lp (fun _ : ℕ => 𝕜) p.val) (κ := ℕ)
      p hp (hyperfilter ℕ)).opNorm_comp_le
    (matrixOperatorSequenceInsert (𝕜 := 𝕜) p)).trans
  exact (mul_le_mul (norm_lpOperatorUltralimit_le (𝕜 := 𝕜)
      (E := lp (fun _ : ℕ => 𝕜) p.val) (κ := ℕ) p hp (hyperfilter ℕ))
    (norm_matrixOperatorSequenceInsert_le (𝕜 := 𝕜) p)
    (ContinuousLinearMap.opNorm_nonneg (matrixOperatorSequenceInsert (𝕜 := 𝕜) p)) zero_le_one).trans_eq (mul_one 1)

theorem matrixProductOperatorLimit_comp_initialCorners (p : BanachExponent)
    (hp : 0 < p.val.toReal) :
    (matrixProductOperatorLimit (𝕜 := 𝕜) p hp).comp (lpOperatorInitialCorners p) =
      ContinuousLinearMap.id 𝕜 (ScalarLpOperator 𝕜 p) := by
  have hfin : p.val ≠ ∞ := by intro h; simp [h] at hp
  apply ContinuousLinearMap.ext
  intro T
  change lpOperatorUltralimit p hp (hyperfilter ℕ)
    (matrixOperatorSequenceInsert p (lpOperatorInitialCorners p T)) = T
  apply lpOperatorUltralimit_eq_of_tendsto
  intro x k
  simpa only [matrixOperatorSequenceInsert_apply, lpOperatorInitialCorners_apply] using
    (finite_matrix_corners_coordinate_tendsto p hfin T x k).mono_left Nat.hyperfilter_le_atTop

theorem exists_lpOperator_matrixProduct_retraction (p : BanachExponent)
    (hp : 0 < p.val.toReal) :
    ∃ (J : ScalarLpOperator 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p)
      (Q : FiniteMatrixSum 𝕜 p →L[𝕜] ScalarLpOperator 𝕜 p),
      ‖J‖ ≤ 1 ∧ ‖Q‖ ≤ 1 ∧ Q.comp J = ContinuousLinearMap.id 𝕜 (ScalarLpOperator 𝕜 p) :=
  ⟨lpOperatorInitialCorners p, matrixProductOperatorLimit p hp,
    norm_lpOperatorInitialCorners_le p, norm_matrixProductOperatorLimit_le p hp,
    matrixProductOperatorLimit_comp_initialCorners p hp⟩

end ThesisCommon

