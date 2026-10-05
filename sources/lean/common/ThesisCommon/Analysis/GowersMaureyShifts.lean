import ThesisCommon.Analysis.GowersMaureySpace
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Actual tail shifts on the completed Gowers--Maurey space. They are
extensions of the concrete finite-sequence spreads, not abstract assumed
operators. The left shift retracts every right shift, which is isometric.
-/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem spread_left_right (n : ℕ) :
    (spread (𝕜 := 𝕜) n 0).comp (spread 0 n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i c
  simp [spread_single]

/-- The concrete tail-to-tail spread extended to the genuine completion. -/
def completedSpread (D : ConstructionData 𝕜) (m n : ℕ) : ShiftSpace D →L[𝕜] ShiftSpace D :=
  ((denseEmbedding D).toContinuousLinearMap.comp (PreSpace.spreadOperator m n)).extend
    (denseEmbedding D).toContinuousLinearMap (denseEmbedding_denseRange D)
    (denseEmbedding D).isometry.isUniformInducing

@[simp] theorem completedSpread_denseEmbedding (D : ConstructionData 𝕜)
    (m n : ℕ) (x : PreSpace D) :
    completedSpread D m n (denseEmbedding D x) =
      denseEmbedding D (PreSpace.spreadOperator m n x) :=
  ContinuousLinearMap.extend_eq _ _ _ _ x

theorem completedSpread_norm_le (D : ConstructionData 𝕜) (m n : ℕ) (x : ShiftSpace D) :
    ‖completedSpread D m n x‖ ≤ ‖x‖ := by
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_le (completedSpread D m n).continuous.norm continuous_norm
  · intro a
    rw [completedSpread_denseEmbedding, denseEmbedding_norm, denseEmbedding_norm]
    exact implicitNorm_spread_le D m n a

theorem norm_completedSpread_le (D : ConstructionData 𝕜) (m n : ℕ) :
    ‖completedSpread D m n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [one_mul] using completedSpread_norm_le D m n x

theorem completedSpread_left_right (D : ConstructionData 𝕜) (n : ℕ) :
    (completedSpread D n 0).comp (completedSpread D 0 n) = ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro x
  change completedSpread D n 0 (completedSpread D 0 n x) = x
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_eq
      ((completedSpread D n 0).continuous.comp (completedSpread D 0 n).continuous)
      continuous_id
  · intro a
    simp only [completedSpread_denseEmbedding]
    apply congrArg (denseEmbedding D)
    exact DFunLike.congr_fun (spread_left_right (𝕜 := 𝕜) n) a

theorem completedRightShift_norm (D : ConstructionData 𝕜) (n : ℕ) (x : ShiftSpace D) :
    ‖completedSpread D 0 n x‖ = ‖x‖ := by
  apply le_antisymm (completedSpread_norm_le D 0 n x)
  have hid := DFunLike.congr_fun (completedSpread_left_right D n) x
  change completedSpread D n 0 (completedSpread D 0 n x) = x at hid
  have h := completedSpread_norm_le D n 0 (completedSpread D 0 n x)
  rwa [hid] at h

/-- The canonical right shift is an actual linear isometric embedding. -/
def rightShiftIsometry (D : ConstructionData 𝕜) (n : ℕ) : ShiftSpace D →ₗᵢ[𝕜] ShiftSpace D :=
  { (completedSpread D 0 n).toLinearMap with norm_map' := completedRightShift_norm D n }

end ThesisCommon.GowersMaurey
