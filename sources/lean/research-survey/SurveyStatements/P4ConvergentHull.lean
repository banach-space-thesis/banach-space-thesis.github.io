import SurveyStatements.P4Lp1WeakCompact
import SurveyStatements.P4Lp1Fold
import SurveyStatements.P4OperatorGaugeInvariance
import SurveyStatements.P4ConvergentDualRepresentation

/-! An actual weakly compact, absolutely convex invariant generating set
for the convergent-sequence bridge. It is the closed unit-ball image of an
absolutely summable mixing operator. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

open Set Filter Topology Metric
open scoped OnePoint ENNReal

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

lemma norm_convergentFreeze_comp_le (R : X →L[𝕜] C(OnePoint ℕ, Y)) (n : ℕ) :
    ‖(convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp R‖ ≤ ‖R‖ :=
  ((convergentFreeze (𝕜 := 𝕜) (Y := Y) n).opNorm_comp_le R).trans
    ((mul_le_mul_of_nonneg_right (norm_convergentFreeze_le_one (𝕜 := 𝕜) (Y := Y) n) R.opNorm_nonneg).trans_eq
      (one_mul _))

def convergentFreezeSum (R : X →L[𝕜] C(OnePoint ℕ, Y)) :
    lp (fun _ : ℕ => X) 1 →L[𝕜] C(OnePoint ℕ, Y) :=
  lp1Sum (fun n => (convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp R) R.opNorm_nonneg
    (norm_convergentFreeze_comp_le R)

@[simp] lemma convergentFreezeSum_single (R : X →L[𝕜] C(OnePoint ℕ, Y))
    (n : ℕ) (x : X) : convergentFreezeSum R (lp.single 1 n x) = convergentFreeze (𝕜 := 𝕜) (Y := Y) n (R x) :=
  lp1Sum_single _ _ _ _ _

theorem convergentFreezeSum_weaklyCompact (R : X →L[𝕜] C(OnePoint ℕ, Y))
    (hR : IsWeaklyCompactOperator 𝕜 R)
    (hshrinking : ∀ Φ : StrongDual 𝕜 C(OnePoint ℕ, Y), Tendsto
      (fun n => banachAdjoint R (banachAdjoint (convergentFreeze (𝕜 := 𝕜) (Y := Y) n) Φ))
      atTop (𝓝 (banachAdjoint R Φ))) :
    IsWeaklyCompactOperator 𝕜 (convergentFreezeSum R) := by
  apply lp1Sum_weaklyCompact_of_adjoint_tendsto _ R R.opNorm_nonneg
    (norm_convergentFreeze_comp_le R)
    (fun n => hR.comp_left (convergentFreeze (𝕜 := 𝕜) (Y := Y) n)) hR hshrinking
  exact convergentDual_coordinate_span_dense

lemma convergentFreezeSum_intertwines (R : X →L[𝕜] C(OnePoint ℕ, Y)) (m : ℕ) :
    (convergentFreezeSum R).comp (lp1Fold (𝕜 := 𝕜) (X := X) m) =
      (convergentFreeze (𝕜 := 𝕜) (Y := Y) m).comp (convergentFreezeSum R) := by
  apply lp1Sum_comp_fold
  intro n
  rw [← ContinuousLinearMap.comp_assoc, convergentFreeze_comp (𝕜 := 𝕜) (Y := Y)]

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
variable [NormedSpace ℝ Y] [IsScalarTower ℝ 𝕜 Y]

lemma convergentHull_freeze_mem (R : X →L[𝕜] C(OnePoint ℕ, Y))
    (n : ℕ) (x : X) (hx : ‖x‖ ≤ 1) :
    convergentFreeze (𝕜 := 𝕜) (Y := Y) n (R x) ∈ (operatorGaugeData (convergentFreezeSum R)).carrier := by
  apply subset_closure
  refine ⟨lp.single 1 n x, ?_, convergentFreezeSum_single R n x⟩
  rw [mem_closedBall_zero_iff, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
  exact hx

lemma convergentHull_lift_mem (R : X →L[𝕜] C(OnePoint ℕ, Y))
    (x : X) (hx : ‖x‖ ≤ 1) :
    R x ∈ (operatorGaugeData (convergentFreezeSum R)).carrier := by
  exact isClosed_closure.mem_of_tendsto (convergentFreeze_tendsto (𝕜 := 𝕜) (Y := Y) (R x))
    (Eventually.of_forall fun n => convergentHull_freeze_mem R n x hx)

theorem convergentHull_preserved (R : X →L[𝕜] C(OnePoint ℕ, Y)) (m : ℕ) :
    ∀ z ∈ (operatorGaugeData (convergentFreezeSum R)).carrier,
      convergentFreeze (𝕜 := 𝕜) (Y := Y) m z ∈ (operatorGaugeData (convergentFreezeSum R)).carrier := by
  exact operatorGaugeData_preserved _ _ (lp1Fold (𝕜 := 𝕜) (X := X) m) (norm_lp1Fold_le_one (𝕜 := 𝕜) (X := X) m)
    (convergentFreezeSum_intertwines R m).symm

end SurveyStatements.P4
