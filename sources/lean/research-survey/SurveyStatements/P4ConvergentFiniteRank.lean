import SurveyStatements.P4ConvergentOperators
import SurveyStatements.P4ConvergentDualBasics
import SurveyStatements.P4FiniteRankCalculus

/-! Every freeze of a finite-rank sequence lift has actual finite rank. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology
open scoped OnePoint BigOperators

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def convergentConstant : Y →L[𝕜] C(OnePoint ℕ, Y) :=
  ({ toFun := fun y => ContinuousMap.const _ y
     map_add' := by intros; ext p; rfl
     map_smul' := by intros; ext p; rfl } : Y →ₗ[𝕜] C(OnePoint ℕ, Y)).mkContinuous 1
    (fun y => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg y)).mpr
      intro p
      exact le_rfl)

lemma convergentFreeze_lift_formula (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y)
    (hpoint : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)))
    {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C) (m : ℕ) :
    (convergentFreeze m).comp (convergentLift A T hpoint hA) =
      convergentConstant.comp (A m) +
        ∑ k ∈ Finset.range m, (convergentDualSingle k).comp (A k - A m) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply]
  ext p
  cases p using OnePoint.rec with
  | infty =>
      simp only [ContinuousLinearMap.comp_apply, convergentFreeze_infty,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
        ContinuousMap.add_apply, ContinuousMap.sum_apply, convergentDualSingle_infty,
        Finset.sum_const_zero, add_zero]
      rfl
  | coe n =>
      change A (min m n) x = A m x +
        (∑ k ∈ Finset.range m, convergentDualSingle (𝕜 := 𝕜) k ((A k - A m) x))
          (n : OnePoint ℕ)
      rw [convergentDualSingle_sum_coe]
      by_cases hn : n < m
      · rw [if_pos (Finset.mem_range.mpr hn), min_eq_right hn.le,
          ContinuousLinearMap.sub_apply]
        abel
      · rw [if_neg (by simpa using hn), min_eq_left (Nat.le_of_not_gt hn), add_zero]

theorem convergentFreeze_lift_finiteRank (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y)
    (hfinite : ∀ n, HasFiniteRank 𝕜 (A n))
    (hpoint : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)))
    {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C) (m : ℕ) :
    HasFiniteRank 𝕜 ((convergentFreeze m).comp (convergentLift A T hpoint hA)) := by
  rw [convergentFreeze_lift_formula]
  exact ((hfinite m).comp_left convergentConstant).add_map
    (HasFiniteRank.sum_map _ _ (fun k hk => ((hfinite k).sub_map (hfinite m)).comp_left _))

end SurveyStatements.P4
