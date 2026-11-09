import SurveyStatements.P4Lp1Summation

/-! Contractive tail aggregation on the actual absolutely summable sum. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped ENNReal

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

lemma norm_lp1Single_le_one (n : ℕ) :
    ‖lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [lp.singleContinuousLinearMap_apply, one_mul] using
    (lp.norm_single (E := fun _ : ℕ => X) (by norm_num : 0 < (1 : ℝ≥0∞)) n x).le

def lp1Fold (m : ℕ) : lp (fun _ : ℕ => X) 1 →L[𝕜] lp (fun _ : ℕ => X) 1 :=
  lp1Sum (fun n => lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 (min m n))
    (by norm_num) (fun n => norm_lp1Single_le_one _)

lemma norm_lp1Fold_le_one (m : ℕ) : ‖lp1Fold (𝕜 := 𝕜) (X := X) m‖ ≤ 1 :=
  norm_lp1Sum_le _ (by norm_num) _

@[simp] lemma lp1Fold_single (m n : ℕ) (x : X) :
    lp1Fold (𝕜 := 𝕜) m (lp.single 1 n x) = lp.single 1 (min m n) x :=
  lp1Sum_single _ _ _ _ _

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

lemma lp1Sum_comp_fold (A : ℕ → X →L[𝕜] E) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C) (S : E →L[𝕜] E) (m : ℕ)
    (hSA : ∀ n, S.comp (A n) = A (min m n)) :
    (lp1Sum A hC hA).comp (lp1Fold m) = S.comp (lp1Sum A hC hA) := by
  apply lp.ext_continuousLinearMap (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
  intro n
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    lp1Fold_single, lp1Sum_single]
  exact (congrArg (fun B : X →L[𝕜] E => B x) (hSA n)).symm

end SurveyStatements.P4
