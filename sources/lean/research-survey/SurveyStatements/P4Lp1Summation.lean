import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Bounded families of operators act on the genuine absolutely summable sum.
The dual pairing used in the sequence bridge is an actual bounded map. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology
open scoped ENNReal

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma lp1_summable_norm (x : lp (fun _ : ℕ => X) 1) : Summable (fun n => ‖x n‖) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

lemma lp1_tsum_norm (x : lp (fun _ : ℕ => X) 1) : ∑' n, ‖x n‖ = ‖x‖ := by
  simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x).symm

lemma lp1_operator_summable_norm (A : ℕ → X →L[𝕜] E) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C) (x : lp (fun _ : ℕ => X) 1) :
    Summable (fun n => ‖A n (x n)‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((lp1_summable_norm x).mul_left C)
  exact ((A n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _))

variable [CompleteSpace E]

def lp1Sum (A : ℕ → X →L[𝕜] E) {C : ℝ} (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C) :
    lp (fun _ : ℕ => X) 1 →L[𝕜] E :=
  ({ toFun := fun x => ∑' n, A n (x n)
     map_add' := by
       intro x y
       simp only [lp.coeFn_add, Pi.add_apply, map_add]
       exact (lp1_operator_summable_norm A hC hA x).of_norm.tsum_add
         (lp1_operator_summable_norm A hC hA y).of_norm
     map_smul' := by
       intro a x
       simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
       exact tsum_const_smul'' a } : lp (fun _ : ℕ => X) 1 →ₗ[𝕜] E).mkContinuous C
    (fun x => by
      calc
        ‖∑' n, A n (x n)‖ ≤ ∑' n, ‖A n (x n)‖ :=
          norm_tsum_le_tsum_norm (lp1_operator_summable_norm A hC hA x)
        _ ≤ ∑' n, C * ‖x n‖ := Summable.tsum_le_tsum
          (fun n => ((A n).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _)))
          (lp1_operator_summable_norm A hC hA x) ((lp1_summable_norm x).mul_left C)
        _ = C * ‖x‖ := by rw [tsum_mul_left, lp1_tsum_norm])

@[simp] lemma lp1Sum_apply (A : ℕ → X →L[𝕜] E) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C) (x : lp (fun _ : ℕ => X) 1) :
    lp1Sum A hC hA x = ∑' n, A n (x n) := rfl

lemma norm_lp1Sum_le (A : ℕ → X →L[𝕜] E) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C) : ‖lp1Sum A hC hA‖ ≤ C := by
  exact LinearMap.mkContinuous_norm_le _ hC _

@[simp] lemma lp1Sum_single (A : ℕ → X →L[𝕜] E) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C) (n : ℕ) (x : X) :
    lp1Sum A hC hA (lp.single 1 n x) = A n x := by
  classical
  rw [lp1Sum_apply, tsum_eq_single n]
  · simp [lp.coeFn_single]
  · intro m hmn
    simp [lp.coeFn_single, Pi.single_eq_of_ne hmn]

end SurveyStatements.P4
