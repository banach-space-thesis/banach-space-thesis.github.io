import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Evaluation along an actual bounded sequence followed by limsup gives
a seminorm on continuous linear maps. No convergence of the sequence or
of its images is assumed. -/
noncomputable section
open Filter
namespace ThesisCommon
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem operator_sequence_norm_le (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (T : E →L[𝕜] F) (n : ℕ) : ‖T (x n)‖ ≤ ‖T‖ :=
  (T.le_opNorm (x n)).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hx n) (norm_nonneg T))

theorem operator_sequence_boundedAbove (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (T : E →L[𝕜] F) : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖T (x n)‖) :=
  isBoundedUnder_of_eventually_le (Eventually.of_forall (operator_sequence_norm_le x hx T))

theorem operator_sequence_boundedBelow (x : ℕ → E) (T : E →L[𝕜] F) :
    IsBoundedUnder (· ≥ ·) atTop (fun n => ‖T (x n)‖) :=
  isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => norm_nonneg (T (x n))))

theorem operator_sequence_cobounded (x : ℕ → E) (T : E →L[𝕜] F) :
    IsCoboundedUnder (· ≤ ·) atTop (fun n => ‖T (x n)‖) :=
  isCoboundedUnder_le_of_le atTop (fun _ => norm_nonneg _)

def operatorSequenceSeminorm (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1) :
    Seminorm 𝕜 (E →L[𝕜] F) :=
  Seminorm.of (fun T => limsup (fun n => ‖T (x n)‖) atTop)
    (by
      intro S T
      have hbound : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖S (x n)‖ + ‖T (x n)‖) :=
        isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => add_le_add
          (operator_sequence_norm_le x hx S n) (operator_sequence_norm_le x hx T n)))
      apply (limsup_le_limsup (Eventually.of_forall (fun n => by
        simpa only [ContinuousLinearMap.add_apply] using norm_add_le (S (x n)) (T (x n))))
        (operator_sequence_cobounded x (S+T)) hbound).trans
      exact limsup_add_le (operator_sequence_boundedBelow x S) (operator_sequence_boundedAbove x hx S)
        (operator_sequence_cobounded x T) (operator_sequence_boundedAbove x hx T))
    (by
      intro c T
      simp only [ContinuousLinearMap.smul_apply, norm_smul]
      have hm : Monotone (fun r : ℝ => ‖c‖ * r) :=
        fun _ _ h => mul_le_mul_of_nonneg_left h (norm_nonneg c)
      exact (hm.map_limsup_of_continuousAt (fun n => ‖T (x n)‖)
        (continuous_const.mul continuous_id).continuousAt
        (operator_sequence_boundedAbove x hx T) (operator_sequence_cobounded x T)).symm)

theorem operatorSequenceSeminorm_apply (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (T : E →L[𝕜] F) : operatorSequenceSeminorm x hx T = limsup (fun n => ‖T (x n)‖) atTop := rfl

theorem operatorSequenceSeminorm_le_norm (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (T : E →L[𝕜] F) : operatorSequenceSeminorm x hx T ≤ ‖T‖ :=
  limsup_le_of_le (operator_sequence_cobounded x T)
    (Eventually.of_forall (operator_sequence_norm_le x hx T))

end ThesisCommon
