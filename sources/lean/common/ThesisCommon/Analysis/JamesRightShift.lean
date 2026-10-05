import ThesisCommon.Analysis.JamesStepDecomposition
import ThesisCommon.Analysis.JamesConstantPrefixes

/-! Zero insertion on the left is bounded by two on James space. Dropping
the inserted coordinates is a contractive left inverse. -/
noncomputable section
open Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesRightShift (k : ℕ) : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  match k with
  | 0 => ContinuousLinearMap.id 𝕜 _
  | k + 1 => jamesMonotoneCompose p hp (fun n => n - (k + 1))
      (fun _ _ h => Nat.sub_le_sub_right h _) (tendsto_sub_atTop_nat _) -
    (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) 0).smulRight
      (jamesConstantPrefix (𝕜 := 𝕜) p hp k)

@[simp] theorem jamesRightShift_apply (k n : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    jamesRightShift (𝕜 := 𝕜) p hp k x n = if n < k then 0 else x (n - k) := by
  cases k with
  | zero => simp [jamesRightShift]
  | succ k =>
    simp only [jamesRightShift, ContinuousLinearMap.sub_apply,
      JamesSequenceSpace.sub_apply, jamesMonotoneCompose_apply,
      ContinuousLinearMap.smulRight_apply, JamesSequenceSpace.coordinate_apply,
      JamesSequenceSpace.smul_apply, jamesConstantPrefix_apply, smul_eq_mul]
    by_cases hn : n < k + 1
    · rw [if_pos hn, if_pos (by omega), Nat.sub_eq_zero_of_le (by omega)]
      simp
    · rw [if_neg hn, if_neg (by omega), mul_zero, sub_zero]

theorem jamesRightShift_norm_bound (k : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    ‖jamesRightShift (𝕜 := 𝕜) p hp k x‖ ≤ 2 * ‖x‖ := by
  cases k with
  | zero => simpa only [jamesRightShift, ContinuousLinearMap.id_apply] using
      (by linarith [norm_nonneg x] : ‖x‖ ≤ 2 * ‖x‖)
  | succ k =>
    apply (norm_sub_le _ _).trans
    have hm := jamesMonotoneComposeValue_norm_le p hp (fun n => n - (k + 1))
      (fun _ _ h => Nat.sub_le_sub_right h _) (tendsto_sub_atTop_nat _) x
    have hc : ‖x 0 • jamesConstantPrefix (𝕜 := 𝕜) p hp k‖ ≤ ‖x‖ := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (jamesConstantPrefix_norm_le p hp k)
        (norm_nonneg _)).trans (by simpa only [mul_one] using x.norm_apply_le 0)
    change ‖jamesMonotoneComposeValue p hp (fun n => n - (k + 1))
      (fun _ _ h => Nat.sub_le_sub_right h _) (tendsto_sub_atTop_nat _) x‖ +
      ‖x 0 • jamesConstantPrefix (𝕜 := 𝕜) p hp k‖ ≤ _
    linarith

theorem jamesRightShift_norm_le (k : ℕ) : ‖jamesRightShift (𝕜 := 𝕜) p hp k‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (jamesRightShift_norm_bound p hp k)

def jamesDrop (k : ℕ) : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  jamesSample p hp (fun n => n + k) (by intro a b hab; dsimp; omega)

@[simp] theorem jamesDrop_apply (k n : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    jamesDrop (𝕜 := 𝕜) p hp k x n = x (n + k) := jamesSample_apply p hp _ _ x n

theorem jamesDrop_norm_le (k : ℕ) : ‖jamesDrop (𝕜 := 𝕜) p hp k‖ ≤ 1 :=
  jamesSample_norm_le p hp _ _

theorem jamesDrop_rightShift (k : ℕ) :
    (jamesDrop (𝕜 := 𝕜) p hp k).comp (jamesRightShift p hp k) =
      ContinuousLinearMap.id 𝕜 _ := by
  ext x n
  simp only [ContinuousLinearMap.comp_apply, jamesDrop_apply, jamesRightShift_apply,
    Nat.not_lt.mpr (Nat.le_add_left k n), if_false, Nat.add_sub_cancel,
    ContinuousLinearMap.id_apply]

end ThesisCommon
