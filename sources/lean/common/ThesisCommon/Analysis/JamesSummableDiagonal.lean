import ThesisCommon.Analysis.JamesSummingColumnBounds

/-! Actual James-space diagonal operators with absolutely summable scalar
coefficients, constructed as norm-convergent sums of coordinate rank-one maps. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ⊤)

def jamesDiagonalTerm (a : ℕ → 𝕜) (n : ℕ) :
    JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  (JamesSequenceSpace.coordinate n).smulRight (a n • jamesUnit p hp n)

theorem norm_jamesDiagonalTerm_le (a : ℕ → 𝕜) (n : ℕ) :
    ‖jamesDiagonalTerm p hp a n‖ ≤ 2 * ‖a n‖ := by
  rw [jamesDiagonalTerm, ContinuousLinearMap.norm_smulRight_apply, norm_smul]
  calc
    _ ≤ 1 * (‖a n‖ * 2) := mul_le_mul
      (JamesSequenceSpace.norm_coordinate_le n)
      (mul_le_mul_of_nonneg_left (jamesUnit_norm_le_two p hp n) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ = _ := by ring

theorem summable_jamesDiagonalTerm (a : ℕ → 𝕜) (ha : Summable (fun n => ‖a n‖)) :
    Summable (jamesDiagonalTerm p hp a) :=
  (ha.mul_left 2).of_norm_bounded (norm_jamesDiagonalTerm_le p hp a)

def jamesSummableDiagonal (a : ℕ → 𝕜) :
    JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  ∑' n, jamesDiagonalTerm p hp a n

theorem norm_jamesSummableDiagonal_le (a : ℕ → 𝕜)
    (ha : Summable (fun n => ‖a n‖)) :
    ‖jamesSummableDiagonal p hp a‖ ≤ 2 * ∑' n, ‖a n‖ := by
  have hn : Summable (fun n => ‖jamesDiagonalTerm p hp a n‖) :=
    (ha.mul_left 2).of_nonneg_of_le (fun n => norm_nonneg _) (norm_jamesDiagonalTerm_le p hp a)
  calc
    _ ≤ ∑' n, ‖jamesDiagonalTerm p hp a n‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, 2 * ‖a n‖ := hn.tsum_le_tsum (norm_jamesDiagonalTerm_le p hp a) (ha.mul_left 2)
    _ = _ := tsum_mul_left

theorem jamesSummableDiagonal_apply (a : ℕ → 𝕜)
    (ha : Summable (fun n => ‖a n‖)) (x : JamesSequenceSpace 𝕜 p) (i : ℕ) :
    jamesSummableDiagonal p hp a x i = a i * x i := by
  let ev := (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) i).comp
    (ContinuousLinearMap.apply 𝕜 (JamesSequenceSpace 𝕜 p) x)
  change ev (∑' n, jamesDiagonalTerm p hp a n) = _
  rw [ev.map_tsum (summable_jamesDiagonalTerm p hp a ha), tsum_eq_single i]
  · simp [ev, jamesDiagonalTerm, JamesSequenceSpace.coordinate, jamesUnit_apply, mul_comm]
  · intro n hni
    simp [ev, jamesDiagonalTerm, JamesSequenceSpace.coordinate, jamesUnit_apply, Ne.symm hni]

end ThesisCommon
