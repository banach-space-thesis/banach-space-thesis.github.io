import ThesisCommon.Analysis.SchauderSumOperators

/-! Insert scalar coefficients along any chosen family of unit-ball vectors
in the inner space. This is the bounded map used to transfer outer weak
nullity to the rows of a functional on the vector-valued sum.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem exists_vector_insertion (v : ℕ → Y) (hv : ∀ n, ‖v n‖ ≤ 1) :
    ∃ B : X →L[𝕜] SchauderSum b hb Y, ‖B‖ ≤ 1 ∧
      ∀ n, B (b.vector n) = single n (v n) := by
  apply b.exists_operator (fun n => single n (v n)) zero_le_one
  intro F a
  have heq : (∑ n ∈ F, a n • single (b := b) (hb := hb) n (v n)) =
      ∑ n ∈ F, single n (a n • v n) := by
    apply Finset.sum_congr rfl
    intro n _
    exact (map_smul (singleL (b := b) (hb := hb) (Y := Y) n) (a n) (v n)).symm
  rw [heq, norm_sum_single]
  exact hb.2 F (fun n => (‖a n • v n‖ : 𝕜)) a (by
    intro n _
    rw [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_smul]
    exact (mul_le_mul_of_nonneg_left (hv n) (norm_nonneg (a n))).trans_eq (mul_one _))

end SchauderSum
end ThesisCommon
