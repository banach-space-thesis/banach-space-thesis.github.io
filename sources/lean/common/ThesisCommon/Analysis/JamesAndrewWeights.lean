import ThesisCommon.Analysis.Factorization

/-! A fixed positive summable error budget for the Andrew compression. -/
noncomputable section
namespace ThesisCommon

def jamesAndrewWeight (n : ℕ) : ℝ := (1 / 128) * (1 / 2) ^ n

theorem jamesAndrewWeight_pos (n : ℕ) : 0 < jamesAndrewWeight n := by
  unfold jamesAndrewWeight
  positivity

theorem jamesAndrewWeight_hasSum : HasSum jamesAndrewWeight (1 / 64 : ℝ) := by
  have h := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
    (1 / 128 : ℝ)
  norm_num at h
  exact h

theorem jamesAndrewWeight_summable : Summable jamesAndrewWeight := jamesAndrewWeight_hasSum.summable

theorem jamesAndrewWeight_tsum : ∑' n, jamesAndrewWeight n = (1 / 64 : ℝ) :=
  jamesAndrewWeight_hasSum.tsum_eq

end ThesisCommon
