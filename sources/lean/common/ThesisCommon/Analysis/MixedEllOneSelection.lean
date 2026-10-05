import ThesisCommon.Analysis.MixedEllOneEstimates
import ThesisCommon.Analysis.AsymmetricMatrixFusion

/-! All inputs to asymmetric selection are proved here for the genuine
mixed sum. The outer basis is symmetric and not equivalent to ell_1;
no inner weak-null hypothesis is used.
-/
noncomputable section
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem ellOne_asymmetric_selection (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ → ℕ) (m : ℕ → ℕ → ℕ), StrictMono n ∧ (∀ i, StrictMono (m i)) ∧
      ∀ r s i j, (r, s) ≠ (i, j) →
        ‖ellOneEntry T (n r) (m r s) (n i) (m i j)‖ ≤
          ε / (2 : ℝ) ^ (r + i + s + 3) := by
  obtain ⟨n, m, hn, hm, hsmall⟩ := asymmetric_matrix_selection
    (fun p q => ‖ellOneEntry T p.1 p.2 q.1 q.2‖)
    (fun p i => ε / (2 : ℝ) ^ (p.1 + i + p.2 + 3)) (by intros; positivity)
    (fun p η hη => ellOne_finite_interfering_rows hs hnot T p.1 p.2 hη)
    (fun p η hη => ellOne_finite_interfering_targets T p.1 p.2 hη)
    (fun r i => ‖block T r i‖) (fun r i j F => ellOne_column_sum_le (block T r i) j F)
  exact ⟨n, m, hn, hm, fun r s i j h => hsmall (r, s) (i, j) h⟩

end SchauderSum
end ThesisCommon
