import PFP.MatrixDiagonalProofs
import PFP.MatrixAlmostDiagonalProofs
import ThesisCommon.Analysis.SharpFactorization

/-! The genuine growing matrix product has 4⁺-PFP; in particular it has
the exact constant 8 asserted in Theorem 5.14. All reduction hypotheses
are discharged by Lemma 5.11 and Proposition 5.13. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem matrixSum_hasCPlusPFP_four (p : BanachExponent)
    (hp : 1 < p.val) (hfin : p.val ≠ ∞) :
    HasCPlusPFP 𝕜 (MatrixSum 𝕜 p) 4 := by
  apply hasCPlusPFP_of_approximate_compressions (by norm_num : (0 : ℝ) < 4)
    (IsMatrixSumDiagonal p)
  · intro D hD
    obtain ⟨U, V, hbranch, hn⟩ := proposition_5_13 (𝕜 := 𝕜) p hp hfin D hD
    rcases hbranch with h | h
    · exact Or.inl ⟨U, V, h, hn⟩
    · exact Or.inr ⟨U, V, h, hn⟩
  · intro T η hη
    obtain ⟨A, B, T', D, hnA, hnB, hAB, hT', hD, he, _⟩ :=
      lemma_5_11 𝕜 p hp hfin T η hη
    exact ⟨A, B, D, hAB, hnA, hnB, hD, hT' ▸ he⟩

theorem theorem_5_14 : Theorem_5_14 𝕜 := by
  intro p hp hfin
  have h := matrixSum_hasCPlusPFP_four (𝕜 := 𝕜) p hp hfin 4 (by norm_num)
  norm_num at h ⊢
  exact h

end PFP
