import PFP.GeneralSumBlockStatements
import ThesisCommon.Analysis.LpLargeDiagonalBlocks

/-! Lemma 4.25: Hajnal selection from the exact triangular block
decomposition, including the all-vector diagonal identity on W.
-/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Exact Lemma 4.25. The WCG and projection premises are retained in the
statement; their role is to provide the assumed block decomposition in 4.24.
Once that decomposition is given, the proof uses its triangular support and
countability conclusions, Hajnal's theorem, and the genuine ℓ₁ expansion. -/
theorem lemma_4_25 : Lemma_4_25 𝕜 Γ X := by
  intro hΓ _hWCG P _hP B hB
  obtain ⟨hpart, htri, _hcomp, hcount⟩ := hB
  have hindex : Cardinal.aleph 1 < Cardinal.mk (CoordinateBlockIndex Γ) := by
    simpa only [CoordinateBlockIndex, Cardinal.mk_ord_toType] using hΓ
  obtain ⟨H, hHcard, hdiag, hall⟩ := lp_exists_large_diagonal_blocks 1
    (by norm_num) hindex P B hpart.1 htri hcount
  refine ⟨H, ?_, hdiag, hall⟩
  simpa only [CoordinateBlockIndex, Cardinal.mk_ord_toType] using hHcard

end PFP
