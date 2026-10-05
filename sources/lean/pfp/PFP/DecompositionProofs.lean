import PFP.DecompositionStatements
import ThesisCommon.Analysis.PelczynskiDecompositionFull

/-! Full proofs of Theorem 2.3 and Appendix A.1. The quantitative theorem
uses precisely the printed admissible constants, actual attained bounded
equivalences, and the matching finite-product and sequence-space norms. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜]

theorem theorem_A_1_square {C1 C2 C3 C4 C5 C6 : ℝ}
    (h1 : 0 ≤ C1) (h2 : 1 ≤ C2) (h3 : 0 ≤ C3) (h4 : 1 ≤ C4)
    (h5 : 1 ≤ C5) (h6 : 1 ≤ C6) :
    Theorem_A_1_square.{u,v} 𝕜 C1 C2 C3 C4 C5 C6 := by
  refine ⟨one_le_decompositionSquareBound h1 h3 h5 h6, ?_⟩
  intro X Y _ _ _ _ _ _ hXY hYX hSq
  exact quantitativeDecomposition_square h1 h2 h3 h4 h5 h6 hXY hYX hSq

theorem theorem_A_1_sequence {C1 C2 C3 C4 C5 : ℝ}
    (h1 : 0 ≤ C1) (h2 : 1 ≤ C2) (h3 : 0 ≤ C3) (h4 : 1 ≤ C4) (h5 : 1 ≤ C5) :
    Theorem_A_1_sequence.{u,v} 𝕜 C1 C2 C3 C4 C5 := by
  refine ⟨one_le_decompositionSequenceBound h1 h3 h5, ?_⟩
  intro X Y _ _ _ _ _ _ hXY hYX hStable
  exact quantitativeDecomposition_sequence h1 h2 h3 h4 h5 hXY hYX hStable

theorem theorem_A_1 : Theorem_A_1.{u,v} 𝕜 := by
  constructor
  · intro C1 C2 C3 C4 C5 C6 h1 h2 h3 h4 h5 h6
    exact theorem_A_1_square 𝕜 h1 h2 h3 h4 h5 h6
  · intro C1 C2 C3 C4 C5 h1 h2 h3 h4 h5
    exact theorem_A_1_sequence 𝕜 h1 h2 h3 h4 h5

theorem theorem_2_3 (X : Type u) (Y : Type v)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y] :
    Theorem_2_3 𝕜 X Y := by
  intro hXY hYX hStable
  exact pelczynskiDecomposition_full hXY hYX hStable

end PFP
