import ThesisCommon.Analysis.QuantitativeDecompositionDefinitions

/-! Full targets for source Theorem 2.3 and Appendix Theorem A.1.
These Prop definitions are specifications, not proofs of either theorem.
The explicit constants are fixed before the spaces and all geometric
witnesses. Both alternatives, including c₀ and the endpoint p=∞, are retained.
-/
noncomputable section
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜]

/-- Theorem 2.3, `th: pelcdecmethod`, both square and sequence alternatives.
The unqualified finite direct sums use the usual product maximum norm;
only bounded equivalence is asserted in this qualitative theorem. -/
def Theorem_2_3 (X : Type u) (Y : Type v)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y] : Prop :=
  HasComplementedCopy 𝕜 X Y → HasComplementedCopy 𝕜 Y X →
    ((Nonempty (X ≃L[𝕜] X × X) ∧ Nonempty (Y ≃L[𝕜] Y × Y)) ∨
      IsSequenceSelfSimilar 𝕜 X) → Nonempty (X ≃L[𝕜] Y)

/-- Appendix A.1(a), with the source's explicit a²b²C5C6 bound. All six
constants are parameters before the universally quantified Banach spaces.
The same r, with its actual ℓr product norm, occurs in both square hypotheses. -/
def Theorem_A_1_square (C1 C2 C3 C4 C5 C6 : ℝ) : Prop :=
  1 ≤ decompositionSquareBound C1 C2 C3 C4 C5 C6 ∧
    ∀ (X : Type u) (Y : Type v)
      [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
      HasComplementedCopyWithBound 𝕜 X Y C1 C2 →
      HasComplementedCopyWithBound 𝕜 Y X C3 C4 →
      (∃ r : BanachExponent,
        IsomorphicWithBound 𝕜 X (BanachDirectSum r X X) C5 ∧
        IsomorphicWithBound 𝕜 Y (BanachDirectSum r Y Y) C6) →
      IsomorphicWithBound 𝕜 X Y (decompositionSquareBound C1 C2 C3 C4 C5 C6)

/-- Appendix A.1(b), with the source's explicit a⁴b⁴C5⁴ bound. The same
bound works for every exponent 1≤p≤∞ and for c₀; it depends on no exponent,
space, projection, or isomorphism witness. -/
def Theorem_A_1_sequence (C1 C2 C3 C4 C5 : ℝ) : Prop :=
  1 ≤ decompositionSequenceBound C1 C2 C3 C4 C5 ∧
    ∀ (X : Type u) (Y : Type v)
      [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
      HasComplementedCopyWithBound 𝕜 X Y C1 C2 →
      HasComplementedCopyWithBound 𝕜 Y X C3 C4 →
      (IsomorphicWithBound 𝕜 X (CZeroSum X) C5 ∨
        ∃ p : BanachExponent, IsomorphicWithBound 𝕜 X (SequenceSum p X) C5) →
      IsomorphicWithBound 𝕜 X Y (decompositionSequenceBound C1 C2 C3 C4 C5)

/-- Full Appendix Theorem A.1, `thm:quant-pelc`, with explicit admissible
constants. Distortion constants retain the convention C≥1. Projection-norm
bounds are only required to be nonnegative, which includes zero projections
and in particular includes the usual convention C1,C3≥1. -/
def Theorem_A_1 : Prop :=
  (∀ C1 C2 C3 C4 C5 C6 : ℝ,
    0 ≤ C1 → 1 ≤ C2 → 0 ≤ C3 → 1 ≤ C4 → 1 ≤ C5 → 1 ≤ C6 →
      Theorem_A_1_square.{u,v} 𝕜 C1 C2 C3 C4 C5 C6) ∧
  (∀ C1 C2 C3 C4 C5 : ℝ,
    0 ≤ C1 → 1 ≤ C2 → 0 ≤ C3 → 1 ≤ C4 → 1 ≤ C5 →
      Theorem_A_1_sequence.{u,v} 𝕜 C1 C2 C3 C4 C5)

end PFP
