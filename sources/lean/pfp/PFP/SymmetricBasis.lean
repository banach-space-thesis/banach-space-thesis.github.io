import PFP.MainStatements
import ThesisCommon.Analysis.SymmetricBasisPFP
import ThesisCommon.Analysis.LpSchauderBasis

/-! The normalized symmetric-basis statements of Section 3.1. The basis
consists of actual vectors and bounded functionals with convergent expansions.
The targets in this file do not postulate any subsequence isomorphisms.
-/
noncomputable section
open Filter Topology
namespace PFP
open ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Lemma 3.1, `lmm: sym-basis-affected`, with the genuine closed span of
each strictly increasing subsequence and an actual bounded isomorphism to ℓ₁.
The full equivalence is an open target; the rank-one step is checked separately. -/
def Lemma_3_1 [CompleteSpace X] (b : NormalizedSchauderBasis 𝕜 X) : Prop :=
  b.IsUnconditional →
    ((∀ f : ℕ → ℕ, StrictMono f →
      ¬ Nonempty (b.subsequenceSpan f ≃L[𝕜] ScalarEllOne 𝕜)) ↔
    ∀ (T : X →L[𝕜] X) n,
      Tendsto (fun m => b.coord n (T (b.vector m))) atTop (𝓝 0))

/-- Lemma 3.2, `lmm: small-norm`. Paper indices 1,2,... correspond to
Lean indices 0,1,..., accounting for the +2 in the geometric denominator. -/
def Lemma_3_2 (b : NormalizedSchauderBasis 𝕜 X) : Prop :=
  b.IsOneUnconditional → ∀ (T : X →L[𝕜] X) (ε : ℝ), 0 < ε →
    (∀ m n, ‖b.coord m (T (b.vector n))‖ < ε / (2 : ℝ) ^ (m + n + 2)) →
    ‖T‖ ≤ ε

theorem lemma_3_2 (b : NormalizedSchauderBasis 𝕜 X) : Lemma_3_2 b := by
  intro hb T ε hε hT
  exact b.norm_le_of_geometric_entries hb T hε.le (fun m n => (hT m n).le)

/-- Theorem 3.3, `th: Cassaza-Lin`, with the source's standing normalization.
Equivalence to the ℓ₁ basis is its two-sided finite coefficient norm inequality;
the upper bound one is proved from normalization. Symmetry is finite permutation
invariance and unconditionality of the actual norm. -/
def Theorem_3_3 [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (b : NormalizedSchauderBasis 𝕜 X) : Prop :=
  b.HasSymmetricNorm → ¬ b.EquivalentEllOne → HasCPlusPFP 𝕜 X 2

theorem theorem_3_3 [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (b : NormalizedSchauderBasis 𝕜 X) : Theorem_3_3 b := by
  intro hb hnot
  exact b.hasCPlusPFP_two hb hnot

end PFP
