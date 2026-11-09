import PL1.Definitions

/-!
# Theorems A and B: full target propositions, awaiting human review

Authoritative source: manuscript/PL1_paper_updated.pdf, page 2, with companion
main.tex labels thm:main and thm:non-schur; scalar convention on pages 2–3.

These declarations DEFINE claims and do not assert proofs of those claims.
For complex scalars the nonlattice clause explicitly targets the stronger
underlying-real obstruction used by the paper's argument. A later formal bridge
to complex Banach-lattice nonisomorphism will be recorded separately; no silent
identification of real and complex lattice predicates is made here.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PL1

/-- All Theorem A clauses apply to this single projection and its actual range.
Closedness and infinite dimension are explicit consequences of the paper's
projection and failure-of-RNP conclusions. The explicit instance arguments in
the last clauses preserve exactly the inherited range norm when restricting
scalars; they avoid a parent-instance inference ambiguity. -/
def TheoremASpec (𝕜 : Type*) [RCLike 𝕜]
    (P : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) : Prop :=
  IsProjection P ∧
  ‖P‖ ≤ projectionBound ∧
  IsClosed (P.range : Set (IntervalL1 𝕜)) ∧
  ¬ FiniteDimensional 𝕜 P.range ∧
  IsDunfordPettis P ∧
  HasSchurProperty 𝕜 P.range ∧
  ¬ @HasRadonNikodymProperty.{_, 0} (UnderlyingReal 𝕜 P.range)
      (inferInstanceAs (NormedAddCommGroup P.range))
      (NormedSpace.restrictScalars ℝ 𝕜 P.range) ∧
  ¬ @HasEquivalentRealLatticeNorm (UnderlyingReal 𝕜 P.range)
      (inferInstanceAs (NormedAddCommGroup P.range))
      (NormedSpace.restrictScalars ℝ 𝕜 P.range)

/-- Theorem A, with an explicit underlying-real nonlattice conclusion. -/
def TheoremAStatement (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∃ P : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜, TheoremASpec 𝕜 P

/-- All Theorem B clauses apply to this same Q and its inherited range norm. -/
def TheoremBSpec (𝕜 : Type*) [RCLike 𝕜]
    (Q : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) : Prop :=
  IsProjection Q ∧
  ‖Q‖ ≤ projectionBound ∧
  IsClosed (Q.range : Set (IntervalL1 𝕜)) ∧
  ¬ FiniteDimensional 𝕜 Q.range ∧
  ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) Q.range ∧
  ¬ ContainsIsomorphicCopy 𝕜 (IntervalL1 𝕜) Q.range ∧
  ¬ HasSchurProperty 𝕜 Q.range ∧
  ¬ @HasEquivalentRealLatticeNorm (UnderlyingReal 𝕜 Q.range)
      (inferInstanceAs (NormedAddCommGroup Q.range))
      (NormedSpace.restrictScalars ℝ 𝕜 Q.range)

/-- Theorem B, with an explicit underlying-real nonlattice conclusion. -/
def TheoremBStatement (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∃ Q : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜, TheoremBSpec 𝕜 Q

/-- Planned proof declaration: theoremAReal. -/
def TheoremARealStatement : Prop := TheoremAStatement ℝ

/-- Planned proof declaration: theoremAComplexStrong. The strengthening over
the printed complex theorem is disclosed in this file and the review guide. -/
def TheoremAComplexStrongStatement : Prop := TheoremAStatement ℂ

/-- Planned proof declaration: theoremBReal. -/
def TheoremBRealStatement : Prop := TheoremBStatement ℝ

/-- Planned proof declaration: theoremBComplexStrong. -/
def TheoremBComplexStrongStatement : Prop := TheoremBStatement ℂ

/-- Four separate existences; the real/complex and A/B witnesses may differ. -/
def MainTheoremsStatement : Prop :=
  TheoremARealStatement ∧ TheoremAComplexStrongStatement ∧
  TheoremBRealStatement ∧ TheoremBComplexStrongStatement

end PL1
