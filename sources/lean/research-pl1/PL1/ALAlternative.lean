import PL1.ALAtomic
import PL1.ALDyadicEmbedding
import PL1.PositiveLowerOneBridge
import PL1.IntervalSumming
import PL1.ProjectionTransport

/-!
# The separable complemented-L1 lattice alternative

Actual atomic coordinates give the Schur branch. Actual balanced fragments
give the interval-L1 branch. Finite Grothendieck estimates and the positive
decomposition norm connect this alternative to a complemented Banach lattice
in real interval L1. No representation or extraction theorem is a premise.
-/

noncomputable section
open TopologicalSpace

namespace PL1.ALAlternative

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E] [CompleteSpace E] [SeparableSpace E]

/-- Every separable complete AL lattice is Schur or contains actual interval L1. -/
theorem schur_or_contains_interval (hAL : ALRenorming.IsALNorm E) :
    HasSchurProperty ℝ E ∨ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) E := by
  by_cases hA : IsAtomicLattice E
  · exact Or.inl (ALAtomic.hasSchurProperty hAL hA)
  · exact Or.inr (ALDyadicEmbedding.containsIsomorphicCopy_of_not_atomic hAL hA)

/-- A positive finite lower-one bound produces the same alternative in the
original norm, through the actual equivalent AL norm. -/
theorem schur_or_contains_interval_of_positiveLowerOne {C : ℝ}
    (hC : ALRenorming.PositiveLowerOne (E := E) C) :
    HasSchurProperty ℝ E ∨ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) E := by
  let : NormedVectorLattice (ALRenorming.Space hC) := ALRenorming.normedVectorLattice hC
  let : CompleteSpace (ALRenorming.Space hC) := ALRenorming.completeSpace hC
  let : SeparableSpace (ALRenorming.Space hC) := ALRenorming.separableSpace hC
  obtain hs | hc := schur_or_contains_interval (ALRenorming.isALNorm hC)
  · exact Or.inl ((hasSchurProperty_equiv_iff (ALRenorming.equiv hC)).mpr hs)
  · exact Or.inr (ContainsIsomorphicCopy.map hc (ALRenorming.equiv hC).symm)

end PL1.ALAlternative

namespace PL1.ALAlternative

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [BanachLattice E] [TopologicalSpace.SeparableSpace E]

/-- The full direct alternative for an actual complemented real interval-L1
Banach lattice. All finite summing and renorming inputs are discharged. -/
theorem schur_or_contains_interval_of_complemented
    (Q : EnfloStarbird.ComplementedCopy ℝ E (IntervalL1 ℝ)) :
    HasSchurProperty ℝ E ∨ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) E :=
  schur_or_contains_interval_of_positiveLowerOne
    (PositiveLowerOneBridge.positiveLowerOne_of_complemented_ambient Q
      (by norm_num : (0 : ℝ) ≤ 128) IntervalSumming.oneSumming_interval
      IntervalSumming.twoSumming_interval)

end PL1.ALAlternative
