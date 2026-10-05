import ThesisCommon.Analysis.WeakCompactClosed
import ThesisCommon.Analysis.Primary
import Mathlib.Analysis.Normed.Module.Complemented

/-! Concrete vocabulary for Appendix B of the PFP manuscript.

Quasi-reflexivity is measured in the actual quotient of the bidual by the
canonical image. Hyperplanes are actual closed submodules of codimension one.
The complemented-subspace predicate is mathlib's `Submodule.ClosedComplemented`,
which supplies a continuous linear retraction onto the inherited subspace.
None of the permanence conclusions is included in these definitions.
-/
noncomputable section
set_option synthInstance.maxSize 1024
namespace ThesisCommon

variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

-- Fix the ambient bidual in quotient instance search, as in `Residuum`.
local instance quasiReflexiveBidualNormedAddCommGroup : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 X)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 X) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance quasiReflexiveBidualNormedSpace : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 X) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance quasiReflexiveBidualHasQuotient : HasQuotient (StrongDual 𝕜 (StrongDual 𝕜 X))
    (Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X))) :=
  @Submodule.hasQuotient 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X))
    inferInstance inferInstance inferInstance

/-- The canonical image of a Banach space is closed in its actual bidual. -/
instance bidualImage_isClosed [CompleteSpace X] :
    IsClosed (bidualImage 𝕜 X : Set (StrongDual 𝕜 (StrongDual 𝕜 X))) :=
  isClosed_bidualImage (𝕜 := 𝕜) (F := X)

/-- The residuum of a Banach space has the genuine Hausdorff quotient norm. -/
instance residuumSpace_normedAddCommGroup [CompleteSpace X] :
    NormedAddCommGroup (ResiduumSpace 𝕜 X) := inferInstance

instance residuumSpace_normedSpace [CompleteSpace X] :
    NormedSpace 𝕜 (ResiduumSpace 𝕜 X) := inferInstance

instance residuumSpace_completeSpace [CompleteSpace X] :
    CompleteSpace (ResiduumSpace 𝕜 X) := inferInstance

/-- Quasi-reflexivity of order `n`: the canonical bidual quotient has exactly
dimension `n`. Cardinal rank, rather than truncated finite rank, records the
dimension directly, including the order-zero case. -/
def IsQuasiReflexiveOfOrder (n : ℕ) : Prop :=
  Module.rank 𝕜 (ResiduumSpace 𝕜 X) = n

/-- The order-one hypothesis used in Appendix B. -/
abbrev IsQuasiReflexiveOfOrderOne : Prop := IsQuasiReflexiveOfOrder 𝕜 X 1

/-- A closed hyperplane is a closed submodule with one-dimensional quotient. -/
def IsClosedHyperplane (H : Submodule 𝕜 X) : Prop :=
  IsClosed (H : Set X) ∧ Module.rank 𝕜 (X ⧸ H) = 1

/-- Every closed hyperplane, with its inherited norm, is boundedly linearly
isomorphic to the ambient space. -/
def IsIsomorphicToEveryHyperplane : Prop :=
  ∀ H : Submodule 𝕜 X, IsClosedHyperplane 𝕜 X H → Nonempty (X ≃L[𝕜] H)

/-- An isomorphism with the one-dimensional extension, with the usual product
norm. This is one conclusion of B.1, distinct from the all-hyperplanes claim. -/
def IsIsomorphicToScalarExtension : Prop := Nonempty (X ≃L[𝕜] (X × 𝕜))

/-- Finite order gives finite-dimensionality of the actual bidual quotient. -/
theorem IsQuasiReflexiveOfOrder.finiteDimensional {n : ℕ}
    (h : IsQuasiReflexiveOfOrder 𝕜 X n) :
    FiniteDimensional 𝕜 (ResiduumSpace 𝕜 X) :=
  FiniteDimensional.of_rank_eq_nat h

end ThesisCommon
