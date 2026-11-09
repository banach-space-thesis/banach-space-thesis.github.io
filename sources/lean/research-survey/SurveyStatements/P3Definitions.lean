import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Problem 3: strict cosingularity and adjoints

Source: `source/problems/P3-cosingular-and-singular.tex`,
Theorem `p4:thm:main` and Definition `p4:def:strictly-singular-cosingular`.

The scalar field is real or complex (`RCLike`). The source's convention that
subspaces in these definitions are norm closed is included explicitly.
These definitions contain no deferred proofs.
-/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- `T` is bounded below on `M` if it has a uniform positive lower norm bound there. -/
def IsBoundedBelowOn (T : X →L[𝕜] Y) (M : Submodule 𝕜 X) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ M, c * ‖x‖ ≤ ‖T x‖

/-- An operator is strictly singular when its restriction to every norm-closed,
infinite-dimensional subspace fails to be bounded below. -/
def IsStrictlySingular (T : X →L[𝕜] Y) : Prop :=
  ∀ M : Submodule 𝕜 X, IsClosed (M : Set X) →
    ¬ FiniteDimensional 𝕜 M → ¬ IsBoundedBelowOn T M

/-- An operator is strictly cosingular if its composition with the quotient map
onto every infinite-dimensional quotient by a norm-closed subspace is not onto.
The quotient here is the actual vector-space quotient `Y ⧸ M`; its algebraic
dimension and the surjectivity of the quotient map do not require a choice of norm. -/
def IsStrictlyCosingular (T : X →L[𝕜] Y) : Prop :=
  ∀ M : Submodule 𝕜 Y, IsClosed (M : Set Y) →
    ¬ FiniteDimensional 𝕜 (Y ⧸ M) →
      ¬ Function.Surjective (fun x : X => M.mkQ (T x))

/-- The Banach-space adjoint `T* : Y* → X*`, defined by `f ↦ f ∘ T`.
Both duals carry the operator norm. This is composition of continuous linear
maps, bundled as a continuous linear map, in mathlib 4.24. -/
def adjoint (T : X →L[𝕜] Y) : (Y →L[𝕜] 𝕜) →L[𝕜] (X →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 X Y 𝕜).flip T


end SurveyStatements.P3

