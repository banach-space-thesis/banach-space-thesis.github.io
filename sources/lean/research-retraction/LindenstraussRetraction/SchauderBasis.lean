import LindenstraussRetraction.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Sequential Schauder bases and monotone decompositions

The pinned Mathlib revision has no Schauder-basis structure. We use continuous
coordinate functionals, biorthogonality, and convergence of the ordered finite
partial sums. An unrestricted `HasSum` over `ℕ` would require unconditional
convergence, which is inappropriate for the main theorem.
-/

noncomputable section

open scoped BigOperators
open Filter Topology

namespace LindenstraussRetraction

universe u v

variable (𝕜 : Type v) [RCLike 𝕜]
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A sequential Schauder basis, indexed from zero.
On Banach spaces this is the usual Schauder basis, with its continuous
coordinate functionals. Biorthogonality rules out zero or redundant vectors. -/
structure SchauderBasis where
  vector : ℕ → X
  coord : ℕ → X →L[𝕜] 𝕜
  biorthogonal : ∀ n m, coord n (vector m) = if n = m then 1 else 0
  expansion : ∀ x : X,
    Tendsto (fun N => ∑ n ∈ Finset.range N, coord n x • vector n) atTop (𝓝 x)

namespace SchauderBasis

variable {𝕜 X}

/-- Projection onto the first `N` basis vectors; `partialSum 0 = 0`. -/
def partialSum (b : SchauderBasis 𝕜 X) (N : ℕ) : X →L[𝕜] X :=
  ∑ n ∈ Finset.range N, (b.coord n).smulRight (b.vector n)

/-- All initial-segment projections are contractive. -/
def IsMonotone (b : SchauderBasis 𝕜 X) : Prop :=
  ∀ N, ‖b.partialSum N‖ ≤ 1

/-- Both initial-segment and complementary tail projections are contractive.
This is the prefix/tail convention for bimonotonicity. It does not assert
contractivity for arbitrary subsets of basis indices (unconditionality). -/
def IsBimonotone (b : SchauderBasis 𝕜 X) : Prop :=
  b.IsMonotone ∧ ∀ N, ‖ContinuousLinearMap.id 𝕜 X - b.partialSum N‖ ≤ 1

end SchauderBasis

/-- Existence of a bimonotone sequential Schauder basis. -/
def HasBimonotoneSchauderBasis : Prop :=
  ∃ b : SchauderBasis 𝕜 X, b.IsBimonotone

/-- A monotone finite-dimensional decomposition in terms of its partial-sum
projections. Zero blocks are allowed; the blocks are the ranges of
`projection (N + 1) - projection N`. -/
structure MonotoneFDD where
  projection : ℕ → X →L[𝕜] X
  projection_zero : projection 0 = 0
  finite_rank : ∀ N, FiniteDimensional 𝕜 (LinearMap.range (projection N).toLinearMap)
  compatible : ∀ N M, (projection N).comp (projection M) = projection (min N M)
  contractive : ∀ N, ‖projection N‖ ≤ 1
  tendsTo_identity : ∀ x : X, Tendsto (fun N => projection N x) atTop (𝓝 x)

end LindenstraussRetraction
