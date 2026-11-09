import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.Bases

/-!
# Problem 4: weakly compact basis factorization

Source: `source/problems/P4-basis-factorisation.tex`, main theorem
`p5:thm:main` (the source retains an older `p5` label).

All spaces are over a real or complex scalar field. Definitions below use the
norm topology unless a `WeakSpace` type is explicitly present. The sole proof
placeholder is the main theorem; the definitions have no placeholders.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

universe u v w z

variable (𝕜 : Type u) [RCLike 𝕜]

/-- A bounded linear map has finite rank when its algebraic range is
finite-dimensional. -/
def HasFiniteRank {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (A : E →L[𝕜] F) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.range A.toLinearMap)

/-- The bounded approximation property: one common operator-norm bound works
for finite-rank approximations to the identity, uniformly on every compact set.
This definition does not build separability into the property. -/
def HasBoundedApproximationProperty (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ K : Set E, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ A : E →L[𝕜] E,
        HasFiniteRank 𝕜 A ∧ ‖A‖ ≤ C ∧ ∀ x ∈ K, ‖A x - x‖ < ε

/-- A bounded linear operator is weakly compact when the weak closure of its
closed-unit-ball image is compact in the weak topology on the codomain.
The closure is deliberately taken after changing to `WeakSpace`. -/
def IsWeaklyCompactOperator {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) : Prop :=
  IsCompact (closure ((toWeakSpace 𝕜 F) '' (T '' Metric.closedBall (0 : E) 1)))

/-- Topological reflexivity: every continuous functional on the continuous
dual is evaluation at a vector. This is continuous-dual reflexivity, not the
stronger algebraic-dual notion `Module.IsReflexive`. -/
def IsReflexiveNormedSpace (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)

/-- The first `N` terms of an ordered expansion indexed by a subset of `ℕ`.
For a finite initial segment, these sums eventually become the full finite sum. -/
def schauderPartialSum {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {I : Set ℕ} (b : I → E) (a : I → 𝕜) (N : ℕ) : E := by
  classical
  exact ∑ n ∈ Finset.range N, if h : n ∈ I then a ⟨n, h⟩ • b ⟨n, h⟩ else 0

/-- An ordered Schauder basis: its index set is an initial segment of `ℕ`, and
every vector has a unique scalar expansion whose initial partial sums converge
in norm. The index set may be empty, finite, or all of `ℕ`, so this includes
finite-dimensional spaces and the zero space. Using ordered sums here is
essential: an unordered `HasSum` would impose unconditional convergence. -/
def IsSchauderBasis {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {I : Set ℕ} (b : I → E) : Prop :=
  IsLowerSet I ∧ ∀ x : E, ∃! a : I → 𝕜,
    Tendsto (schauderPartialSum 𝕜 b a) atTop (𝓝 x)

/-- Existence of a finite or countably infinite ordered Schauder basis. -/
def HasSchauderBasis (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∃ (I : Set ℕ) (b : I → E), IsSchauderBasis 𝕜 b

/-- A bundled intermediate space keeps the Banach-space structure inside the
existential assertion of the factorization theorem. -/
structure ReflexiveBanachSpaceWithBasis where
  Carrier : Type z
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace 𝕜 Carrier]
  [completeSpace : CompleteSpace Carrier]
  reflexive : IsReflexiveNormedSpace 𝕜 Carrier
  schauderBasis : HasSchauderBasis 𝕜 Carrier

attribute [instance] ReflexiveBanachSpaceWithBasis.normedAddCommGroup
  ReflexiveBanachSpaceWithBasis.normedSpace ReflexiveBanachSpaceWithBasis.completeSpace

/-- A factorization consists of bounded linear maps `A : X → V` and `B : V → Y`
with `B ∘ A = T`; the witness `V` is a reflexive Banach space with a Schauder basis.
The witness universe is large enough for either original space and the field. -/
def FactorsThroughReflexiveBasisSpace {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y) : Prop :=
  ∃ V : ReflexiveBanachSpaceWithBasis.{u, max u v w} 𝕜,
    ∃ A : X →L[𝕜] V.Carrier, ∃ B : V.Carrier →L[𝕜] Y, B.comp A = T


end SurveyStatements.P4

