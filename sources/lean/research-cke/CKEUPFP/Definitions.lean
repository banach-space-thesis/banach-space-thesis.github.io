import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.Nat

/-!
# Definitions for the UPFP transfer theorem

Source: `source/2-Preliminaries.tex`, Definitions `def:factor-through` and
`def:upfp`, and the first paragraph of `source/1-Introduction.tex`.
The scalar type is real or complex, expressed using `RCLike`.
All operators below are genuine continuous linear maps with operator norms.
-/

noncomputable section

universe u v w z t

namespace CKEUPFP

open scoped ZeroAtInfty

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type z} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable {W : Type t} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- `S` factors through `T`: the domain of the right factor is the domain of `S`.
Composition is `U ∘ T ∘ V`, exactly as in `def:factor-through`. -/
def FactorsThrough (S : Z →L[𝕜] W) (T : X →L[𝕜] Y) : Prop :=
  ∃ U : Y →L[𝕜] W, ∃ V : Z →L[𝕜] X, (U.comp T).comp V = S

/-- Factorisation with bound `C`. The norm of `T` is not part of the cost. -/
def FactorsThroughWith (S : Z →L[𝕜] W) (T : X →L[𝕜] Y) (C : ℝ) : Prop :=
  ∃ U : Y →L[𝕜] W, ∃ V : Z →L[𝕜] X,
    (U.comp T).comp V = S ∧ ‖U‖ * ‖V‖ ≤ C

variable (𝕜 X)

/-- Definition `def:upfp`(a). The alternative and factors may depend on `T`. -/
def HasPFP : Prop :=
  ∀ T : X →L[𝕜] X,
    FactorsThrough (ContinuousLinearMap.id 𝕜 X) T ∨
      FactorsThrough (ContinuousLinearMap.id 𝕜 X) (ContinuousLinearMap.id 𝕜 X - T)

/-- Definition `def:upfp`(b), including the paper's requirement `1 ≤ C`. -/
def HasCPFP (C : ℝ) : Prop :=
  1 ≤ C ∧ ∀ T : X →L[𝕜] X,
    FactorsThroughWith (ContinuousLinearMap.id 𝕜 X) T C ∨
      FactorsThroughWith (ContinuousLinearMap.id 𝕜 X) (ContinuousLinearMap.id 𝕜 X - T) C

/-- Definition `def:upfp`(c). One constant is chosen before all operators. -/
def HasUPFP : Prop :=
  ∃ C : ℝ, HasCPFP 𝕜 X C

/-- Primariness, as defined in the Introduction. Both ranges carry the
inherited norm, and `≃L` denotes a continuous linear equivalence. -/
def IsPrimary : Prop :=
  ∀ P : X →L[𝕜] X, P.comp P = P →
    Nonempty (X ≃L[𝕜] LinearMap.range P.toLinearMap) ∨
      Nonempty (X ≃L[𝕜] LinearMap.range (ContinuousLinearMap.id 𝕜 X - P).toLinearMap)

/-- Scalar null sequences with the supremum norm. On discrete `ℕ`, vanishing
at infinity means precisely convergence to zero. -/
abbrev CZero := C₀(ℕ, 𝕜)

/-- `X` contains `Y` via a continuous linear embedding with a positive lower norm bound.
For a Banach domain, its range is closed and the inverse on the range is bounded.
This condition neither asks for an isometry nor for a complemented range. -/
def ContainsIsomorphicCopy (Y : Type w) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] : Prop :=
  ∃ J : Y →L[𝕜] X, ∃ c : ℝ, 0 < c ∧ ∀ y : Y, c * ‖y‖ ≤ ‖J y‖

/-- The hypothesis that `X` contains no isomorphic copy of scalar `c₀`. -/
def ContainsNoCZero : Prop :=
  ¬ ContainsIsomorphicCopy 𝕜 X (CZero 𝕜)

end CKEUPFP
