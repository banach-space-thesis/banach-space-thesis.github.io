import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-! Shared vocabulary for primariness and primary factorisation.
Sources: Acuaviva, both supplied manuscripts, Introduction and Section 2.
All maps are continuous linear maps, with their actual operator norms.
No implication from PFP to primariness is built into these definitions.
-/
noncomputable section
universe u v w z
namespace ThesisCommon

variable (𝕜 : Type u) [RCLike 𝕜]
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A projection has either its range or its complementary range isomorphic to X.
The range has the inherited norm; `≃L` means bounded linear isomorphism. -/
def IsPrimary : Prop :=
  ∀ P : X →L[𝕜] X, P.comp P = P →
    Nonempty (X ≃L[𝕜] LinearMap.range P.toLinearMap) ∨
    Nonempty (X ≃L[𝕜] LinearMap.range (ContinuousLinearMap.id 𝕜 X - P).toLinearMap)

variable {𝕜 X}
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type z} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The identity on Z factors through T with bound C: U T V = I and ‖U‖‖V‖ ≤ C.
The bound itself need not be ≥ 1; UPFP imposes that condition separately. -/
def FactorsIdentityWith (T : X →L[𝕜] Y) (Z : Type z)
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (C : ℝ) : Prop :=
  ∃ U : Y →L[𝕜] Z, ∃ V : Z →L[𝕜] X,
    (U.comp T).comp V = ContinuousLinearMap.id 𝕜 Z ∧ ‖U‖ * ‖V‖ ≤ C

/-- Unquantified factorisation, equivalent to the existence of a bound ≥ 1. -/
def FactorsIdentity (T : X →L[𝕜] Y) (Z : Type z)
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] : Prop :=
  ∃ U : Y →L[𝕜] Z, ∃ V : Z →L[𝕜] X,
    (U.comp T).comp V = ContinuousLinearMap.id 𝕜 Z

variable (𝕜 X)
/-- The primary factorisation property; the witnesses may depend on T. -/
def HasPFP : Prop :=
  ∀ T : X →L[𝕜] X,
    FactorsIdentity T X ∨ FactorsIdentity (ContinuousLinearMap.id 𝕜 X - T) X

/-- A uniform dichotomy with a specified bound. Use C ≥ 1 for the paper's C-PFP. -/
def HasCPFP (C : ℝ) : Prop :=
  ∀ T : X →L[𝕜] X,
    FactorsIdentityWith T X C ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - T) X C

/-- One constant works for all operators; it is chosen before T. -/
def HasUPFP : Prop := ∃ C : ℝ, 1 ≤ C ∧ HasCPFP 𝕜 X C

end ThesisCommon
