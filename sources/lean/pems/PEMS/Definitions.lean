import ThesisCommon.ALSpace
import ThesisCommon.WeakCalkin
import ThesisCommon.Residuum
import PEMS.MeasureDefinitions
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.ExtremallyDisconnected

noncomputable section
open Set Topology
open scoped ZeroAtInfty
namespace PEMS
open ThesisCommon

abbrev EllOne (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) 1
abbrev EllInfinity (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) ⊤
abbrev CZero (𝕜 : Type*) [RCLike 𝕜] := C₀(ℕ, 𝕜)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def dualWeakEssentialNorm (T : E →L[𝕜] F) : ℝ := weakEssentialNorm (banachAdjoint T)

/-- The factorization supremum. Adjoining zero implements the paper's convention
that the supremum of an empty family of positive quantities is zero. -/
def factorizationSup (Z : Type*) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (T : E →L[𝕜] F) : ℝ :=
  sSup (insert 0 {r : ℝ | ∃ U : F →L[𝕜] Z, ∃ V : Z →L[𝕜] E,
    U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z ∧ r = ‖U‖⁻¹ * ‖V‖⁻¹})

/-- Minimum modulus on the unit sphere. Only used on the nontrivial space c₀. -/
def minimumModulus (T : E →L[𝕜] F) : ℝ :=
  sInf {r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = ‖T x‖}

def fixesCZeroSup (T : E →L[𝕜] F) : ℝ :=
  sSup {r : ℝ | ∃ V : CZero 𝕜 →L[𝕜] E, ‖V‖ ≤ 1 ∧ r = minimumModulus (T.comp V)}

/-- Equation (1): the De Blasi measure of a set, with arbitrary weakly compact
approximating sets D. The inequality spells out D + ε B_E, using the closed ball. -/
def deBlasiSet (A : Set E) : ℝ :=
  sInf {ε : ℝ | 0 < ε ∧ ∃ D : Set E, IsCompact (toWeakSpace 𝕜 E '' D) ∧
    ∀ x ∈ A, ∃ y ∈ D, ‖x - y‖ ≤ ε}

def deBlasiOperator (T : E →L[𝕜] F) : ℝ :=
  deBlasiSet (𝕜 := 𝕜) (T '' Metric.closedBall 0 1)

end PEMS
