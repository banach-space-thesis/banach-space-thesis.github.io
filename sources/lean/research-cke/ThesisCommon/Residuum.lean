import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic
import ThesisCommon.QuotientOperator

noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 400000
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- Supplying the ambient types prevents higher-order instance inference from
-- losing the norm topology while reconstructing a doubly nested dual.
local instance : HasQuotient (StrongDual 𝕜 (StrongDual 𝕜 E))
    (Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :=
  @Submodule.hasQuotient 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))
    inferInstance inferInstance inferInstance

/-- The linear Banach adjoint (also complex-linear), by precomposition. -/
def banachAdjoint (T : E →L[𝕜] F) : (F →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T

def bidualMap (T : E →L[𝕜] F) :
    StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F) :=
  banachAdjoint (banachAdjoint T)

/-- The canonical image of E in E**. -/
def bidualImage (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  LinearMap.range (NormedSpace.inclusionInDoubleDual 𝕜 E)

/-- E** / J_E(E), with the genuine quotient seminorm (a norm for complete E). -/
abbrev ResiduumSpace (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  (StrongDual 𝕜 (StrongDual 𝕜 E)) ⧸ bidualImage 𝕜 E

theorem bidual_preserves_image (T : E →L[𝕜] F) :
    bidualImage 𝕜 E ≤ (bidualImage 𝕜 F).comap (bidualMap T).toLinearMap := by
  rintro x ⟨y, rfl⟩
  exact ⟨T y, by ext φ; rfl⟩

/-- The actual bounded residuum map [x] ↦ [T**x]. The source is E**, correcting
the printed F** typo after equation (1) in the introduction. -/
def residuumOperator (T : E →L[𝕜] F) :=
  quotientOperator (𝕜 := 𝕜)
    (E := StrongDual 𝕜 (StrongDual 𝕜 E)) (F := StrongDual 𝕜 (StrongDual 𝕜 F))
    (bidualImage 𝕜 E) (bidualImage 𝕜 F)
    (bidualMap T) (bidual_preserves_image T)

@[simp] theorem residuumOperator_mk (T : E →L[𝕜] F) (x : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    residuumOperator T (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (bidualMap T x) := rfl

/-- The operator norm of the actual residuum map on the quotient seminorms. -/
def residuumNorm (T : E →L[𝕜] F) : ℝ :=
  quotientOperatorNorm (𝕜 := 𝕜)
    (E := StrongDual 𝕜 (StrongDual 𝕜 E)) (F := StrongDual 𝕜 (StrongDual 𝕜 F))
    (bidualImage 𝕜 E) (bidualImage 𝕜 F) (bidualMap T) (bidual_preserves_image T)

end ThesisCommon
