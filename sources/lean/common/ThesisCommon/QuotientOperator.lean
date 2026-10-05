import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The bounded map on genuine quotient seminormed spaces induced by T. -/
def quotientOperator (p : Submodule 𝕜 E) (q : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (h : p ≤ q.comap T.toLinearMap) : (E ⧸ p) →L[𝕜] (F ⧸ q) where
  toLinearMap := p.mapQ q T.toLinearMap h
  cont := by
    apply p.isOpenQuotientMap_mkQ.continuous_comp_iff.mp
    exact continuous_quot_mk.comp T.continuous

@[simp] theorem quotientOperator_mk (p : Submodule 𝕜 E) (q : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (h : p ≤ q.comap T.toLinearMap) (x : E) :
    quotientOperator p q T h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T x) := rfl

/-- The actual operator norm of the induced quotient map, exposed separately
so consumers need not reconstruct nested quotient norm instances. -/
def quotientOperatorNorm (p : Submodule 𝕜 E) (q : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (h : p ≤ q.comap T.toLinearMap) : ℝ :=
  ‖quotientOperator p q T h‖

end ThesisCommon
