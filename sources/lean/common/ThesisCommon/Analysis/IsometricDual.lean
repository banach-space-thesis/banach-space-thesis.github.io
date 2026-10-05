import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.StrongTopology

noncomputable section
namespace ThesisCommon

/-- Transport bounded functionals through a linear isometry equivalence.
The operator norm is preserved, not merely equivalent. -/
def dualIsometryEquiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) :
    (E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (F →L[ℝ] ℝ) := by
  let d := e.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  refine { d.toLinearEquiv with norm_map' := ?_ }
  intro f
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro x
    change ‖f (e.symm x)‖ ≤ ‖f‖ * ‖x‖
    simpa using f.le_opNorm (e.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (d f))
    intro x
    have h := (d f).le_opNorm (e x)
    change ‖f (e.symm (e x))‖ ≤ ‖d f‖ * ‖e x‖ at h
    simpa using h

@[simp] theorem dualIsometryEquiv_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) (f : E →L[ℝ] ℝ) (x : F) :
    dualIsometryEquiv e f x = f (e.symm x) := rfl

end ThesisCommon
