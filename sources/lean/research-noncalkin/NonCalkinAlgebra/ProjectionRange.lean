import NonCalkinAlgebra.BoundedRetraction
import Mathlib.Analysis.Normed.Module.Complemented

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2 Set TopologicalSpace
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X]

structure BoundedProjection where
  operator : BoundedOperators X
  idempotent : operator * operator = operator

namespace BoundedProjection
variable {X} (P : BoundedProjection X)

def range : Submodule ℂ X := LinearMap.range P.operator.toLinearMap

instance range_isClosed : IsClosed (P.range : Set X) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range P.idempotent

instance range_completeSpace [CompleteSpace X] : CompleteSpace P.range :=
  P.range_isClosed.completeSpace_coe

def rangeRetraction : BoundedRetraction X P.range where
  inclusion := P.range.subtypeL
  projection := P.operator.codRestrict P.range (fun x => ⟨x, rfl⟩)
  left_inverse y := by
    apply Subtype.ext
    obtain ⟨x, hx⟩ := y.property
    change P.operator y.val = y.val
    rw [← hx]
    exact congrArg (fun T : BoundedOperators X => T x) P.idempotent

@[simp] theorem rangeRetraction_projectionOperator :
    P.rangeRetraction.projectionOperator = P.operator := by
  ext x
  rfl

theorem range_closedComplemented : P.range.ClosedComplemented :=
  ⟨P.rangeRetraction.projection, P.rangeRetraction.left_inverse⟩

theorem range_separable_of_separableRange (hP : IsSeparable (Set.range P.operator)) :
    SeparableSpace P.range := by
  exact hP.separableSpace

instance range_separableSpace [SeparableSpace X] : SeparableSpace P.range :=
  P.range_separable_of_separableRange
    ((isSeparable_univ_iff.mpr (inferInstance : SeparableSpace X)).mono (Set.subset_univ _))

end BoundedProjection
end NonCalkinAlgebra
