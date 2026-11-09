import NonCalkinAlgebra.OperatorIdeals
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u v w

/-- A complemented subspace, represented by its actual bounded inclusion
and retraction. No norm is changed on either space. -/
structure BoundedRetraction (X : Type u) (Y : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] where
  inclusion : Y →L[ℂ] X
  projection : X →L[ℂ] Y
  left_inverse : ∀ y : Y, projection (inclusion y) = y

namespace BoundedRetraction
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  (s : BoundedRetraction X Y)

def projectionOperator : BoundedOperators X := s.inclusion.comp s.projection

@[simp] theorem projectionOperator_apply (x : X) :
    s.projectionOperator x = s.inclusion (s.projection x) := rfl

theorem projectionOperator_idempotent : s.projectionOperator * s.projectionOperator =
    s.projectionOperator := by
  ext x
  exact congrArg s.inclusion (s.left_inverse (s.projection x))

def extendOperators : BoundedOperators Y →L[ℂ] BoundedOperators X :=
  (ContinuousLinearMap.compL ℂ X Y X s.inclusion).comp
    ((ContinuousLinearMap.compL ℂ X Y Y).flip s.projection)

def compressOperators : BoundedOperators X →L[ℂ] BoundedOperators Y :=
  (ContinuousLinearMap.compL ℂ Y X Y s.projection).comp
    ((ContinuousLinearMap.compL ℂ Y X X).flip s.inclusion)

@[simp] theorem extendOperators_apply (T : BoundedOperators Y) (x : X) :
    s.extendOperators T x = s.inclusion (T (s.projection x)) := rfl

@[simp] theorem compressOperators_apply (T : BoundedOperators X) (y : Y) :
    s.compressOperators T y = s.projection (T (s.inclusion y)) := rfl

theorem compress_extend (T : BoundedOperators Y) :
    s.compressOperators (s.extendOperators T) = T := by
  ext y
  simp only [compressOperators_apply, extendOperators_apply, s.left_inverse]

theorem extend_compress (T : BoundedOperators X) :
    s.extendOperators (s.compressOperators T) = s.projectionOperator * T * s.projectionOperator := by
  ext x
  rfl

theorem extendOperators_mul (S T : BoundedOperators Y) :
    s.extendOperators (S * T) = s.extendOperators S * s.extendOperators T := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, extendOperators_apply, s.left_inverse]

theorem extendOperators_one : s.extendOperators 1 = s.projectionOperator := by
  ext x
  rfl

theorem extendOperators_injective : Function.Injective s.extendOperators :=
  Function.LeftInverse.injective s.compress_extend

end BoundedRetraction

section FiniteRankComposition
variable {X : Type u} {Y : Type v} {Z : Type w}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem finiteDimensional_range_comp_left (S : Y →L[ℂ] Z) (T : X →L[ℂ] Y)
    (hT : FiniteDimensional ℂ (LinearMap.range T.toLinearMap)) :
    FiniteDimensional ℂ (LinearMap.range (S.comp T).toLinearMap) := by
  letI : FiniteDimensional ℂ (LinearMap.range T.toLinearMap) := hT
  let f : (LinearMap.range T.toLinearMap) →ₗ[ℂ] Z :=
    S.toLinearMap.comp (LinearMap.range T.toLinearMap).subtype
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f)
  rintro z ⟨x, rfl⟩
  exact ⟨⟨T x, ⟨x, rfl⟩⟩, rfl⟩

theorem finiteDimensional_range_comp_right (S : Y →L[ℂ] Z) (T : X →L[ℂ] Y)
    (hS : FiniteDimensional ℂ (LinearMap.range S.toLinearMap)) :
    FiniteDimensional ℂ (LinearMap.range (S.comp T).toLinearMap) := by
  letI : FiniteDimensional ℂ (LinearMap.range S.toLinearMap) := hS
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range S.toLinearMap)
  rintro z ⟨x, rfl⟩
  exact ⟨T x, rfl⟩

end FiniteRankComposition
end NonCalkinAlgebra
