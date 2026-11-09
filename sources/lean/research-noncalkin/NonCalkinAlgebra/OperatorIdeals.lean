import SurveyStatements.P2Calkin
import SurveyStatements.P2SeparableRange
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.Mul

/-! The two actual closed operator subspaces used in arXiv:2607.15075v1.
Approximable operators are the operator-norm closure of finite-rank operators.
No approximation property of the Banach space is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra
open SurveyStatements.P2

universe u v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]

def HasFiniteRank (T : BoundedOperators X) : Prop :=
  FiniteDimensional ℂ (LinearMap.range T.toLinearMap)

def finiteRankOperators : Submodule ℂ (BoundedOperators X) where
  carrier := {T | HasFiniteRank X T}
  zero_mem' := by
    change FiniteDimensional ℂ (LinearMap.range (0 : X →ₗ[ℂ] X))
    rw [LinearMap.range_zero]
    infer_instance
  add_mem' := by
    intro S T hS hT
    letI : FiniteDimensional ℂ (LinearMap.range S.toLinearMap) := hS
    letI : FiniteDimensional ℂ (LinearMap.range T.toLinearMap) := hT
    exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le S.toLinearMap T.toLinearMap)
  smul_mem' := by
    intro a T hT
    letI : FiniteDimensional ℂ (LinearMap.range T.toLinearMap) := hT
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T.toLinearMap)
    rintro y ⟨x, rfl⟩
    exact (LinearMap.range T.toLinearMap).smul_mem a ⟨x, rfl⟩

@[simp] theorem mem_finiteRankOperators (T : BoundedOperators X) :
    T ∈ finiteRankOperators X ↔ HasFiniteRank X T := Iff.rfl

def approximableOperators : Submodule ℂ (BoundedOperators X) :=
  (finiteRankOperators X).topologicalClosure

@[simp] theorem coe_approximableOperators :
    (approximableOperators X : Set (BoundedOperators X)) =
      closure (finiteRankOperators X : Set (BoundedOperators X)) := rfl

instance approximableOperators_isClosed :
    IsClosed (approximableOperators X : Set (BoundedOperators X)) :=
  Submodule.isClosed_topologicalClosure _

theorem finiteRank_le_approximable : finiteRankOperators X ≤ approximableOperators X :=
  Submodule.le_topologicalClosure _

theorem finiteRank_isCompact {T : BoundedOperators X} (hT : HasFiniteRank X T) :
    IsCompactOperator T := by
  letI : FiniteDimensional ℂ (LinearMap.range T.toLinearMap) := hT
  letI : ProperSpace (LinearMap.range T.toLinearMap) :=
    FiniteDimensional.proper ℂ (LinearMap.range T.toLinearMap)
  let U : X →L[ℂ] (LinearMap.range T.toLinearMap) :=
    T.codRestrict (LinearMap.range T.toLinearMap) (fun x => ⟨x, rfl⟩)
  have hU : IsCompactOperator U := by
    apply (isCompactOperator_iff_image_closedBall_subset_compact U.toLinearMap zero_lt_one).mpr
    refine ⟨Metric.closedBall 0 ‖U‖, isCompact_closedBall 0 ‖U‖, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact (U.le_opNorm x).trans (by nlinarith [norm_nonneg U])
  have h := hU.continuous_comp (LinearMap.range T.toLinearMap).subtypeL.continuous
  exact h

variable [CompleteSpace X]

theorem approximable_le_compact : approximableOperators X ≤ CompactOperators X := by
  apply Submodule.topologicalClosure_minimal
  · intro T hT
    exact finiteRank_isCompact X hT
  · exact isClosed_setOf_isCompactOperator

/-- The choice is fixed across the paper, and the eventual witness works for both. -/
inductive QuotientConvention where
  | approximable
  | compact
  deriving DecidableEq, Repr

def operatorIdeal (convention : QuotientConvention) : Submodule ℂ (BoundedOperators X) :=
  match convention with
  | .approximable => approximableOperators X
  | .compact => CompactOperators X

instance operatorIdeal_isClosed (convention : QuotientConvention) :
    IsClosed (operatorIdeal X convention : Set (BoundedOperators X)) := by
  cases convention
  · exact approximableOperators_isClosed X
  · exact SurveyStatements.P2.compactOperators_isClosed X

theorem operatorIdeal_le_compact (convention : QuotientConvention) :
    operatorIdeal X convention ≤ CompactOperators X := by
  cases convention
  · exact approximable_le_compact X
  · exact le_rfl

abbrev OperatorQuotient (convention : QuotientConvention) :=
  BoundedOperators X ⧸ operatorIdeal X convention

def operatorQuotientMap (convention : QuotientConvention) :
    BoundedOperators X →ₗ[ℂ] OperatorQuotient X convention :=
  (operatorIdeal X convention).mkQ

/-- Exact Banach-algebra isomorphism condition, expressed on quotient representatives. -/
structure OperatorQuotientIso (convention : QuotientConvention) (A : Type u)
    [NormedRing A] [NormedAlgebra ℂ A] extends OperatorQuotient X convention ≃L[ℂ] A where
  map_mul_representatives : ∀ S T : BoundedOperators X,
    toContinuousLinearEquiv (operatorQuotientMap X convention (S * T)) =
      toContinuousLinearEquiv (operatorQuotientMap X convention S) *
      toContinuousLinearEquiv (operatorQuotientMap X convention T)
  map_one_representative : toContinuousLinearEquiv (operatorQuotientMap X convention 1) = 1

end NonCalkinAlgebra
