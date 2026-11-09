import NonCalkinAlgebra.RetractionCalkinCorner
import Mathlib.Topology.Algebra.Algebra.Equiv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u v
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- A bounded linear equivalence is a retraction whose complementary
projection is the identity. -/
def equivRetraction (e : X ≃L[ℂ] Y) : BoundedRetraction Y X where
  inclusion := e.toContinuousLinearMap
  projection := e.symm.toContinuousLinearMap
  left_inverse := e.symm_apply_apply

omit [CompleteSpace X] [CompleteSpace Y] in
theorem equivRetraction_projection (e : X ≃L[ℂ] Y) :
    (equivRetraction e).projectionOperator = 1 := by
  ext y
  exact e.apply_symm_apply y

def calkinCongruenceLinear (e : X ≃L[ℂ] Y) (k : QuotientConvention) :
    OperatorQuotient X k ≃L[ℂ] OperatorQuotient Y k where
  toFun := (equivRetraction e).extendQuotient k
  invFun := (equivRetraction e).compressQuotient k
  map_add' := ((equivRetraction e).extendQuotient k).map_add
  map_smul' := ((equivRetraction e).extendQuotient k).map_smul
  left_inv := (equivRetraction e).compress_extend_quotient k
  right_inv := by
    intro a
    rw [(equivRetraction e).extend_compress_quotient, equivRetraction_projection,
      operatorQuotientMap_one, one_mul, mul_one]
  continuous_toFun := ((equivRetraction e).extendQuotient k).continuous
  continuous_invFun := ((equivRetraction e).compressQuotient k).continuous

/-- Conjugation by an actual bounded linear equivalence preserves both
operator ideals and gives a bounded algebra equivalence of their quotients.
The Banach spaces may live in different universes. -/
def calkinCongruence (e : X ≃L[ℂ] Y) (k : QuotientConvention) :
    OperatorQuotient X k ≃A[ℂ] OperatorQuotient Y k where
  toAlgEquiv := AlgEquiv.ofLinearEquiv (calkinCongruenceLinear e k).toLinearEquiv
    (by
      change (equivRetraction e).extendQuotient k 1 = 1
      rw [(equivRetraction e).extendQuotient_one, equivRetraction_projection,
        operatorQuotientMap_one])
    ((equivRetraction e).extendQuotient_mul k)
  continuous_toFun := (calkinCongruenceLinear e k).continuous
  continuous_invFun := (calkinCongruenceLinear e k).symm.continuous

end NonCalkinAlgebra
