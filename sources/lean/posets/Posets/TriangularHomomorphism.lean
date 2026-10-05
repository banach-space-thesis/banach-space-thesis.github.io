import Posets.BipartiteOperatorProduct
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The triangular matrix homomorphism carried by the bipartite incidence algebra. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def triangularLinearMap {A : Type*} [AddCommGroup A] [Module 𝕜 A]
    (a b c : A →ₗ[𝕜] 𝕜) : A →ₗ[𝕜] Matrix (Fin 2) (Fin 2) 𝕜 where
  toFun T := !![a T, b T; 0, c T]
  map_add' := by intro T S; ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' := by intro z T; ext i j; fin_cases i <;> fin_cases j <;> simp

@[simp] theorem triangularLinearMap_zero_zero {A : Type*} [AddCommGroup A] [Module 𝕜 A]
    (a b c : A →ₗ[𝕜] 𝕜) (T : A) : triangularLinearMap a b c T 0 0 = a T := rfl
@[simp] theorem triangularLinearMap_zero_one {A : Type*} [AddCommGroup A] [Module 𝕜 A]
    (a b c : A →ₗ[𝕜] 𝕜) (T : A) : triangularLinearMap a b c T 0 1 = b T := rfl
@[simp] theorem triangularLinearMap_one_zero {A : Type*} [AddCommGroup A] [Module 𝕜 A]
    (a b c : A →ₗ[𝕜] 𝕜) (T : A) : triangularLinearMap a b c T 1 0 = 0 := rfl
@[simp] theorem triangularLinearMap_one_one {A : Type*} [AddCommGroup A] [Module 𝕜 A]
    (a b c : A →ₗ[𝕜] 𝕜) (T : A) : triangularLinearMap a b c T 1 1 = c T := rfl

theorem triangularLinearMap_multiplicative {A : Type*} [AddCommGroup A] [Module 𝕜 A] [Mul A]
    (a b c : A →ₗ[𝕜] 𝕜) (ha : ∀ T S, a (T*S) = a T * a S)
    (hc : ∀ T S, c (T*S) = c T * c S)
    (hb : ∀ T S, b (T*S) = a T * b S + b T * c S) :
    IsMultiplicative 𝕜 (triangularLinearMap a b c) := by
  intro T S
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc]

variable {P Q : Type*}

def bipartiteTriangularMap (U : Ultrafilter P) (V : Ultrafilter Q)
    (L : (CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) →ₗ[𝕜] 𝕜) :
    BipartiteAlgebra 𝕜 P Q →ₗ[𝕜] Matrix (Fin 2) (Fin 2) 𝕜 :=
  triangularLinearMap
    ((ultrafilterEvaluation (𝕜 := 𝕜) U).toLinearMap.comp bipartiteLeftDiagonalMap)
    (L.comp bipartiteUpperBlockMap)
    ((ultrafilterEvaluation (𝕜 := 𝕜) V).toLinearMap.comp bipartiteRightDiagonalMap)

theorem bipartiteTriangularMap_multiplicative (U : Ultrafilter P) (V : Ultrafilter Q)
    (L : (CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) →ₗ[𝕜] 𝕜)
    (hleft : ∀ a T, L ((multiplicationOperator a).comp T) =
      ultrafilterEvaluation U a * L T)
    (hright : ∀ b T, L (T.comp (multiplicationOperator b)) =
      L T * ultrafilterEvaluation V b) :
    IsMultiplicative 𝕜 (bipartiteTriangularMap U V L) := by
  apply triangularLinearMap_multiplicative
  · intro T S
    change ultrafilterEvaluation U (bipartiteLeftDiagonal (T*S)) = _
    rw [bipartiteLeftDiagonal_mul, ultrafilterEvaluation_mul]
    rfl
  · intro T S
    change ultrafilterEvaluation V (bipartiteRightDiagonal (T*S)) = _
    rw [bipartiteRightDiagonal_mul, ultrafilterEvaluation_mul]
    rfl
  · intro T S
    change L (bipartiteUpperBlock (T*S)) = _
    rw [bipartiteUpperBlock_mul, map_add, hleft, hright]
    rfl

theorem bipartiteTriangularMap_range_subset (U : Ultrafilter P) (V : Ultrafilter Q)
    (L : (CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) →ₗ[𝕜] 𝕜) :
    Set.range (bipartiteTriangularMap U V L) ⊆ triangularTwo 𝕜 := by
  rintro _ ⟨T, rfl⟩
  rfl

end Posets


