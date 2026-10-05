import JLMS.OrdinalAtomicMatrix

/-!
# Matrix coordinates of rank-one evaluation operators

The operator g ↦ g(y)f has only its y-column nonzero, and that column is f.
The ordinal version is stated on the actual C([0,α]) space. These formulas
will identify the special operators used to generate the missing scalar
direction in the Loy--Willis ideal.
-/

noncomputable section
attribute [local instance] Classical.decEq
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]

theorem atomicOperatorRow_rankOne (M : AtomicDualModel 𝕜 K)
    (f : CZero 𝕜 K) (x y : K) :
    atomicOperatorRow M ((evaluation y).smulRight f) x =
      f x • (lp.single 1 y (1 : 𝕜) : ellOneOn 𝕜 K) := by
  have he : (evaluation x).comp ((evaluation y).smulRight f) = f x • evaluation y := by
    ext g
    change g y * f x = f x * g y
    exact mul_comm _ _
  change M.representation ((evaluation x).comp ((evaluation y).smulRight f)) = _
  rw [he, map_smul]
  have hy : M.representation (evaluation y) = lp.single 1 y (1 : 𝕜) := by
    rw [← M.pointMass y]
    exact M.representation.apply_symm_apply _
  rw [hy]

theorem atomicOperatorMatrix_rankOne (M : AtomicDualModel 𝕜 K)
    (f : CZero 𝕜 K) (x y z : K) :
    atomicOperatorMatrix M ((evaluation y).smulRight f) x z =
      if z = y then f x else 0 := by
  rw [atomicOperatorMatrix, atomicOperatorRow_rankOne]
  by_cases h : z = y <;> simp [h, lp.coeFn_smul, lp.coeFn_single]

theorem ordinalZeroOperator_rankOne (α : Ordinal.{u}) (f : OrdinalC 𝕜 α)
    (y : OrdinalInterval α) :
    ordinalZeroOperator α ((ContinuousMap.evalCLM (R := 𝕜) y).smulRight f) =
      (evaluation y).smulRight (ordinalContinuousCZeroEquiv (𝕜 := 𝕜) α f) := by
  ext g x
  rfl

theorem ordinalOperatorMatrix_rankOne (α : Ordinal.{u}) (f : OrdinalC 𝕜 α)
    (x y z : OrdinalInterval α) :
    ordinalOperatorMatrix α ((ContinuousMap.evalCLM (R := 𝕜) y).smulRight f) x z =
      if z = y then f x else 0 := by
  change atomicOperatorMatrix (ordinalAtomicDualModel α)
    (ordinalZeroOperator α ((ContinuousMap.evalCLM (R := 𝕜) y).smulRight f)) x z = _
  rw [ordinalZeroOperator_rankOne, atomicOperatorMatrix_rankOne]
  by_cases hz : z = y
  · simp only [if_pos hz]
    rfl
  · simp only [if_neg hz]

end JLMS
