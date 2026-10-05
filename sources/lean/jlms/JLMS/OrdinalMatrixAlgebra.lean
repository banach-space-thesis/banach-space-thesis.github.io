import JLMS.AtomicMatrixEntry

/-!
# Algebraic operations on the actual ordinal operator matrix

Ogden's matrix multiplication formula (Lemma 3.5) is obtained by applying
a bounded coordinate functional to the ℓ¹-valued row composition formula.
Identity, addition and scalar multiplication use the same Rudin coordinates.
-/

noncomputable section
attribute [local instance] Classical.decEq
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Evaluation of one coordinate of an absolutely summable family. -/
def ellOneCoordinate {I : Type*} (i : I) : ellOneOn 𝕜 I →L[𝕜] 𝕜 :=
  ({ toFun a := a i
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : ellOneOn 𝕜 I →ₗ[𝕜] 𝕜).mkContinuous 1
    (fun a => by
      simpa only [one_mul] using
        lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) a i)

@[simp] theorem ellOneCoordinate_apply {I : Type*} (i : I) (a : ellOneOn 𝕜 I) :
    ellOneCoordinate i a = a i := rfl

theorem atomicOperatorMatrix_comp_hasSum {K : Type*} [TopologicalSpace K]
    (M : AtomicDualModel 𝕜 K) (S T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K) (x z : K) :
    HasSum (fun y => atomicOperatorMatrix M S x y * atomicOperatorMatrix M T y z)
      (atomicOperatorMatrix M (S.comp T) x z) := by
  have h := (atomicOperatorRow_comp_hasSum M S T x).map
    (ellOneCoordinate (𝕜 := 𝕜) z) (ellOneCoordinate (𝕜 := 𝕜) z).continuous
  simpa only [map_smul, ellOneCoordinate_apply, smul_eq_mul, atomicOperatorMatrix] using h

@[simp] theorem ordinalZeroOperator_comp (α : Ordinal.{u})
    (S T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    ordinalZeroOperator α (S.comp T) = (ordinalZeroOperator α S).comp
      (ordinalZeroOperator α T) :=
  (operatorConjugation (ordinalContinuousCZeroEquiv (𝕜 := 𝕜) α).toContinuousLinearEquiv).map_mul S T

@[simp] theorem ordinalZeroOperator_id (α : Ordinal.{u}) :
    ordinalZeroOperator α (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α)) =
      ContinuousLinearMap.id 𝕜 (CZero 𝕜 (OrdinalInterval α)) := by
  ext f x
  simp [ordinalZeroOperator]

/-- Ogden Lemma 3.5, with the infinite matrix product stated as a convergent series. -/
theorem ordinalOperatorMatrix_comp_hasSum (α : Ordinal.{u})
    (S T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x z : OrdinalInterval α) :
    HasSum (fun y => ordinalOperatorMatrix α S x y * ordinalOperatorMatrix α T y z)
      (ordinalOperatorMatrix α (S.comp T) x z) := by
  simpa only [ordinalOperatorMatrix, ordinalOperatorRow, ← ordinalZeroOperator_comp,
    atomicOperatorMatrix] using
    atomicOperatorMatrix_comp_hasSum (ordinalAtomicDualModel α)
      (ordinalZeroOperator α S) (ordinalZeroOperator α T) x z

/-- A continuous column of the right factor is carried to its image by the left factor. -/
theorem ordinalOperatorMatrix_comp_column (α : Ordinal.{u})
    (S T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (z : OrdinalInterval α)
    (f : OrdinalC 𝕜 α) (hf : ∀ y, ordinalOperatorMatrix α T y z = f y)
    (x : OrdinalInterval α) :
    ordinalOperatorMatrix α (S.comp T) x z = S f x := by
  apply (ordinalOperatorMatrix_comp_hasSum α S T x z).unique
  simpa only [hf] using ordinalOperatorRow_hasSum α S f x

@[simp] theorem ordinalOperatorRow_id (α : Ordinal.{u}) (x : OrdinalInterval α) :
    ordinalOperatorRow α (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α)) x =
      lp.single 1 x (1 : 𝕜) := by
  rw [ordinalOperatorRow, ordinalZeroOperator_id, atomicOperatorRow_id]
  ext y
  simp [lp.single_apply, Pi.single_apply]

@[simp] theorem ordinalOperatorMatrix_id (α : Ordinal.{u}) (x y : OrdinalInterval α) :
    ordinalOperatorMatrix α (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 α)) x y =
      if x = y then 1 else 0 := by
  classical
  simp [ordinalOperatorMatrix, ordinalOperatorRow_id, lp.single_apply, Pi.single_apply,
    eq_comm]

@[simp] theorem ordinalOperatorMatrix_add (α : Ordinal.{u})
    (S T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x y : OrdinalInterval α) :
    ordinalOperatorMatrix α (S + T) x y =
      ordinalOperatorMatrix α S x y + ordinalOperatorMatrix α T x y :=
  (ordinalOperatorEntryCLM (𝕜 := 𝕜) α x y).map_add S T

@[simp] theorem ordinalOperatorMatrix_smul (α : Ordinal.{u})
    (a : 𝕜) (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x y : OrdinalInterval α) :
    ordinalOperatorMatrix α (a • T) x y = a * ordinalOperatorMatrix α T x y :=
  (ordinalOperatorEntryCLM (𝕜 := 𝕜) α x y).map_smul a T

@[simp] theorem ordinalOperatorMatrix_sub (α : Ordinal.{u})
    (S T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x y : OrdinalInterval α) :
    ordinalOperatorMatrix α (S - T) x y =
      ordinalOperatorMatrix α S x y - ordinalOperatorMatrix α T x y :=
  (ordinalOperatorEntryCLM (𝕜 := 𝕜) α x y).map_sub S T

@[simp] theorem ordinalOperatorMatrix_zero (α : Ordinal.{u}) (x y : OrdinalInterval α) :
    ordinalOperatorMatrix α (0 : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) x y = 0 :=
  (ordinalOperatorEntryCLM (𝕜 := 𝕜) α x y).map_zero

end JLMS
