import JLMS.AtomicOperatorMatrix
import JLMS.Rudin
import JLMS.CompactCZeroEquiv
import JLMS.OperatorConjugation
import JLMS.OrdinalSupportBounds

/-!
# The actual ordinal operator matrix in Ogden Section 3

Rudin's proved representation and the isometry C([0,α]) ≃ C₀([0,α]) provide
the rows without any additional representation hypothesis. They act on the
paper's continuous functions, have countable support, and recover the operator
norm. At uncountable cofinality, all non-endpoint entries of the endpoint row
vanish beyond one ordinal cutoff.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalAtomicDualModel (α : Ordinal.{u}) : AtomicDualModel 𝕜 (OrdinalInterval α) :=
  Classical.choice (exists_atomicDualModel (𝕜 := 𝕜) (scattered_ordinalInterval α))

def ordinalZeroOperator (α : Ordinal.{u}) (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    CZero 𝕜 (OrdinalInterval α) →L[𝕜] CZero 𝕜 (OrdinalInterval α) :=
  operatorConjugation (ordinalContinuousCZeroEquiv (𝕜 := 𝕜) α).toContinuousLinearEquiv T

def ordinalOperatorRow (α : Ordinal.{u}) (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (x : OrdinalInterval α) : ellOneOn 𝕜 (OrdinalInterval α) :=
  atomicOperatorRow (ordinalAtomicDualModel α) (ordinalZeroOperator α T) x

def ordinalOperatorMatrix (α : Ordinal.{u}) (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (x y : OrdinalInterval α) : 𝕜 := ordinalOperatorRow α T x y

theorem ordinalOperatorRow_hasSum (α : Ordinal.{u})
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (f : OrdinalC 𝕜 α) (x : OrdinalInterval α) :
    HasSum (fun y => ordinalOperatorMatrix α T x y * f y) (T f x) := by
  have h := atomicOperatorRow_hasSum (ordinalAtomicDualModel α) (ordinalZeroOperator α T)
    (ordinalContinuousCZeroEquiv (𝕜 := 𝕜) α f) x
  simpa only [ordinalOperatorMatrix, ordinalOperatorRow, atomicOperatorMatrix,
    ordinalZeroOperator, operatorConjugation_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
    compactContinuousCZeroEquiv_apply] using h

theorem ordinalOperatorRow_countable_support (α : Ordinal.{u})
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x : OrdinalInterval α) :
    (Function.support (ordinalOperatorMatrix α T x)).Countable :=
  atomicOperatorRow_countable_support (ordinalAtomicDualModel α) (ordinalZeroOperator α T) x

theorem norm_ordinalOperatorRow_le (α : Ordinal.{u})
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (x : OrdinalInterval α) :
    ‖ordinalOperatorRow α T x‖ ≤ ‖T‖ := by
  have h := norm_atomicOperatorRow_le (ordinalAtomicDualModel α) (ordinalZeroOperator α T) x
  simpa only [ordinalOperatorRow, ordinalZeroOperator, norm_operatorConjugation] using h

theorem ordinalOperatorRows_isLUB (α : Ordinal.{u})
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    IsLUB (Set.range (fun x => ‖ordinalOperatorRow α T x‖)) ‖T‖ := by
  letI : Nonempty (OrdinalInterval α) := ⟨⟨0, le_rfl, Ordinal.zero_le α⟩⟩
  have h := atomicOperatorRows_isLUB (ordinalAtomicDualModel α) (ordinalZeroOperator α T)
  simpa only [ordinalOperatorRow, ordinalZeroOperator, norm_operatorConjugation] using h

theorem exists_ordinalOperatorRow_cutoff {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α)
    (x : OrdinalInterval α) :
    ∃ β < α, ∀ y : OrdinalInterval α, β < y.val → y.val < α →
      ordinalOperatorMatrix α T x y = 0 :=
  exists_ordinal_ellOne_cutoff hα (ordinalOperatorRow α T x)

theorem exists_ordinalOperatorEndpointRows_cutoff {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    ∃ β < α, ∀ n (y : OrdinalInterval α), β < y.val → y.val < α →
      ordinalOperatorMatrix α (T n) ⟨α, Ordinal.zero_le _, le_rfl⟩ y = 0 :=
  exists_common_ordinal_ellOne_cutoff hα
    (fun n => ordinalOperatorRow α (T n) ⟨α, Ordinal.zero_le _, le_rfl⟩)

end JLMS
