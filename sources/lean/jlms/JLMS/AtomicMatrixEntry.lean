import JLMS.OrdinalAtomicMatrix

/-!
# Bounded coordinate functionals of the ordinal operator matrix

Every matrix coefficient depends linearly and continuously on the operator,
with norm at most one. In particular T ↦ Tκκ is an actual bounded linear
functional, as required for the codimension-one step of Ogden's argument.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]

local instance atomicEntryOperatorGroup : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] CZero 𝕜 K) := inferInstance
local instance atomicEntryOperatorSpace : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] CZero 𝕜 K) := inferInstance
local instance atomicEntryDualGroup : NormedAddCommGroup ((CZero 𝕜 K →L[𝕜] CZero 𝕜 K) →L[𝕜] 𝕜) := inferInstance

def atomicOperatorEntryCLM (M : AtomicDualModel 𝕜 K) (x y : K) :
    (CZero 𝕜 K →L[𝕜] CZero 𝕜 K) →L[𝕜] 𝕜 :=
  ({ toFun T := atomicOperatorMatrix M T x y
     map_add' S T := by
       change M.representation ((evaluation x).comp (S + T)) y = _
       rw [ContinuousLinearMap.comp_add, map_add]
       rfl
     map_smul' c T := by
       change M.representation ((evaluation x).comp (c • T)) y = _
       rw [ContinuousLinearMap.comp_smul, map_smul]
       rfl } : (CZero 𝕜 K →L[𝕜] CZero 𝕜 K) →ₗ[𝕜] 𝕜).mkContinuous 1
    (fun T => by
      change ‖atomicOperatorMatrix M T x y‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact (lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
        (atomicOperatorRow M T x) y).trans (norm_atomicOperatorRow_le M T x))

@[simp] theorem atomicOperatorEntryCLM_apply (M : AtomicDualModel 𝕜 K) (x y : K)
    (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K) :
    atomicOperatorEntryCLM M x y T = atomicOperatorMatrix M T x y := rfl

theorem norm_atomicOperatorEntryCLM_le (M : AtomicDualModel 𝕜 K) (x y : K) :
    ‖atomicOperatorEntryCLM M x y‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  rw [one_mul]
  exact (lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
    (atomicOperatorRow M T x) y).trans (norm_atomicOperatorRow_le M T x)

def ordinalZeroOperatorCLM (α : Ordinal.{u}) :
    (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →L[𝕜]
      (CZero 𝕜 (OrdinalInterval α) →L[𝕜] CZero 𝕜 (OrdinalInterval α)) := by
  let L : (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →ₗ[𝕜]
      (CZero 𝕜 (OrdinalInterval α) →L[𝕜] CZero 𝕜 (OrdinalInterval α)) :=
    { toFun := ordinalZeroOperator (𝕜 := 𝕜) α
      map_add' := (operatorConjugation (ordinalContinuousCZeroEquiv
        (𝕜 := 𝕜) α).toContinuousLinearEquiv).map_add
      map_smul' := (operatorConjugation (ordinalContinuousCZeroEquiv
        (𝕜 := 𝕜) α).toContinuousLinearEquiv).map_smul }
  exact { L with cont := continuous_operatorConjugation (ordinalContinuousCZeroEquiv (𝕜 := 𝕜) α).toContinuousLinearEquiv }

def ordinalOperatorEntryCLM (α : Ordinal.{u}) (x y : OrdinalInterval α) :
    (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →L[𝕜] 𝕜 :=
  (atomicOperatorEntryCLM (ordinalAtomicDualModel α) x y).comp (ordinalZeroOperatorCLM α)

@[simp] theorem ordinalOperatorEntryCLM_apply (α : Ordinal.{u}) (x y : OrdinalInterval α)
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    ordinalOperatorEntryCLM (𝕜 := 𝕜) α x y T = ordinalOperatorMatrix α T x y := rfl

def ordinalEndpointCoefficient (α : Ordinal.{u}) :
    (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →L[𝕜] 𝕜 :=
  ordinalOperatorEntryCLM α ⟨α, Ordinal.zero_le _, le_rfl⟩ ⟨α, Ordinal.zero_le _, le_rfl⟩

@[simp] theorem ordinalEndpointCoefficient_apply (α : Ordinal.{u})
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) :
    ordinalEndpointCoefficient (𝕜 := 𝕜) α T = ordinalOperatorMatrix α T
      ⟨α, Ordinal.zero_le _, le_rfl⟩ ⟨α, Ordinal.zero_le _, le_rfl⟩ := rfl

end JLMS
