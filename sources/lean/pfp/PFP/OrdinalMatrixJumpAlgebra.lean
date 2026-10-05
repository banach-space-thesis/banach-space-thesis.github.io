import PFP.OrdinalMatrixJumpOperator
import Posets.CZeroContinuousAmplification

/-! The actual endpoint-jump operator respects subtraction and the identity,
so its two scalar diagonal colours correspond to T and I − T. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS
universe u
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

local instance jumpAlgebraSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance jumpAlgebraSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

@[simp] theorem regularOrdinalBlock_sub {c : Cardinal.{ordU}} {I : Type u}
    (T S : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) (i j : I) :
    regularOrdinalBlock (T - S) i j = regularOrdinalBlock T i j - regularOrdinalBlock S i j := by
  apply ContinuousLinearMap.ext
  intro f
  rfl

@[simp] theorem regularOrdinalBlockJump_sub
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T S : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) (i j : I) :
    regularOrdinalBlockJump hc hu (T - S) i j =
      regularOrdinalBlockJump hc hu T i j - regularOrdinalBlockJump hc hu S i j := by
  simp only [regularOrdinalBlockJump, regularOrdinalBlock_sub, map_sub]

@[simp] theorem regularOrdinalJumpOperator_sub
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T S : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) :
    regularOrdinalJumpOperator hc hu (T - S) =
      regularOrdinalJumpOperator hc hu T - regularOrdinalJumpOperator hc hu S := by
  apply cZeroSum_clm_ext_columns
  intro j z
  rw [cZeroScalarSingle_smul j z, map_smul, map_smul]
  congr 1
  apply CZeroSum.ext
  intro i
  simp only [ContinuousLinearMap.sub_apply, CZeroSum.sub_apply,
    regularOrdinalJumpOperator_single, regularOrdinalBlockJump_sub]

@[simp] theorem regularOrdinalJumpOperator_id
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u} :
    regularOrdinalJumpOperator hc hu
      (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord))) =
      ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜 (fun _ : I => 𝕜)) := by
  classical
  apply cZeroSum_clm_ext_columns
  intro j z
  rw [cZeroScalarSingle_smul j z, map_smul, map_smul]
  congr 1
  apply CZeroSum.ext
  intro i
  rw [regularOrdinalJumpOperator_single]
  change initialEndpointJump (𝕜 := 𝕜) hc hu (regularOrdinalBlock _ i j) =
    CZeroSum.single (𝕜 := 𝕜) (E := fun _ : I => 𝕜) j 1 i
  by_cases hij : i = j
  · subst i
    have he : regularOrdinalBlock
        (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord))) j j =
        ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord) := by
      apply ContinuousLinearMap.ext
      intro f
      exact CZeroSum.single_apply_self (𝕜 := 𝕜) (E := fun _ : I => OrdinalC 𝕜 c.ord) j f
    rw [he, initialEndpointJump_id, CZeroSum.single_apply_self]
  · have he : regularOrdinalBlock
        (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord))) i j = 0 := by
      apply ContinuousLinearMap.ext
      intro f
      exact CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := fun _ : I => OrdinalC 𝕜 c.ord) j f hij
    rw [he, map_zero, CZeroSum.single_apply_ne j 1 hij]

end Posets.UniverseRegularMatrix


