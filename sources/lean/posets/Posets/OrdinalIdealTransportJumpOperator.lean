import Posets.OrdinalIdealTransportJumpColumns
import Posets.CZeroContinuousAmplificationColumns

/-! The matrix of endpoint jumps defines a bounded scalar c₀ operator for
arbitrarily many repeated regular ordinal blocks. -/
noncomputable section
namespace Posets
open JLMS
universe u
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

local instance jumpOperatorSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance jumpOperatorSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

theorem regularOrdinalJumpColumns_bound
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) :
    CZeroSumFiniteColumnBound
      (fun j => (ContinuousLinearMap.id 𝕜 𝕜).smulRight (regularOrdinalJumpColumn hc hu T j))
      (2 * ‖T‖) := by
  classical
  intro x s M hM hx
  apply CZeroSum.norm_le (by positivity)
  intro i
  let J : OrdinalC 𝕜 c.ord →L[𝕜] CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) :=
    ∑ j ∈ s, x j • (CZeroSum.singleIsometry (𝕜 := 𝕜) (E := fun _ : I => OrdinalC 𝕜 c.ord) j).toContinuousLinearMap
  have hJf (f : OrdinalC 𝕜 c.ord) : ‖J f‖ ≤ M * ‖f‖ := by
    apply CZeroSum.norm_le (mul_nonneg hM (norm_nonneg f))
    intro j
    simp only [J, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      LinearIsometry.coe_toContinuousLinearMap, CZeroSum.sum_apply, CZeroSum.smul_apply,
      CZeroSum.singleIsometry_apply]
    by_cases hj : j ∈ s
    · rw [Finset.sum_eq_single j]
      · rw [CZeroSum.single_apply_self, norm_smul]
        exact mul_le_mul_of_nonneg_right (hx j hj) (norm_nonneg f)
      · intro k hk hkj
        rw [CZeroSum.single_apply_ne _ _ hkj.symm, smul_zero]
      · exact fun h => (h hj).elim
    · rw [Finset.sum_eq_zero (fun k hk => by
        rw [CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := fun _ : I => OrdinalC 𝕜 c.ord) k f (fun he : j = k => hj (he.symm ▸ hk)), smul_zero]), norm_zero]
      positivity
  let V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    ∑ j ∈ s, x j • regularOrdinalBlock T i j
  have hVf (f : OrdinalC 𝕜 c.ord) : V f = T (J f) i := by
    simp only [V, J, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, CZeroSum.sum_apply, CZeroSum.smul_apply]
    rfl
  have hV : ‖V‖ ≤ ‖T‖ * M := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg T) hM)
    intro f
    rw [hVf]
    exact (T (J f)).norm_apply_le_norm i |>.trans ((T.le_opNorm _).trans
      (by calc
        ‖T‖ * ‖J f‖ ≤ ‖T‖ * (M * ‖f‖) := mul_le_mul_of_nonneg_left (hJf f) (norm_nonneg T)
        _ = (‖T‖ * M) * ‖f‖ := (mul_assoc _ _ _).symm))
  have he : (∑ j ∈ s, (ContinuousLinearMap.id 𝕜 𝕜).smulRight
      (regularOrdinalJumpColumn hc hu T j) (x j)) i = initialEndpointJump (𝕜 := 𝕜) hc hu V := by
    simp only [V, map_sum, map_smul, CZeroSum.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      CZeroSum.smul_apply, regularOrdinalJumpColumn_apply, regularOrdinalBlockJump]
  rw [he]
  calc
    ‖initialEndpointJump (𝕜 := 𝕜) hc hu V‖ ≤ ‖initialEndpointJump (𝕜 := 𝕜) hc hu‖ * ‖V‖ :=
      (initialEndpointJump (𝕜 := 𝕜) hc hu).le_opNorm V
    _ ≤ 2 * (‖T‖ * M) := mul_le_mul (norm_initialEndpointJump_le hc hu) hV
      (norm_nonneg V) (by norm_num)
    _ = (2 * ‖T‖) * M := (mul_assoc _ _ _).symm

def regularOrdinalJumpOperator
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) :
    CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] CZeroSum 𝕜 (fun _ : I => 𝕜) :=
  cZeroSumColumns
    (fun j => (ContinuousLinearMap.id 𝕜 𝕜).smulRight (regularOrdinalJumpColumn hc hu T j))
    (2 * ‖T‖) (by positivity) (regularOrdinalJumpColumns_bound hc hu T)

@[simp] theorem regularOrdinalJumpOperator_single
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) (i j : I) :
    regularOrdinalJumpOperator hc hu T (CZeroSum.single j 1) i =
      regularOrdinalBlockJump hc hu T i j := by
  unfold regularOrdinalJumpOperator
  rw [cZeroSumColumns_single]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    one_smul, regularOrdinalJumpColumn_apply]

theorem norm_regularOrdinalJumpOperator_le
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) :
    ‖regularOrdinalJumpOperator hc hu T‖ ≤ 2 * ‖T‖ := norm_cZeroSumColumns_le ..

end Posets
