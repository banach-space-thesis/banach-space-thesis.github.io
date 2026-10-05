import Posets.OrdinalIdealTransportMatrixCompression
import Posets.OrdinalIdealTransportJumpAlgebra
import Posets.CZeroContinuousAmplification

/-! Exact diagonal compression when the off-diagonal endpoint jumps vanish.
All maps act on the genuine Banach c₀ sum. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 1000000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

local instance matrixScalarSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance matrixScalarSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

theorem exists_initialOrdinal_scalar_matrix_compression
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : c.ord.toType → c.ord.toType → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hoff : ∀ i j, i ≠ j → initialEndpointJump (𝕜 := 𝕜) hc hu (T i j) = 0) :
    ∃ L R : c.ord.toType → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      (∀ i, (L i).comp (R i) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ i, ‖L i‖ ≤ 4) ∧ (∀ i, ‖R i‖ ≤ 2) ∧
      ∀ i j x, L i (T i j (R j x)) = if i = j then initialEndpointJump (𝕜 := 𝕜) hc hu (T i i) • x else 0 := by
  classical
  let a (i j : c.ord.toType) := initialEndpointJump (𝕜 := 𝕜) hc hu (T i j)
  let U (i j : c.ord.toType) := T i j - a i j • ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)
  have hU (i j) : U i j ∈ loyWillisSubspace hc hu := sub_jump_smul_id_mem_loyWillisSubspace hc hu (T i j)
  let f (i j : c.ord.toType) := loyWillisEndpointColumn hc hu (U i j) (hU i j)
  let S (i j : c.ord.toType) := U i j - ordinalEndpointRankOne c.ord (f i j)
  have hS (i j) : S i j ∈ loyWillisZeroEndpointSubspace hc hu := by
    refine ⟨loyWillis_sub_endpointRankOne_mem hc hu (U i j) (hU i j), ?_⟩
    change ordinalOperatorMatrix c.ord (S i j) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0
    exact loyWillis_sub_endpointRankOne_zero_column hc hu (U i j) (hU i j) _
  obtain ⟨L, R, hLR, hLSR, htop, hL, hR⟩ := exists_loyWillis_regular_matrix_compression hc hu S hS
  refine ⟨L, R, hLR, hL, hR, ?_⟩
  intro i j x
  have hSR : S i j (R j x) = T i j (R j x) - a i j • R j x := by
    ext y
    change (T i j (R j x) y - a i j * R j x y) -
      R j x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ * f i j y = _
    rw [htop, zero_mul, sub_zero]
    rfl
  have hz := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) (hLSR i j)
  change L i (S i j (R j x)) = 0 at hz
  rw [hSR, map_sub, map_smul] at hz
  rw [sub_eq_zero] at hz
  rw [hz]
  by_cases hij : i = j
  · subst j
    have hid := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) (hLR i)
    change L i (R i x) = x at hid
    simp only [ite_true, hid, a]
  · simp only [if_neg hij, show a i j = 0 from hoff i j hij, zero_smul]

theorem exists_regularOrdinalSum_diagonal_compression
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord))
    (hoff : ∀ i j, i ≠ j → regularOrdinalBlockJump hc hu T i j = 0) :
    ∃ L R : CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord) →L[𝕜]
        CZeroSum 𝕜 (fun _ : c.ord.toType => OrdinalC 𝕜 c.ord),
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 ∧
      ∀ x i, L (T (R x)) i = regularOrdinalBlockJump hc hu T i i • x i := by
  classical
  obtain ⟨l, r, hlr, hl, hr, hscalar⟩ :=
    exists_initialOrdinal_scalar_matrix_compression hc hu (regularOrdinalBlock T) hoff
  let L := CZeroSum.mapCLM l (by norm_num : (0:ℝ) ≤ 4) hl
  let R := CZeroSum.mapCLM r (by norm_num : (0:ℝ) ≤ 2) hr
  refine ⟨L, R, ?_, CZeroSum.norm_mapCLM_le _ _ _, CZeroSum.norm_mapCLM_le _ _ _, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply CZeroSum.ext
    intro i
    exact congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V (x i)) (hlr i)
  · intro x i
    have heq : (CZeroSum.evalCLM i).comp (L.comp (T.comp R)) =
        (regularOrdinalBlockJump hc hu T i i) • CZeroSum.evalCLM (𝕜 := 𝕜)
          (E := fun _ : c.ord.toType => OrdinalC 𝕜 c.ord) i := by
      apply cZeroSum_clm_ext_columns
      intro j f
      change l i (T (R (CZeroSum.single j f)) i) = _
      rw [cZeroSum_mapCLM_single]
      change l i (regularOrdinalBlock T i j (r j f)) = _
      rw [hscalar]
      by_cases hij : i = j
      · subst j
        simp only [ite_true, ContinuousLinearMap.smul_apply, CZeroSum.evalCLM_apply,
          CZeroSum.single_apply_self]
        rfl
      · simp only [if_neg hij, ContinuousLinearMap.smul_apply, CZeroSum.evalCLM_apply,
          CZeroSum.single_apply_ne _ _ hij, smul_zero]
    exact congrArg (fun V => V x) heq

end Posets
