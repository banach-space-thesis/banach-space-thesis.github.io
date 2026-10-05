import Posets.OrdinalIdealTransportRepeatedBlocks
import Posets.CZeroContinuousAmplificationSynthesis

/-! Endpoint jumps of arbitrary repeated-ordinal operator matrices have
vanishing scalar columns. Only countable simultaneous compression is used. -/
noncomputable section
namespace Posets
open JLMS Filter Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

local instance jumpColumnSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance jumpColumnSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

def regularOrdinalBlock {c : Cardinal.{0}} {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) (i j : I) :
    OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
  (CZeroSum.evalCLM i).comp (T.comp (CZeroSum.singleIsometry j).toContinuousLinearMap)

def regularOrdinalBlockJump {c : Cardinal.{0}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) (i j : I) : 𝕜 :=
  initialEndpointJump (𝕜 := 𝕜) hc hu (regularOrdinalBlock T i j)

theorem regularOrdinalBlockJump_column_tendsto
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) (j : I) :
    Tendsto (fun i => ‖regularOrdinalBlockJump hc hu T i j‖) cofinite (𝓝 0) := by
  classical
  apply (JLMS.tendsto_norm_cofinite_iff_finite _).mpr
  intro ε hε
  by_contra hfin
  let e := Set.Infinite.natEmbedding {i | ε ≤ ‖regularOrdinalBlockJump hc hu T i j‖} hfin
  obtain ⟨L, R, _, hL, _, _, hscalar⟩ :=
    exists_initialOrdinal_scalar_family_compression hc hu
      (fun n => regularOrdinalBlock T (e n).val j)
  let one : OrdinalC 𝕜 c.ord := ContinuousMap.const _ 1
  let zero : OrdinalInterval c.ord := ⟨0, le_rfl, Ordinal.zero_le _⟩
  let y := T (CZeroSum.single j (R one))
  have hvalue (n : ℕ) : L (y (e n).val) zero = regularOrdinalBlockJump hc hu T (e n).val j := by
    have h := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V one zero)
      (hscalar n)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousMap.smul_apply, smul_eq_mul,
      one, ContinuousMap.const_apply, mul_one] using h
  have hlarge (n : ℕ) : ε / 4 ≤ ‖y (e n).val‖ := by
    have ha := (e n).property
    have hb : ‖regularOrdinalBlockJump hc hu T (e n).val j‖ ≤ 4 * ‖y (e n).val‖ := by
      rw [← hvalue n]
      exact ((L (y (e n).val)).norm_coe_le_norm zero).trans
        ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _)))
    change ε ≤ ‖regularOrdinalBlockJump hc hu T (e n).val j‖ at ha
    linarith
  have hf : Set.Finite (Set.range (fun n : ℕ => (e n).val)) :=
    (y.finite_norm_ge (show 0 < ε / 4 by positivity)).subset (by
      rintro i ⟨n, rfl⟩
      exact hlarge n)
  exact (Set.infinite_range_of_injective (Subtype.val_injective.comp e.injective)) hf

def regularOrdinalJumpColumn
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) (j : I) :
    CZeroSum 𝕜 (fun _ : I => 𝕜) :=
  CZeroSum.mk (regularOrdinalBlockJump hc hu T · j)
    (regularOrdinalBlockJump_column_tendsto hc hu T j)

@[simp] theorem regularOrdinalJumpColumn_apply
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) {I : Type u}
    (T : CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord) →L[𝕜]
      CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) (i j : I) :
    regularOrdinalJumpColumn hc hu T j i = regularOrdinalBlockJump hc hu T i j := rfl

end Posets
