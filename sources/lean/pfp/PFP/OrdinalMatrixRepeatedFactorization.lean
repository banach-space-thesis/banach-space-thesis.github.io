import PFP.OrdinalMatrixSmallRepeatedBlocks
import ThesisCommon.Analysis.Factorization
import Posets.CZeroContinuousAmplification

/-! Scalar c₀ factorisations lift to repeated regular ordinal blocks.
This proves the genuine all-operator dichotomy for C(κ·ω). -/
noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS ThesisCommon
universe u v
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

local instance repeatedFactorSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance repeatedFactorSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem factorsIdentityWith_cZeroContinuousAmplification
    {I : Type u} {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {A : JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜) →L[𝕜] JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)}
    {C : ℝ} (h : FactorsIdentityWith A (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) C) :
    FactorsIdentityWith (cZeroContinuousAmplification (K := K) A)
      (JLMS.CZeroSum 𝕜 (fun _ : I => C(K, 𝕜))) C := by
  obtain ⟨U, V, hUV, hnorm⟩ := h
  refine ⟨cZeroContinuousAmplification U, cZeroContinuousAmplification V, ?_, ?_⟩
  · rw [← cZeroContinuousAmplification_comp, ← cZeroContinuousAmplification_comp,
      hUV, cZeroContinuousAmplification_id]
  · exact (mul_le_mul (norm_cZeroContinuousAmplification_le (K := K) U)
      (norm_cZeroContinuousAmplification_le (K := K) V) (norm_nonneg _) (norm_nonneg _)).trans hnorm

attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm

theorem smallRepeatedRegularOrdinal_hasUPFP_of_scalar
    {c : Cardinal.{ordU}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    {I : Type ordU} [Nonempty I] (hI : Cardinal.mk I < c)
    (hscalar : HasUPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜))) :
    HasUPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => OrdinalC 𝕜 c.ord)) := by
  obtain ⟨C, hC, hpfp⟩ := hscalar
  refine ⟨8*C, by linarith, ?_⟩
  intro T
  obtain ⟨L, R, hLR, hL, hR, A, hcols⟩ :=
    exists_smallRepeatedRegularOrdinal_scalar_blocks hc hu hI T
  have hD : (L.comp T).comp R = cZeroContinuousAmplification A :=
    eq_cZeroContinuousAmplification_of_columns A _ hcols
  have hbound : C * (‖L‖ * ‖R‖) ≤ 8*C := by
    calc
      _ ≤ C * (4*2) := by gcongr
      _ = 8*C := by ring
  rcases hpfp A with hA | hA
  · have h := factorsIdentityWith_cZeroContinuousAmplification (K := JLMS.OrdinalInterval c.ord) hA
    rw [← hD] at h
    exact Or.inl ((h.of_compression L R).mono hbound)
  · have h := factorsIdentityWith_cZeroContinuousAmplification (K := JLMS.OrdinalInterval c.ord) hA
    rw [cZeroContinuousAmplification_sub, cZeroContinuousAmplification_id, ← hD,
      ← compression_complement T L R hLR] at h
    exact Or.inr ((h.of_compression L R).mono hbound)

end Posets.UniverseRegularMatrix


