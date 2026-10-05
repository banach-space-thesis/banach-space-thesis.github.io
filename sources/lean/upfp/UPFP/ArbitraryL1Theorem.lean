import UPFP.L1Applications
import ThesisCommon.Analysis.IntervalL1ArbitraryEllOneFactorization
import ThesisCommon.Analysis.IntervalDualRepresentation
import ThesisCommon.Analysis.PrimaryIsometry

/-! Theorem 1.6 with its original arbitrary index and scalar quantifiers.
The dual conclusion uses the actual continuum-sum representation and the
proved decomposition theorem. No continuum hypothesis is assumed. -/
noncomputable section
open scoped ENNReal
namespace UPFP
open ThesisCommon

theorem theorem_1_6_dual_upfp_primary (𝕜 : Type*) [RCLike 𝕜] :
    HasUPFP 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) ∧
      IsPrimary 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := by
  letI : Infinite UnitInterval := Cardinal.aleph0_le_mk_iff.mp (by
    rw [Cardinal.mk_Icc_real (show (0 : ℝ) < 1 by norm_num)]
    exact Cardinal.aleph0_le_continuum)
  let e := intervalContinuousDualLebesgueEquiv 𝕜
  have h := intervalL1ArbitraryEllOne_hasUPFP 𝕜 UnitInterval
  have hs : IsSequenceSelfSimilar 𝕜 (EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)) :=
    Or.inl ⟨⟨1, le_rfl⟩, ⟨(lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜)
      (X := IntervalLp 𝕜 ⟨1, le_rfl⟩) (Γ := UnitInterval) 1 (by norm_num)).toContinuousLinearEquiv⟩⟩
  exact ⟨h.of_equiv e.symm, (h.isPrimary_of_sequenceSelfSimilar hs).of_equiv e.symm⟩

theorem theorem_1_6_proof (𝕜 Γ : Type*) [RCLike 𝕜] : Theorem_1_6 𝕜 Γ :=
  ⟨intervalL1ArbitraryEllOne_hasUPFP 𝕜 Γ, theorem_1_6_dual_upfp_primary 𝕜⟩

end UPFP
