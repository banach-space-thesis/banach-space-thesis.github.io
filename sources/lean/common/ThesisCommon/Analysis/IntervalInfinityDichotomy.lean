import ThesisCommon.Analysis.IntervalInfinityDiagonal
import ThesisCommon.Analysis.IntervalLowerTriangular
import ThesisCommon.Analysis.DiagonalAssembly

/-! LPCK 4.6 and the infinity assembly in Section 5, for C[0,1].
The stated base-space C-PFP hypothesis is explicit. The reductions,
retractions, diagonal dichotomy and both perturbations are proved. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem interval_infinity_lower_dichotomy {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 (IntervalContinuous 𝕜) C)
    (L : EllInfinitySum (IntervalContinuous 𝕜) →L[𝕜] EllInfinitySum (IntervalContinuous 𝕜))
    (hL : IsLpLowerPart L L) :
    FactorsIdentityWith L (EllInfinitySum (IntervalContinuous 𝕜)) (2*C) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - L)
        (EllInfinitySum (IntervalContinuous 𝕜)) (2*C) := by
  apply factorization_dichotomy_of_approximate_compressions hC L IsLpDiagonal
    (fun D hD => lp_diagonal_dichotomy hC hX D hD)
  intro ε hε
  obtain ⟨A, B, hAB, hA, hB, hsmall⟩ := interval_infinity_lower_diagonal_retraction L hL hε
  exact ⟨A, B, lpDiagonalPart ((A.comp L).comp B), hAB, hA, hB,
    isLpDiagonal_lpDiagonalPart _, hsmall⟩

theorem HasCPFP.interval_infinity {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 (IntervalContinuous 𝕜) C) :
    HasCPFP 𝕜 (EllInfinitySum (IntervalContinuous 𝕜)) (4*C) := by
  have h := hasCPFP_of_approximate_compressions (by linarith : 1 ≤ 2*C)
    (fun L : EllInfinitySum (IntervalContinuous 𝕜) →L[𝕜] EllInfinitySum (IntervalContinuous 𝕜) =>
      IsLpLowerPart L L)
    (fun L hL => interval_infinity_lower_dichotomy hC hX L hL)
  have hconstant : 2*(2*C) = 4*C := by ring
  rw [hconstant] at h
  apply h
  intro T ε hε
  obtain ⟨e, c, L, _, hAB, hsmall, hL⟩ := interval_lp_lower_retraction (Or.inl rfl) T hε
  exact ⟨_, _, L, hAB, norm_lpBlockRead_le ∞ e _ _, norm_lpBlockInsert_le ∞ e _ _,
    hL.self_lowerPart, hsmall⟩

theorem HasUPFP.interval_infinity (hX : HasUPFP 𝕜 (IntervalContinuous 𝕜)) :
    HasUPFP 𝕜 (EllInfinitySum (IntervalContinuous 𝕜)) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨4*C, by linarith, hX.interval_infinity hC⟩

end ThesisCommon
