import ThesisCommon.Analysis.IntervalLowerTriangular
import ThesisCommon.Analysis.TriangularDiagonalAlgebra
import ThesisCommon.Analysis.DiagonalAssembly

/-! LPCK Proposition 3.15 for C[0,1]. The hypothesis that C[0,1] has
C-PFP is retained exactly as in the proposition. The reduction to a
diagonal and its transfer through contractive interval retractions are proved. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem interval_upper_diagonal_reduction (hp : p = ∞ ∨ 1 < p.toReal)
    (U : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p)
    (hU : IsLpUpperPart U U) {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p,
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ‖(A.comp U).comp B - lpDiagonalPart ((A.comp U).comp B)‖ < ε := by
  obtain ⟨e, c, L, he, hAB, hsmall, hL⟩ := interval_lp_lower_retraction hp U hε
  let A := lpBlockRead p e (fun k => intervalRead (𝕜 := 𝕜) (c k))
    (fun k => norm_intervalRead_le (𝕜 := 𝕜) (c k))
  let B := lpBlockInsert p e (fun k => intervalInsert (𝕜 := 𝕜) (c k))
    (fun k => norm_intervalInsert_le (𝕜 := 𝕜) (c k))
  have hupper : IsLpUpperPart ((A.comp U).comp B) ((A.comp U).comp B) :=
    hU.block_compression e he _ _ _ _
  have hdiag := hL.eq_diagonal_of_upper hupper
  refine ⟨A, B, hAB, norm_lpBlockRead_le p e _ _, norm_lpBlockInsert_le p e _ _, ?_⟩
  rwa [hdiag] at hsmall

theorem interval_lp_upper_dichotomy (hp : p = ∞ ∨ 1 < p.toReal)
    {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 (IntervalContinuous 𝕜) C)
    (U : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p)
    (hU : IsLpUpperPart U U) :
    FactorsIdentityWith U (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) (2*C) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - U)
        (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) (2*C) := by
  apply factorization_dichotomy_of_approximate_compressions hC U IsLpDiagonal
    (fun D hD => lp_diagonal_dichotomy hC hX D hD)
  intro ε hε
  obtain ⟨A, B, hAB, hA, hB, hsmall⟩ := interval_upper_diagonal_reduction hp U hU hε
  exact ⟨A, B, lpDiagonalPart ((A.comp U).comp B), hAB, hA, hB,
    isLpDiagonal_lpDiagonalPart _, hsmall⟩

end ThesisCommon
