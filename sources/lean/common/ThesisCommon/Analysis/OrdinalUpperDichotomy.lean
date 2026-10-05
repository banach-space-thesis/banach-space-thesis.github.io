import ThesisCommon.Analysis.OrdinalLowerTriangular
import ThesisCommon.Analysis.TriangularDiagonalAlgebra
import ThesisCommon.Analysis.DiagonalAssembly

/-! LPCK Proposition 3.15 on characteristic-one compact ordinal intervals. The base-space C-PFP hypothesis is retained; the whole-operator reduction and contractive transfer are proved. -/
noncomputable section
open scoped ENNReal
universe u
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α η a : Ordinal.{u}}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem ordinal_upper_diagonal_reduction (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p = ∞ ∨ 1 < p.toReal)
    (U : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p)
    (hU : IsLpUpperPart U U) {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p,
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ‖(A.comp U).comp B - lpDiagonalPart ((A.comp U).comp B)‖ < ε := by
  obtain ⟨e, c, L, he, hAB, hsmall, hL⟩ := ordinal_lp_lower_retraction hD hp U hε
  let A := lpBlockRead p e (fun k => ordinalCopyRead (𝕜 := 𝕜) (c k))
    (fun k => norm_ordinalCopyRead_le (𝕜 := 𝕜) (c k))
  let B := lpBlockInsert p e (fun k => ordinalCopyInsert (𝕜 := 𝕜) (c k))
    (fun k => norm_ordinalCopyInsert_le (𝕜 := 𝕜) (c k))
  have hupper : IsLpUpperPart ((A.comp U).comp B) ((A.comp U).comp B) :=
    hU.block_compression e he _ _ _ _
  have hdiag := hL.eq_diagonal_of_upper hupper
  refine ⟨A, B, hAB, norm_lpBlockRead_le p e _ _, norm_lpBlockInsert_le p e _ _, ?_⟩
  rwa [hdiag] at hsmall

theorem ordinal_lp_upper_dichotomy (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p = ∞ ∨ 1 < p.toReal)
    {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 (OrdinalContinuous 𝕜 α) C)
    (U : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p)
    (hU : IsLpUpperPart U U) :
    FactorsIdentityWith U (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) (2*C) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - U)
        (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) (2*C) := by
  apply factorization_dichotomy_of_approximate_compressions hC U IsLpDiagonal
    (fun D hD => lp_diagonal_dichotomy hC hX D hD)
  intro ε hε
  obtain ⟨A, B, hAB, hA, hB, hsmall⟩ := ordinal_upper_diagonal_reduction hD hp U hU hε
  exact ⟨A, B, lpDiagonalPart ((A.comp U).comp B), hAB, hA, hB,
    isLpDiagonal_lpDiagonalPart _, hsmall⟩

end ThesisCommon
