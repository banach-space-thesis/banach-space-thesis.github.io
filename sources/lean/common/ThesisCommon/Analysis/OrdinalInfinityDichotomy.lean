import ThesisCommon.Analysis.OrdinalInfinityDiagonal
import ThesisCommon.Analysis.OrdinalLowerTriangular
import ThesisCommon.Analysis.DiagonalAssembly

/-! LPCK 4.6 and the infinity sequence assembly for characteristic-one ordinal intervals. Only the independent base-space C-PFP remains a hypothesis. -/
noncomputable section
open scoped ENNReal
universe u
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α η a : Ordinal.{u}}

theorem ordinal_infinity_lower_dichotomy (hD : ordinalDerived (Set.Icc 0 α) η = {a}) {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 ((OrdinalContinuous 𝕜 α)) C)
    (L : EllInfinitySum ((OrdinalContinuous 𝕜 α)) →L[𝕜] EllInfinitySum ((OrdinalContinuous 𝕜 α)))
    (hL : IsLpLowerPart L L) :
    FactorsIdentityWith L (EllInfinitySum ((OrdinalContinuous 𝕜 α))) (2*C) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - L)
        (EllInfinitySum ((OrdinalContinuous 𝕜 α))) (2*C) := by
  apply factorization_dichotomy_of_approximate_compressions hC L IsLpDiagonal
    (fun D hD => lp_diagonal_dichotomy hC hX D hD)
  intro ε hε
  obtain ⟨A, B, hAB, hA, hB, hsmall⟩ := ordinal_infinity_lower_diagonal_retraction hD L hL hε
  exact ⟨A, B, lpDiagonalPart ((A.comp L).comp B), hAB, hA, hB,
    isLpDiagonal_lpDiagonalPart _, hsmall⟩

theorem HasCPFP.ordinal_infinity (hD : ordinalDerived (Set.Icc 0 α) η = {a}) {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 ((OrdinalContinuous 𝕜 α)) C) :
    HasCPFP 𝕜 (EllInfinitySum ((OrdinalContinuous 𝕜 α))) (4*C) := by
  have h := hasCPFP_of_approximate_compressions (by linarith : 1 ≤ 2*C)
    (fun L : EllInfinitySum ((OrdinalContinuous 𝕜 α)) →L[𝕜] EllInfinitySum ((OrdinalContinuous 𝕜 α)) =>
      IsLpLowerPart L L)
    (fun L hL => ordinal_infinity_lower_dichotomy hD hC hX L hL)
  have hconstant : 2*(2*C) = 4*C := by ring
  rw [hconstant] at h
  apply h
  intro T ε hε
  obtain ⟨e, c, L, _, hAB, hsmall, hL⟩ := ordinal_lp_lower_retraction hD (Or.inl rfl) T hε
  exact ⟨_, _, L, hAB, norm_lpBlockRead_le ∞ e _ _, norm_lpBlockInsert_le ∞ e _ _,
    hL.self_lowerPart, hsmall⟩

theorem HasUPFP.ordinal_infinity (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hX : HasUPFP 𝕜 ((OrdinalContinuous 𝕜 α))) :
    HasUPFP 𝕜 (EllInfinitySum ((OrdinalContinuous 𝕜 α))) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨4*C, by linarith, hX.ordinal_infinity hD hC⟩

end ThesisCommon

