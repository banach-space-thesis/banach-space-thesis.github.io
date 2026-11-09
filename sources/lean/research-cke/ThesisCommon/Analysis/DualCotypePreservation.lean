import ThesisCommon.Analysis.DualCotypeDiagonalReduction
import ThesisCommon.Analysis.DiagonalAssembly

/-! Complete ell1 UPFP preservation under finite cotype of the Banach dual. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem HasCPFP.ellOne_of_dualFiniteCotype {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 X C) (hcotype : HasFiniteCotype (X →L[𝕜] 𝕜)) :
    HasCPFP 𝕜 (EllOneSum ℕ X) (2*C) := by
  apply hasCPFP_of_approximate_compressions hC IsLpDiagonal
    (fun D hD => lp_diagonal_dichotomy hC hX D hD)
  intro T ε hε
  obtain ⟨e, _he, hsmall⟩ := hcotype.dual_ellOne_diagonal_reduction T hε
  exact ⟨lpRestrict 1 e, lpExtend 1 e,
    lpDiagonalPart (((lpRestrict 1 e).comp T).comp (lpExtend 1 e)),
    lpRestrict_comp_extend e, norm_lpRestrict_le e, norm_lpExtend_le e,
    isLpDiagonal_lpDiagonalPart _, hsmall⟩

theorem HasUPFP.ellOne_of_dualFiniteCotype (hX : HasUPFP 𝕜 X)
    (hcotype : HasFiniteCotype (X →L[𝕜] 𝕜)) : HasUPFP 𝕜 (EllOneSum ℕ X) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨2*C, by linarith, hX.ellOne_of_dualFiniteCotype hC hcotype⟩

end ThesisCommon
