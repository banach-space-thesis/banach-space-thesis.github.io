import ThesisCommon.Analysis.CotypeDiagonalReduction
import ThesisCommon.Analysis.DiagonalAssembly

/-! The complete finite-cotype UPFP preservation argument of UPFP Theorem 1.2.
The diagonal reduction is proved for the actual spaces, so the concluding
compression and perturbation step has no unproved analytic input.
Primariness and the separate self-similarity branch are not asserted here.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- C-PFP and finite cotype of X imply 2C-PFP of ℓ∞(X). -/
theorem HasCPFP.infinity_of_finiteCotype {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 X C) (hcotype : HasFiniteCotype X) :
    HasCPFP 𝕜 (EllInfinitySum X) (2 * C) := by
  apply hasCPFP_of_approximate_compressions hC IsLpDiagonal
    (fun D hD => lp_diagonal_dichotomy hC hX D hD)
  intro T ε hε
  obtain ⟨e, _he, hsmall⟩ := hcotype.infinity_diagonal_reduction T hε
  refine ⟨lpRestrict ∞ e, lpExtend ∞ e,
    lpDiagonalPart (((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e)),
    lpRestrict_comp_extend e, norm_lpRestrict_le e, norm_lpExtend_le e,
    isLpDiagonal_lpDiagonalPart _, hsmall⟩

/-- C-PFP and finite cotype of X imply 2C-PFP of c₀(X). -/
theorem HasCPFP.cZero_of_finiteCotype {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 X C) (hcotype : HasFiniteCotype X) :
    HasCPFP 𝕜 (CZeroSum X) (2 * C) := by
  apply hasCPFP_of_approximate_compressions hC IsCZeroDiagonal
    (fun D hD => cZero_diagonal_dichotomy hC hX D hD)
  intro T ε hε
  obtain ⟨e, _he, hsmall⟩ := hcotype.cZero_diagonal_reduction T hε
  refine ⟨cZeroRestrict e, cZeroExtend e,
    cZeroDiagonalPart (((cZeroRestrict e).comp T).comp (cZeroExtend e)),
    cZeroRestrict_comp_extend e, norm_cZeroRestrict_le e, norm_cZeroExtend_le e,
    isCZeroDiagonal_cZeroDiagonalPart _, hsmall⟩

/-- Genuine preservation of UPFP under ℓ∞ sums in the finite-cotype case. -/
theorem HasUPFP.infinity_of_finiteCotype (hX : HasUPFP 𝕜 X) (hcotype : HasFiniteCotype X) :
    HasUPFP 𝕜 (EllInfinitySum X) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨2 * C, by linarith, hX.infinity_of_finiteCotype hC hcotype⟩

/-- Genuine preservation of UPFP under c₀ sums in the finite-cotype case. -/
theorem HasUPFP.cZero_of_finiteCotype (hX : HasUPFP 𝕜 X) (hcotype : HasFiniteCotype X) :
    HasUPFP 𝕜 (CZeroSum X) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨2 * C, by linarith, hX.cZero_of_finiteCotype hC hcotype⟩

end ThesisCommon
