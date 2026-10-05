import ThesisCommon.Analysis.CZeroSelfSimilarDiagonalReduction
import ThesisCommon.Analysis.IsomorphicDiagonalAssembly
import ThesisCommon.Analysis.SequenceSumEquivs

/-! UPFP preservation for finite-p self-similar coefficient spaces.
All reductions are supplied by the proved Proposition 5.4 constructions. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem HasUPFP.infinity_of_lp_equiv (hX : HasUPFP 𝕜 X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (e : X ≃L[𝕜] lp (fun _ : ℕ => X) p) :
    HasUPFP 𝕜 (EllInfinitySum X) := by
  obtain ⟨C, hC, hX⟩ := hX
  let H : EllInfinitySum X ≃L[𝕜] EllInfinitySum (lp (fun _ : ℕ => X) p) := lpMapEquiv ∞ e
  have hbig : HasUPFP 𝕜 (EllInfinitySum (lp (fun _ : ℕ => X) p)) := by
    apply hasUPFP_of_approximate_retractions hC H IsLpDiagonal
      (fun D hD => lp_diagonal_dichotomy hC hX D hD)
    intro T ε hε
    obtain ⟨n, m, _hn, _hm, hsmall⟩ := infinity_lp_diagonal_reduction p hp T hε
    exact ⟨lpPointRead p ∞ n m, lpPointInsert p ∞ n m,
      lpDiagonalPart (((lpPointRead p ∞ n m).comp T).comp (lpPointInsert p ∞ n m)),
      lpPointRead_comp_insert p ∞ n m, norm_lpPointRead_le p ∞ n m,
      norm_lpPointInsert_le p ∞ n m, isLpDiagonal_lpDiagonalPart _, hsmall⟩
  exact hbig.of_equiv H.symm

theorem HasUPFP.cZero_of_lp_equiv (hX : HasUPFP 𝕜 X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (e : X ≃L[𝕜] lp (fun _ : ℕ => X) p) :
    HasUPFP 𝕜 (CZeroSum X) := by
  obtain ⟨C, hC, hX⟩ := hX
  let H : CZeroSum X ≃L[𝕜] CZeroSum (lp (fun _ : ℕ => X) p) := cZeroMapEquiv e
  have hbig : HasUPFP 𝕜 (CZeroSum (lp (fun _ : ℕ => X) p)) := by
    apply hasUPFP_of_approximate_retractions hC H IsCZeroDiagonal
      (fun D hD => cZero_diagonal_dichotomy hC hX D hD)
    intro T ε hε
    obtain ⟨n, m, _hn, _hm, hsmall⟩ := cZero_lp_diagonal_reduction p hp T hε
    exact ⟨cZeroPointRead p n m, cZeroPointInsert p n m,
      cZeroDiagonalPart (((cZeroPointRead p n m).comp T).comp (cZeroPointInsert p n m)),
      cZeroPointRead_comp_insert p n m, norm_cZeroPointRead_le p n m,
      norm_cZeroPointInsert_le p n m, isCZeroDiagonal_cZeroDiagonalPart _, hsmall⟩
  exact hbig.of_equiv H.symm

theorem HasUPFP.infinity_of_finiteLpSelfSimilar (hX : HasUPFP 𝕜 X)
    (hself : IsFiniteLpSelfSimilar 𝕜 X) : HasUPFP 𝕜 (EllInfinitySum X) := by
  obtain ⟨p, hp, ⟨e⟩⟩ := hself
  exact hX.infinity_of_lp_equiv p.val hp e

theorem HasUPFP.cZero_of_finiteLpSelfSimilar (hX : HasUPFP 𝕜 X)
    (hself : IsFiniteLpSelfSimilar 𝕜 X) : HasUPFP 𝕜 (CZeroSum X) := by
  obtain ⟨p, hp, ⟨e⟩⟩ := hself
  exact hX.cZero_of_lp_equiv p.val hp e

end ThesisCommon
