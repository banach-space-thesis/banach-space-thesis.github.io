import ThesisCommon.Analysis.EllOneCZeroDiagonalReduction
import ThesisCommon.Analysis.IsomorphicDiagonalAssembly
import ThesisCommon.Analysis.SequenceSumEquivs

/-! The full self-similarity alternative of UPFP Theorem 1.1.
The p=1 case is immediate; every other case uses the proved diagonal reduction. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem HasUPFP.ellOne_of_lp_equiv (hX : HasUPFP 𝕜 X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (e : X ≃L[𝕜] lp (fun _ : ℕ => X) p) :
    HasUPFP 𝕜 (EllOneSum ℕ X) := by
  by_cases hp1 : p = 1
  · subst p
    exact hX.of_equiv e
  have hp : p = ∞ ∨ 1 < p.toReal := by
    rcases eq_or_ne p ∞ with hp | hp
    · exact Or.inl hp
    · right
      have hlt : (1 : ℝ≥0∞) < p := lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp1)
      simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal (by simp) hp).mpr hlt
  obtain ⟨C, hC, hX⟩ := hX
  let H : EllOneSum ℕ X ≃L[𝕜] EllOneSum ℕ (lp (fun _ : ℕ => X) p) := lpMapEquiv 1 e
  have hbig : HasUPFP 𝕜 (EllOneSum ℕ (lp (fun _ : ℕ => X) p)) := by
    apply hasUPFP_of_approximate_retractions hC H IsLpDiagonal
      (fun D hD => lp_diagonal_dichotomy hC hX D hD)
    intro T ε hε
    obtain ⟨n, m, _hn, _hm, hsmall⟩ := ellOne_lp_diagonal_reduction p hp T hε
    exact ⟨lpPointRead p 1 n m, lpPointInsert p 1 n m,
      lpDiagonalPart (((lpPointRead p 1 n m).comp T).comp (lpPointInsert p 1 n m)),
      lpPointRead_comp_insert p 1 n m, norm_lpPointRead_le p 1 n m,
      norm_lpPointInsert_le p 1 n m, isLpDiagonal_lpDiagonalPart _, hsmall⟩
  exact hbig.of_equiv H.symm

theorem HasUPFP.ellOne_of_cZero_equiv (hX : HasUPFP 𝕜 X) (e : X ≃L[𝕜] CZeroSum X) :
    HasUPFP 𝕜 (EllOneSum ℕ X) := by
  obtain ⟨C, hC, hX⟩ := hX
  let H : EllOneSum ℕ X ≃L[𝕜] EllOneSum ℕ (CZeroSum X) := lpMapEquiv 1 e
  have hbig : HasUPFP 𝕜 (EllOneSum ℕ (CZeroSum X)) := by
    apply hasUPFP_of_approximate_retractions hC H IsLpDiagonal
      (fun D hD => lp_diagonal_dichotomy hC hX D hD)
    intro T ε hε
    obtain ⟨n, m, _hn, _hm, hsmall⟩ := ellOne_cZero_diagonal_reduction T hε
    exact ⟨lpCZeroPointRead 1 n m, lpCZeroPointInsert 1 n m,
      lpDiagonalPart (((lpCZeroPointRead 1 n m).comp T).comp (lpCZeroPointInsert 1 n m)),
      lpCZeroPointRead_comp_insert 1 n m, norm_lpCZeroPointRead_le 1 n m,
      norm_lpCZeroPointInsert_le 1 n m, isLpDiagonal_lpDiagonalPart _, hsmall⟩
  exact hbig.of_equiv H.symm

theorem HasUPFP.ellOne_of_sequenceSelfSimilar (hX : HasUPFP 𝕜 X)
    (hself : IsSequenceSelfSimilar 𝕜 X) : HasUPFP 𝕜 (EllOneSum ℕ X) := by
  rcases hself with hlp | hzero
  · obtain ⟨p, ⟨e⟩⟩ := hlp
    exact hX.ellOne_of_lp_equiv p.val e
  · obtain ⟨e⟩ := hzero
    exact hX.ellOne_of_cZero_equiv e

end ThesisCommon
