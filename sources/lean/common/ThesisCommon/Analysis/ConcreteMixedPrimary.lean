import ThesisCommon.Analysis.ConcreteSchauderSums
import ThesisCommon.Analysis.ConcreteNonEllOneBases
import ThesisCommon.Analysis.MixedEllOneFactorization
import ThesisCommon.Analysis.MixedInfinityFactorization
import ThesisCommon.Analysis.PelczynskiDecomposition
import ThesisCommon.Analysis.LpSelfSimilarity
import ThesisCommon.Analysis.CZeroSelfSimilarity

/-! Primariness of the actual c₀(ell₁), ℓp(ell₁), and c₀(ell_infinity)
spaces. Transport uses coordinate-preserving linear isometries. The final
step is the proved Pełczyński decomposition method, with countable sequence
self-similarity supplied by actual flattening equivalences. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem cZero_ellOne_hasUPFP : HasUPFP 𝕜 (CZeroSum (lp (fun _ : ℕ => 𝕜) 1)) := by
  have hs := scalarCZeroSchauderBasis_symmetric (𝕜 := 𝕜)
  have hf := SchauderSum.ellOne_hasCPlusPFP_two (hb := hs.1) hs
    (scalarCZeroSchauderBasis_not_equivalentEllOne (𝕜 := 𝕜))
  exact (hf.hasUPFP (by norm_num)).of_equiv
    (cZeroSchauderSumEquiv (𝕜 := 𝕜) (Y := lp (fun _ : ℕ => 𝕜) 1) hs.1).toContinuousLinearEquiv

theorem lp_ellOne_hasUPFP (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p) :
    HasUPFP 𝕜 (lp (fun _ : ℕ => lp (fun _ : ℕ => 𝕜) 1) p) := by
  have hs := scalarLpSchauderBasis_symmetric (𝕜 := 𝕜) p hp
  have hf := SchauderSum.ellOne_hasCPlusPFP_two (hb := hs.1) hs
    (scalarLpSchauderBasis_not_equivalentEllOne p hp hp1)
  exact (hf.hasUPFP (by norm_num)).of_equiv
    (lpSchauderSumEquiv (𝕜 := 𝕜) (Y := lp (fun _ : ℕ => 𝕜) 1) p hp hs.1).toContinuousLinearEquiv

theorem cZero_infinity_hasUPFP : HasUPFP 𝕜 (CZeroSum (lp (fun _ : ℕ => 𝕜) ∞)) := by
  have hs := scalarCZeroSchauderBasis_symmetric (𝕜 := 𝕜)
  have hf := SchauderSum.infinity_hasCPlusPFP_two (hb := hs.1) hs
    (scalarCZeroSchauderBasis_not_equivalentEllOne (𝕜 := 𝕜))
  exact (hf.hasUPFP (by norm_num)).of_equiv
    (cZeroSchauderSumEquiv (𝕜 := 𝕜) (Y := lp (fun _ : ℕ => 𝕜) ∞) hs.1).toContinuousLinearEquiv

theorem cZero_ellOne_isPrimary : IsPrimary 𝕜 (CZeroSum (lp (fun _ : ℕ => 𝕜) 1)) :=
  (cZero_ellOne_hasUPFP (𝕜 := 𝕜)).isPrimary_of_sequenceSelfSimilar
    (cZero_sequenceSelfSimilar (𝕜 := 𝕜) (X := lp (fun _ : ℕ => 𝕜) 1))

theorem lp_ellOne_isPrimary (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p) :
    IsPrimary 𝕜 (lp (fun _ : ℕ => lp (fun _ : ℕ => 𝕜) 1) p) :=
  (lp_ellOne_hasUPFP (𝕜 := 𝕜) p hp hp1).isPrimary_of_sequenceSelfSimilar
    (lp_sequenceSelfSimilar (𝕜 := 𝕜) (X := lp (fun _ : ℕ => 𝕜) 1) p)

theorem cZero_infinity_isPrimary : IsPrimary 𝕜 (CZeroSum (lp (fun _ : ℕ => 𝕜) ∞)) :=
  (cZero_infinity_hasUPFP (𝕜 := 𝕜)).isPrimary_of_sequenceSelfSimilar
    (cZero_sequenceSelfSimilar (𝕜 := 𝕜) (X := lp (fun _ : ℕ => 𝕜) ∞))

end ThesisCommon
