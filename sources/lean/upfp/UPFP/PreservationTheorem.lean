import UPFP.CotypeSteps
import ThesisCommon.Analysis.SelfSimilarPreservation

/-! The complete Theorem 1.2 of the supplied preservation paper. Both
alternative hypotheses and all four conclusions are proved. -/
noncomputable section
open scoped ENNReal
namespace UPFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- Proposition 5.4, infinity case, using the manuscript's point retractions
and increasing sequences in both coordinates. -/
theorem proposition_5_4_infinity (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : EllInfinitySum (lp (fun _ : ℕ => X) p) →L[𝕜]
      EllInfinitySum (lp (fun _ : ℕ => X) p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ ↪ ℕ) (m : ℕ → ℕ), StrictMono n ∧ StrictMono m ∧
      ‖((lpPointRead p ∞ n m).comp T).comp (lpPointInsert p ∞ n m) -
        lpDiagonalPart (((lpPointRead p ∞ n m).comp T).comp (lpPointInsert p ∞ n m))‖ < ε :=
  infinity_lp_diagonal_reduction p hp T hε

omit [CompleteSpace X] in
/-- Proposition 5.4, c₀ case, on actual null sequences. -/
theorem proposition_5_4_cZero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : CZeroSum (lp (fun _ : ℕ => X) p) →L[𝕜] CZeroSum (lp (fun _ : ℕ => X) p))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ ↪ ℕ) (m : ℕ → ℕ), StrictMono n ∧ StrictMono m ∧
      ‖((cZeroPointRead p n m).comp T).comp (cZeroPointInsert p n m) -
        cZeroDiagonalPart (((cZeroPointRead p n m).comp T).comp (cZeroPointInsert p n m))‖ < ε :=
  cZero_lp_diagonal_reduction p hp T hε

/-- All four conclusions under the finite-p self-similarity alternative. -/
theorem theorem_1_2_finiteLpSelfSimilar (hX : HasUPFP 𝕜 X)
    (hself : IsFiniteLpSelfSimilar 𝕜 X) :
    (HasUPFP 𝕜 (CZeroSum X) ∧ HasUPFP 𝕜 (EllInfinitySum X)) ∧
      (IsPrimary 𝕜 (CZeroSum X) ∧ IsPrimary 𝕜 (EllInfinitySum X)) := by
  have hz := hX.cZero_of_finiteLpSelfSimilar hself
  have hi := hX.infinity_of_finiteLpSelfSimilar hself
  exact ⟨⟨hz, hi⟩, hz.cZero_isPrimary, hi.infinity_isPrimary⟩

/-- Theorem 1.2, with exactly the hypotheses and conclusions of its original
statement. No diagonal reduction or auxiliary analytic theorem is assumed. -/
theorem theorem_1_2_proof : Theorem_1_2 𝕜 X := by
  intro hX h
  rcases h with hself | hcotype
  · exact theorem_1_2_finiteLpSelfSimilar hX hself
  · exact theorem_1_2_finiteCotype hX hcotype

end UPFP

