import LPCK.MainStatements
import ThesisCommon.Analysis.InfinityDiagonal
import ThesisCommon.Analysis.LpDiagonal
import ThesisCommon.Analysis.DiagonalAssembly

/-! Supporting results consumed through ThesisCommon, not copied proofs. -/
noncomputable section
namespace LPCK
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Lemma 2.3 for every exponent 1 ≤ p ≤ ∞, with the same constant C. -/
theorem lemma_2_3 (p : BanachExponent) {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 X C) (D : SequenceSum p X →L[𝕜] SequenceSum p X)
    (hD : IsLpDiagonal D) :
    FactorsIdentityWith D (SequenceSum p X) C ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (SequenceSum p X) - D)
      (SequenceSum p X) C := lp_diagonal_dichotomy hC hX D hD

/-- Compatibility specialization of Lemma 2.3 to p = ∞. -/
theorem lemma_2_3_infinity {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 X C)
    (D : EllInfinitySum X →L[𝕜] EllInfinitySum X) (hD : IsInfinityDiagonal D) :
    FactorsIdentityWith D (EllInfinitySum X) C ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (EllInfinitySum X) - D)
      (EllInfinitySum X) C := infinity_diagonal_dichotomy hC hX D hD

/-- Lemma 2.4, all Banach X, exact bound 2C, paper's Neumann-series proof. -/
theorem lemma_2_4 [CompleteSpace X] {T S : X →L[𝕜] X} {C : ℝ}
    (h : FactorsIdentityWith T X C) (hsmall : C * ‖S - T‖ < 1 / 2) :
    FactorsIdentityWith S X (2 * C) := h.perturb hsmall

/-- Corollary 2.5 for every exponent, including the complementary branch. -/
theorem corollary_2_5 [CompleteSpace X] (p : BanachExponent) {C : ℝ}
    (hC : 1 ≤ C) (hX : HasCPFP 𝕜 X C)
    (S D : SequenceSum p X →L[𝕜] SequenceSum p X)
    (hD : IsLpDiagonal D) (hsmall : C * ‖S - D‖ < 1 / 2) :
    FactorsIdentityWith S (SequenceSum p X) (2 * C) ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (SequenceSum p X) - S)
      (SequenceSum p X) (2 * C) :=
  factorization_dichotomy_perturb (lemma_2_3 p hC hX D hD) hsmall

/-- Compatibility specialization of Corollary 2.5 to p = ∞. -/
theorem corollary_2_5_infinity [CompleteSpace X] {C : ℝ}
    (hC : 1 ≤ C) (hX : HasCPFP 𝕜 X C)
    (S D : EllInfinitySum X →L[𝕜] EllInfinitySum X)
    (hD : IsInfinityDiagonal D) (hsmall : C * ‖S - D‖ < 1 / 2) :
    FactorsIdentityWith S (EllInfinitySum X) (2 * C) ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (EllInfinitySum X) - S)
      (EllInfinitySum X) (2 * C) :=
  factorization_dichotomy_perturb (infinity_diagonal_dichotomy hC hX D hD) hsmall

end LPCK
