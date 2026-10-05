import UPFP.MainStatements
import ThesisCommon.Analysis.InfinityDiagonal
import ThesisCommon.Analysis.LpDiagonal
import ThesisCommon.Analysis.CZeroDiagonal
import ThesisCommon.Analysis.DiagonalAssembly
import ThesisCommon.Analysis.SequencePrimariness

/-! Checked supporting results, separate from the open main targets. -/
noncomputable section
namespace UPFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Proposition 5.5, the ℓ₁ case. -/
theorem proposition_5_5_ellOne {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 X C)
    (D : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) (hD : IsLpDiagonal D) :
    FactorsIdentityWith D (EllOneSum ℕ X) C ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (EllOneSum ℕ X) - D)
      (EllOneSum ℕ X) C := lp_diagonal_dichotomy hC hX D hD

/-- Proposition 5.5, the c₀ case. -/
theorem proposition_5_5_cZero {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 X C)
    (D : CZeroSum X →L[𝕜] CZeroSum X) (hD : IsCZeroDiagonal D) :
    FactorsIdentityWith D (CZeroSum X) C ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (CZeroSum X) - D)
      (CZeroSum X) C := cZero_diagonal_dichotomy hC hX D hD

/-- Proposition 5.5, the ℓ∞ case. Together the three wrappers cover the proposition. -/
theorem proposition_5_5_infinity {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 X C)
    (D : EllInfinitySum X →L[𝕜] EllInfinitySum X) (hD : IsInfinityDiagonal D) :
    FactorsIdentityWith D (EllInfinitySum X) C ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (EllInfinitySum X) - D)
      (EllInfinitySum X) C := infinity_diagonal_dichotomy hC hX D hD

/-- Lemma 5.6, all Banach X and both scalar fields, with the exact 2C bound. -/
theorem lemma_5_6 [CompleteSpace X] {T S : X →L[𝕜] X} {C : ℝ}
    (h : FactorsIdentityWith T X C) (hsmall : C * ‖S - T‖ < 1 / 2) :
    FactorsIdentityWith S X (2 * C) := h.perturb hsmall

/-- The trivial self-similarity branch in the proof of Theorem 1.1:
X ≃ ℓ₁(X) transports UPFP directly. Primariness is NOT concluded here. -/
theorem ellOne_upfp_of_ellOne_equiv (hX : HasUPFP 𝕜 X)
    (e : X ≃L[𝕜] EllOneSum ℕ X) : HasUPFP 𝕜 (EllOneSum ℕ X) := hX.of_equiv e

/-- Both conclusions of Theorem 1.1 in its immediate ℓ₁ self-similarity
subcase. The other self-similarity and dual-cotype cases remain separate. -/
theorem theorem_1_1_ellOne_equiv (hX : HasUPFP 𝕜 X)
    (e : X ≃L[𝕜] EllOneSum ℕ X) :
    HasUPFP 𝕜 (EllOneSum ℕ X) ∧ IsPrimary 𝕜 (EllOneSum ℕ X) := by
  have h := ellOne_upfp_of_ellOne_equiv hX e
  exact ⟨h, h.lp_isPrimary⟩

/-- The empty-index case of the first clause of Theorem 1.6.
This does not establish that theorem's independent C[0,1]* conclusions. -/
theorem theorem_1_6_empty_index_upfp (Γ : Type*) [IsEmpty Γ] :
    HasUPFP 𝕜 (EllOneSum Γ (IntervalLp 𝕜 ⟨1, le_rfl⟩)) := by
  letI : Subsingleton (EllOneSum Γ (IntervalLp 𝕜 ⟨1, le_rfl⟩)) :=
    ⟨fun x y => Subtype.ext (funext (fun i => isEmptyElim i))⟩
  exact hasUPFP_of_subsingleton

/-- Open analytic input for the ℓ∞ conclusion of 1.2. This records a weaker
output specification of Section 5's coordinate construction: an actual
contractive retract and an actual diagonal, not an assumed UPFP conclusion. -/
def InfinityDiagonalReduction : Prop :=
  ∀ (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) (ε : ℝ), 0 < ε →
    ∃ A B D : EllInfinitySum X →L[𝕜] EllInfinitySum X,
      A.comp B = ContinuousLinearMap.id 𝕜 (EllInfinitySum X) ∧
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ IsInfinityDiagonal D ∧ ‖(A.comp T).comp B - D‖ < ε

/-- Conditional conclusion of the finite-cotype branch for ℓ∞(X).
The reduction remains an explicit unproved input; this is NOT Theorem 1.2. -/
theorem infinity_upfp_of_diagonal_reduction [CompleteSpace X]
    (hX : HasUPFP 𝕜 X) (hred : InfinityDiagonalReduction (𝕜 := 𝕜) (X := X)) :
    HasUPFP 𝕜 (EllInfinitySum X) := by
  obtain ⟨C, hC, hX⟩ := hX
  refine ⟨2 * C, by linarith, ?_⟩
  exact hasCPFP_of_approximate_compressions hC IsInfinityDiagonal
    (fun D hD => infinity_diagonal_dichotomy hC hX D hD) hred

end UPFP
