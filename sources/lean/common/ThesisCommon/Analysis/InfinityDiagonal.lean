import ThesisCommon.Analysis.InfinityOperators
import ThesisCommon.Analysis.FactorNormalization
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! The complete ℓ∞ case of UPFP Proposition 5.5 / LPCK Lemma 2.3.
Uses the paper's infinite monochromatic subset, reciprocal rescaling and
coordinatewise factorisation. It does not assume matrix determination.
-/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Infinitely many diagonal entries factoring I suffice. The injection e
enumerates that subset; zero extension and restriction implement the compression. -/
theorem infinity_diagonal_factors_of_subsequence
    (D : EllInfinitySum X →L[𝕜] EllInfinitySum X) (F : ℕ → X →L[𝕜] X)
    (hD : ∀ x n, D x n = F n (x n)) (e : ℕ ↪ ℕ)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ n, FactorsIdentityWith (F (e n)) X C) :
    FactorsIdentityWith D (EllInfinitySum X) C := by
  classical
  choose U V heq hU hV using fun n => (hF n).normalized
  let A := infinityDiagonal U C hC hU
  let B := infinityDiagonal V 1 zero_le_one hV
  let P := infinityRestrict (𝕜 := 𝕜) (X := X) e
  let J := infinityExtend (𝕜 := 𝕜) (X := X) e
  have hnA : ‖A‖ ≤ C := norm_infinityDiagonal_le _ _ _ _
  have hnB : ‖B‖ ≤ 1 := norm_infinityDiagonal_le _ _ _ _
  have hnP : ‖P‖ ≤ 1 := norm_infinityRestrict_le e
  have hnJ : ‖J‖ ≤ 1 := norm_infinityExtend_le e
  refine ⟨A.comp P, J.comp B, ?_, ?_⟩
  · ext x n
    change U n (D (J (B x)) (e n)) = x n
    rw [hD]
    change U n (F (e n) (infinityExtend e (B x) (e n))) = x n
    rw [infinityExtend_apply_image]
    exact congrArg (fun f : X →L[𝕜] X => f (x n)) (heq n)
  · have hAP : ‖A.comp P‖ ≤ C := calc
      ‖A.comp P‖ ≤ ‖A‖ * ‖P‖ := A.opNorm_comp_le P
      _ ≤ C * 1 := mul_le_mul hnA hnP (norm_nonneg _) hC
      _ = C := mul_one _
    have hJB : ‖J.comp B‖ ≤ 1 := calc
      ‖J.comp B‖ ≤ ‖J‖ * ‖B‖ := J.opNorm_comp_le B
      _ ≤ 1 * 1 := mul_le_mul hnJ hnB (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
    simpa only [mul_one] using mul_le_mul hAP hJB (norm_nonneg _) hC

/-- A diagonal means actual coordinatewise action, even on ℓ∞. -/
def IsInfinityDiagonal (D : EllInfinitySum X →L[𝕜] EllInfinitySum X) : Prop :=
  ∃ F : ℕ → X →L[𝕜] X, ∀ x n, D x n = F n (x n)

/-- Every diagonal on ℓ∞(X) satisfies the C-factorisation dichotomy when X
has C-PFP. This proves the full ℓ∞ case, but says nothing about reducing an
arbitrary operator to diagonal form. -/
theorem infinity_diagonal_dichotomy {C : ℝ} (hC : 1 ≤ C)
    (hX : HasCPFP 𝕜 X C) (D : EllInfinitySum X →L[𝕜] EllInfinitySum X)
    (hD : IsInfinityDiagonal D) :
    FactorsIdentityWith D (EllInfinitySum X) C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (EllInfinitySum X) - D)
        (EllInfinitySum X) C := by
  classical
  obtain ⟨F, hD⟩ := hD
  let S : Set ℕ := {n | FactorsIdentityWith (F n) X C}
  have hnonneg : 0 ≤ C := zero_le_one.trans hC
  by_cases hS : S.Infinite
  · let e : ℕ ↪ ℕ := (hS.natEmbedding S).trans (Function.Embedding.subtype S)
    left
    apply infinity_diagonal_factors_of_subsequence D F hD e hnonneg
    intro n
    exact (hS.natEmbedding S n).property
  · have hi : Sᶜ.Infinite := (Set.not_infinite.mp hS).infinite_compl
    let e : ℕ ↪ ℕ := (hi.natEmbedding Sᶜ).trans (Function.Embedding.subtype Sᶜ)
    right
    refine infinity_diagonal_factors_of_subsequence _
      (fun n => ContinuousLinearMap.id 𝕜 X - F n) ?_ e hnonneg ?_
    · intro x n
      change x n - D x n = x n - F n (x n)
      rw [hD]
    · intro n
      have hn : ¬ FactorsIdentityWith (F (e n)) X C := (hi.natEmbedding Sᶜ n).property
      exact (hX (F (e n))).resolve_left hn

end ThesisCommon
