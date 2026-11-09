import SurveyStatements.P5CaponLocalizedInput
import SurveyStatements.P5RealScalarHaar

/-! Finite localized Capon tests commute with any prescribed Haar action.
The codomain may be an arbitrary real normed space, including an RCLike
mixed-norm space viewed over the real scalars. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open P5Support
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem caponLocalized_tensor_level_of_haar_cut
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (F G : MixedNorm ℝ p →L[ℝ] E)
    (hFG : ∀ I J : DyadicIndex,
      m ≤ I.1 → lpHaarCell I.1 I.2 ⊆ lpHaarCell m i₀ →
      m ≤ J.1 → lpHaarCell J.1 J.2 ⊆ lpHaarCell m j₀ →
      F (productHaar ℝ p I J) = if J.1 ≤ I.1 then G (productHaar ℝ p I J) else 0)
    (k n : ℕ) :
    F (tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
      (caponLocalRademacher m i₀ p n)) =
      if k ≤ n then G (tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
        (caponLocalRademacher m i₀ p n)) else 0 := by
  have hlevel : tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
      (caponLocalRademacher m i₀ p n) =
      ∑ l ∈ caponLocalCells m i₀ n,
        productHaar ℝ p ⟨m + n, l⟩ (caponLocalInnerIndex m j₀ k) := by
    rw [caponLocalRademacher, map_sum]
    rfl
  rw [hlevel, map_sum]
  have hterm (l : Fin (2 ^ (m + n))) (hl : l ∈ caponLocalCells m i₀ n) :=
    hFG ⟨m + n, l⟩ (caponLocalInnerIndex m j₀ k) (by change m ≤ m + n; omega)
      (caponLocalCells_contained m i₀ n l hl) (by change m ≤ m + k; omega)
      (caponLocalInnerIndex_contained m j₀ k)
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, map_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact (hterm l hl).trans (if_pos (Nat.add_le_add_left hkn m))
  · rw [if_neg hkn]
    apply Finset.sum_eq_zero
    intro l hl
    exact (hterm l hl).trans (if_neg (fun h => hkn (Nat.le_of_add_le_add_left h)))

theorem caponLocalizedInput_image_of_haar_cut
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (F G : MixedNorm ℝ p →L[ℝ] E)
    (hFG : ∀ I J : DyadicIndex,
      m ≤ I.1 → lpHaarCell I.1 I.2 ⊆ lpHaarCell m i₀ →
      m ≤ J.1 → lpHaarCell J.1 J.2 ⊆ lpHaarCell m j₀ →
      F (productHaar ℝ p I J) = if J.1 ≤ I.1 then G (productHaar ℝ p I J) else 0)
    (N : ℕ) :
    F (caponLocalizedInput m i₀ j₀ p N) = G (caponLocalizedImage m i₀ j₀ p N) := by
  rw [caponLocalizedInput_eq_level_sum, caponLocalizedImage, map_smul, map_smul]
  congr 1
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, map_smul]
  congr 1
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [caponLocalized_tensor_level_of_haar_cut m i₀ j₀ F G hFG]
  split <;> simp only [*, map_zero]

theorem caponLocalized_tensor_level_of_haar_agreement
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (F G : MixedNorm ℝ p →L[ℝ] E)
    (hFG : ∀ I J : DyadicIndex,
      m ≤ I.1 → lpHaarCell I.1 I.2 ⊆ lpHaarCell m i₀ →
      m ≤ J.1 → lpHaarCell J.1 J.2 ⊆ lpHaarCell m j₀ →
      F (productHaar ℝ p I J) = G (productHaar ℝ p I J))
    (k n : ℕ) :
    F (tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
      (caponLocalRademacher m i₀ p n)) =
      G (tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
        (caponLocalRademacher m i₀ p n)) := by
  rw [caponLocalRademacher, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact hFG ⟨m + n, l⟩ (caponLocalInnerIndex m j₀ k) (by change m ≤ m + n; omega)
    (caponLocalCells_contained m i₀ n l hl) (by change m ≤ m + k; omega)
    (caponLocalInnerIndex_contained m j₀ k)

theorem caponLocalizedImage_map_of_haar_agreement
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (F G : MixedNorm ℝ p →L[ℝ] E)
    (hFG : ∀ I J : DyadicIndex,
      m ≤ I.1 → lpHaarCell I.1 I.2 ⊆ lpHaarCell m i₀ →
      m ≤ J.1 → lpHaarCell J.1 J.2 ⊆ lpHaarCell m j₀ →
      F (productHaar ℝ p I J) = G (productHaar ℝ p I J))
    (N : ℕ) :
    F (caponLocalizedImage m i₀ j₀ p N) = G (caponLocalizedImage m i₀ j₀ p N) := by
  rw [caponLocalizedImage, map_smul, map_smul]
  congr 1
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, map_smul]
  congr 1
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  split
  · exact caponLocalized_tensor_level_of_haar_agreement m i₀ j₀ F G hFG k n
  · rw [map_zero, map_zero]

theorem caponLocalized_embedded_input_image
    (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (F M : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hFM : ∀ I J : DyadicIndex,
      m ≤ I.1 → lpHaarCell I.1 I.2 ⊆ lpHaarCell m i₀ →
      m ≤ J.1 → lpHaarCell J.1 J.2 ⊆ lpHaarCell m j₀ →
      F (productHaar 𝕜 p I J) = if J.1 ≤ I.1 then M (productHaar 𝕜 p I J) else 0)
    (N : ℕ) :
    F (RealScalar.embedding 𝕜 p (caponLocalizedInput m i₀ j₀ p N)) =
      M (RealScalar.embedding 𝕜 p (caponLocalizedImage m i₀ j₀ p N)) := by
  apply caponLocalizedInput_image_of_haar_cut m i₀ j₀
    ((F.restrictScalars ℝ).comp (RealScalar.embedding 𝕜 p))
    ((M.restrictScalars ℝ).comp (RealScalar.embedding 𝕜 p))
  intro I J hI hIsub hJ hJsub
  change F (RealScalar.embedding 𝕜 p (productHaar ℝ p I J)) =
    if J.1 ≤ I.1 then M (RealScalar.embedding 𝕜 p (productHaar ℝ p I J)) else 0
  simp only [RealScalar.embedding_productHaar]
  exact hFM I J hI hIsub hJ hJsub

end SurveyStatements.P5
