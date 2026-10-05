import ThesisCommon.Analysis.SchauderSumCompression
import ThesisCommon.Analysis.SchauderSumBasis
import ThesisCommon.Analysis.SchauderLargeDiagonal
import ThesisCommon.Analysis.SupportingTree

/-! Canonical product-coordinate compressions and the diagonal dichotomy
on X(Y), for symmetric outer and inner norms. The product basis need not
itself be symmetric. An infinite family of infinite rows supplies the copy.
-/
noncomputable section
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem exists_product_compression (hs : b.HasSymmetricNorm)
    (c : NormalizedSchauderBasis 𝕜 Y) (hc : c.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) :
    ∃ A B : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Y,
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ p : ℕ × ℕ, B (productVector c p) = productVector c (n p.1, m p.1 p.2)) ∧
      ∀ (p : ℕ × ℕ) x, productCoordinate c p (A x) =
        productCoordinate c (n p.1, m p.1 p.2) x := by
  choose R E hRE hR hE hEv hRc using fun i => c.exists_subsequence_compression hc (m i)
  obtain ⟨A, B, hAB, hA, hB, hBv, hAc⟩ :=
    exists_reindexed_compression (hb := hb) hs n R E hRE hR hE
  refine ⟨A, B, hAB, hA, hB, ?_, ?_⟩
  · intro p
    simp only [productVector, hBv, hEv]
  · intro p x
    change c.coord p.2 (A x p.1) = c.coord (m p.1 p.2) (x (n p.1))
    rw [hAc, hRc]

/-- Diagonal on every actual product vector, without a symmetry assertion
about the pair-enumerated basis. -/
def IsProductDiagonal (c : NormalizedSchauderBasis 𝕜 Y)
    (D : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Y) : Prop :=
  ∃ d : ℕ × ℕ → 𝕜, ∀ p, D (productVector c p) = d p • productVector c p

theorem product_diagonal_factors (hs : b.HasSymmetricNorm)
    (c : NormalizedSchauderBasis 𝕜 Y) (hc : c.HasSymmetricNorm)
    (D : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Y) (d : ℕ × ℕ → 𝕜)
    (hD : ∀ p, D (productVector c p) = d p • productVector c p)
    (hd : {i : ℕ | {j : ℕ | (1 / 2 : ℝ) ≤ ‖d (i, j)‖}.Infinite}.Infinite) :
    FactorsIdentityWith D (SchauderSum b hb Y) 2 := by
  let a := hd.natEmbedding _
  let n : ℕ ↪ ℕ := a.trans (Function.Embedding.subtype _)
  have hinner (i : ℕ) : {j : ℕ | (1 / 2 : ℝ) ≤ ‖d (n i, j)‖}.Infinite := (a i).property
  let m : ℕ → ℕ ↪ ℕ := fun i =>
    (hinner i).natEmbedding _ |>.trans (Function.Embedding.subtype _)
  obtain ⟨A, B, hAB, hA, hB, hBv, _⟩ := exists_product_compression hs c hc n m
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let c' := productBasis (b := b) (hb := hb) c hc.1 e
  have hcomp (k : ℕ) : ((A.comp D).comp B) (c'.vector k) =
      d (n (e k).1, m (e k).1 (e k).2) • c'.vector k := by
    change A (D (B (productVector c (e k)))) = _
    rw [hBv, hD, map_smul]
    have hh := DFunLike.congr_fun hAB (productVector c (e k))
    change A (B (productVector c (e k))) = productVector c (e k) at hh
    rw [hBv] at hh
    rw [hh]
    rfl
  have hf := c'.diagonal_factors_of_half_le (productBasis_oneUnconditional c hc.1 e)
    ((A.comp D).comp B) _ hcomp (fun k => ((hinner (e k).1).natEmbedding _ (e k).2).property)
  apply (hf.of_compression A B).mono
  have hh : ‖A‖ * ‖B‖ ≤ 1 := by
    simpa only [mul_one] using mul_le_mul hA hB (norm_nonneg _) zero_le_one
  linarith

theorem product_diagonal_dichotomy (hs : b.HasSymmetricNorm)
    (c : NormalizedSchauderBasis 𝕜 Y) (hc : c.HasSymmetricNorm)
    (D : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Y) (hD : IsProductDiagonal c D) :
    FactorsIdentityWith D (SchauderSum b hb Y) 2 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - D) (SchauderSum b hb Y) 2 := by
  obtain ⟨d, hD⟩ := hD
  have hlarge (t : Fin 2 → ℕ) :
      (1 / 2 : ℝ) ≤ ‖d (t 0, t 1)‖ ∨ (1 / 2 : ℝ) ≤ ‖1 - d (t 0, t 1)‖ := by
    have hh := norm_add_le (d (t 0, t 1)) (1 - d (t 0, t 1))
    rw [add_sub_cancel, norm_one] at hh
    by_cases h : (1 / 2 : ℝ) ≤ ‖d (t 0, t 1)‖
    · exact Or.inl h
    · right; linarith
  have h := infinitelySupported_or 2 _ _ hlarge
  change {i : ℕ | {j : ℕ | (1 / 2 : ℝ) ≤ ‖d (i, j)‖}.Infinite}.Infinite ∨
    {i : ℕ | {j : ℕ | (1 / 2 : ℝ) ≤ ‖1 - d (i, j)‖}.Infinite}.Infinite at h
  rcases h with h | h
  · exact Or.inl (product_diagonal_factors hs c hc D d hD h)
  · right
    apply product_diagonal_factors hs c hc _ (fun p => 1 - d p) _ h
    intro p
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hD,
      sub_smul, one_smul]

end SchauderSum
end ThesisCommon
