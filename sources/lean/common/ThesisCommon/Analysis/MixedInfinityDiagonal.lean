import ThesisCommon.Analysis.MixedInfinityCompression
import ThesisCommon.Analysis.SupportingTree
import ThesisCommon.Analysis.SharpFactorization

/-! Actual coordinate multipliers and the two-level diagonal dichotomy on
X(ell_infinity). Diagonal action is specified on every vector. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

def infinityDiagonal (d : ℕ × ℕ → 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ p, ‖d p‖ ≤ C) :
    SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) :=
  diagonal (fun i => lpDiagonal ∞ (fun j => d (i, j) • ContinuousLinearMap.id 𝕜 𝕜)
    C hC (fun j => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hd (i, j)))
    C hC (fun _ => norm_lpDiagonal_le _ _ _ _)

@[simp] theorem infinityDiagonal_apply (d : ℕ × ℕ → 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ p, ‖d p‖ ≤ C) (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j : ℕ) :
    infinityDiagonal d C hC hd x i j = x i j * d (i, j) := by
  change d (i, j) * x i j = x i j * d (i, j)
  exact mul_comm _ _

theorem norm_infinityDiagonal_le (d : ℕ × ℕ → 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ p, ‖d p‖ ≤ C) :
    ‖infinityDiagonal (b := b) (hb := hb) d C hC hd‖ ≤ C := norm_diagonal_le _ _ _ _

theorem norm_infinityEntry_le
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j r s : ℕ) :
    ‖infinityEntry T i j r s‖ ≤ ‖T‖ := by
  let v : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) := single r (lp.single ∞ s (1 : 𝕜))
  have hv : ‖v‖ = 1 := by
    change ‖single (b := b) (hb := hb) r (lp.single ∞ s (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) ∞)‖ = 1
    rw [norm_single, lp.norm_single (by simp : (0 : ℝ≥0∞) < ∞), norm_one]
  calc
    _ ≤ ‖T v i‖ :=
      lp.norm_apply_le_norm ENNReal.top_ne_zero _ j
    _ ≤ ‖T v‖ := norm_apply_le _ i
    _ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
    _ = ‖T‖ := by rw [hv, mul_one]

def infinityDiagonalPart
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) :
    SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) :=
  infinityDiagonal (fun p => infinityEntry T p.1 p.2 p.1 p.2) ‖T‖ (norm_nonneg T)
    (fun p => norm_infinityEntry_le T p.1 p.2 p.1 p.2)

@[simp] theorem infinityDiagonalPart_apply
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞))
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j : ℕ) :
    infinityDiagonalPart T x i j = x i j * infinityEntry T i j i j :=
  infinityDiagonal_apply _ _ _ _ x i j

theorem norm_infinityDiagonalPart_le
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) : ‖infinityDiagonalPart T‖ ≤ ‖T‖ :=
  norm_infinityDiagonal_le _ _ _ _

def IsInfinityDiagonal
    (D : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) : Prop :=
  ∃ d : ℕ × ℕ → 𝕜, ∀ x i j, D x i j = x i j * d (i, j)

theorem isInfinityDiagonal_infinityDiagonalPart
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) : IsInfinityDiagonal (infinityDiagonalPart T) :=
  ⟨fun p => infinityEntry T p.1 p.2 p.1 p.2, infinityDiagonalPart_apply T⟩

theorem infinity_diagonal_factors (hs : b.HasSymmetricNorm)
    (D : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (d : ℕ × ℕ → 𝕜)
    (hD : ∀ x i j, D x i j = x i j * d (i, j))
    (hd : {i : ℕ | {j : ℕ | (1 / 2 : ℝ) ≤ ‖d (i, j)‖}.Infinite}.Infinite) :
    FactorsIdentityWith D (SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) 2 := by
  let a := hd.natEmbedding _
  let n : ℕ ↪ ℕ := a.trans (Function.Embedding.subtype _)
  have hinner (i : ℕ) : {j : ℕ | (1 / 2 : ℝ) ≤ ‖d (n i, j)‖}.Infinite := (a i).property
  let m : ℕ → ℕ ↪ ℕ := fun i =>
    (hinner i).natEmbedding _ |>.trans (Function.Embedding.subtype _)
  have hlarge (i j : ℕ) : (1 / 2 : ℝ) ≤ ‖d (n i, m i j)‖ :=
    ((hinner i).natEmbedding _ j).property
  have hne (i j : ℕ) : d (n i, m i j) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hlarge i j))
  have hinv (p : ℕ × ℕ) : ‖(d (n p.1, m p.1 p.2))⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hlarge p.1 p.2))]
    linarith [hlarge p.1 p.2]
  let R := infinityDiagonal (b := b) (hb := hb)
    (fun p => (d (n p.1, m p.1 p.2))⁻¹) 2 (by norm_num) hinv
  let A := infinityRestrict (hb := hb) hs n m
  let B := infinityExtend (hb := hb) hs n m
  have hR : ‖R‖ ≤ 2 := norm_infinityDiagonal_le _ _ _ _
  have hA : ‖A‖ ≤ 1 := norm_infinityRestrict_le hs n m
  have hB : ‖B‖ ≤ 1 := norm_infinityExtend_le hs n m
  refine ⟨R.comp A, B, ?_, ?_⟩
  · ext x i j
    change R (A (D (B x))) i j = x i j
    rw [show R (A (D (B x))) i j = A (D (B x)) i j * (d (n i, m i j))⁻¹ from
      infinityDiagonal_apply _ _ _ _ _ i j]
    change D (B x) (n i) (m i j) * (d (n i, m i j))⁻¹ = _
    rw [hD, show B x (n i) (m i j) = x i j from infinityExtend_apply_image hs n m x i j,
      mul_assoc, mul_inv_cancel₀ (hne i j), mul_one]
  · have hRA : ‖R.comp A‖ ≤ 2 := calc
      _ ≤ ‖R‖ * ‖A‖ := R.opNorm_comp_le A
      _ ≤ 2 * 1 := mul_le_mul hR hA (norm_nonneg _) (by norm_num)
      _ = 2 := mul_one _
    simpa only [mul_one] using mul_le_mul hRA hB (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)

theorem infinity_diagonal_dichotomy (hs : b.HasSymmetricNorm)
    (D : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (hD : IsInfinityDiagonal D) :
    FactorsIdentityWith D (SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) 2 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - D)
        (SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) 2 := by
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
  · exact Or.inl (infinity_diagonal_factors hs D d hD h)
  · right
    apply infinity_diagonal_factors hs _ (fun p => 1 - d p) _ h
    intro x i j
    change x i j - D x i j = _
    rw [hD, mul_sub, mul_one]

end SchauderSum
end ThesisCommon
