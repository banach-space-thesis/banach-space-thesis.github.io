import ThesisCommon.Analysis.CotypeLowerTriangular

/-! Prefix and increasing-compression identities for diagonal reduction. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[simp] theorem lpPrefix_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (k : ℕ) (x : lp (fun _ : ℕ => X) p) (n : ℕ) :
    lpPrefix k x n = if n ≤ k then x n else 0 := rfl

@[simp] theorem cZeroPrefix_apply (k : ℕ) (x : CZeroSum X) (n : ℕ) :
    cZeroPrefix k x n = if n ≤ k then x n else 0 := rfl

/-- Prefix truncation is idempotent. -/
theorem lpPrefix_idempotent {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (k : ℕ) (x : lp (fun _ : ℕ => X) p) : lpPrefix k (lpPrefix k x) = lpPrefix k x := by
  ext n
  by_cases hn : n ≤ k <;> simp [hn]

theorem cZeroPrefix_idempotent (k : ℕ) (x : CZeroSum X) :
    cZeroPrefix k (cZeroPrefix k x) = cZeroPrefix k x := by
  ext n
  by_cases hn : n ≤ k <;> simp [hn]

/-- Inserted sequences vanish off the embedding's range. -/
theorem lpExtend_apply_off_range {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (e : ℕ ↪ ℕ) (x : lp (fun _ : ℕ => X) p) {n : ℕ} (hn : n ∉ Set.range e) :
    lpExtend (𝕜 := 𝕜) p e x n = 0 := by
  change Function.extend e x 0 n = 0
  simp only [Function.extend_apply' _ _ _ hn, Pi.zero_apply]

theorem cZeroExtend_apply_off_range (e : ℕ ↪ ℕ) (x : CZeroSum X)
    {n : ℕ} (hn : n ∉ Set.range e) : cZeroExtend (𝕜 := 𝕜) e x n = 0 := by
  change Function.extend e x 0 n = 0
  simp only [Function.extend_apply' _ _ _ hn, Pi.zero_apply]

/-- Increasing insertion commutes with the corresponding prefix truncations. -/
theorem lpPrefix_extend {p : ℝ≥0∞} [Fact (1 ≤ p)] (e : ℕ ↪ ℕ) (he : StrictMono e)
    (k : ℕ) (x : lp (fun _ : ℕ => X) p) :
    lpPrefix (e k) (lpExtend (𝕜 := 𝕜) p e x) = lpExtend (𝕜 := 𝕜) p e (lpPrefix k x) := by
  ext n
  by_cases hn : n ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hn
    simp only [lpPrefix_apply, lpExtend_apply_image, he.le_iff_le]
  · simp only [lpPrefix_apply, lpExtend_apply_off_range e _ hn, ite_self]

theorem cZeroPrefix_extend (e : ℕ ↪ ℕ) (he : StrictMono e) (k : ℕ) (x : CZeroSum X) :
    cZeroPrefix (e k) (cZeroExtend (𝕜 := 𝕜) e x) = cZeroExtend (𝕜 := 𝕜) e (cZeroPrefix k x) := by
  ext n
  by_cases hn : n ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hn
    simp only [cZeroPrefix_apply, cZeroExtend_apply_image, he.le_iff_le]
  · simp only [cZeroPrefix_apply, cZeroExtend_apply_off_range e _ hn, ite_self]

/-- A lower part has lower-triangular action relative to itself. -/
theorem IsLpLowerPart.self_lowerPart {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {S L : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p}
    (h : IsLpLowerPart S L) : IsLpLowerPart L L := by
  intro x k
  rw [h x k, h (lpPrefix k x) k, lpPrefix_idempotent]

theorem IsCZeroLowerPart.self_lowerPart {S L : CZeroSum X →L[𝕜] CZeroSum X}
    (h : IsCZeroLowerPart S L) : IsCZeroLowerPart L L := by
  intro x k
  rw [h x k, h (cZeroPrefix k x) k, cZeroPrefix_idempotent]

/-- An increasing coordinate compression of a lower-triangular operator is lower. -/
theorem IsLpLowerPart.compression {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {S L : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p}
    (h : IsLpLowerPart S L) (e : ℕ ↪ ℕ) (he : StrictMono e) :
    IsLpLowerPart (((lpRestrict p e).comp L).comp (lpExtend p e))
      (((lpRestrict p e).comp L).comp (lpExtend p e)) := by
  intro x k
  change L (lpExtend p e x) (e k) = L (lpExtend p e (lpPrefix k x)) (e k)
  rw [h.self_lowerPart (lpExtend p e x) (e k), lpPrefix_extend e he]

theorem IsCZeroLowerPart.compression {S L : CZeroSum X →L[𝕜] CZeroSum X}
    (h : IsCZeroLowerPart S L) (e : ℕ ↪ ℕ) (he : StrictMono e) :
    IsCZeroLowerPart (((cZeroRestrict e).comp L).comp (cZeroExtend e))
      (((cZeroRestrict e).comp L).comp (cZeroExtend e)) := by
  intro x k
  change L (cZeroExtend e x) (e k) = L (cZeroExtend e (cZeroPrefix k x)) (e k)
  rw [h.self_lowerPart (cZeroExtend e x) (e k), cZeroPrefix_extend e he]

end ThesisCommon
