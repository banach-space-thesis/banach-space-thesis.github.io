import ThesisCommon.Analysis.SequenceEntryOperators
import ThesisCommon.Analysis.SequencePrefixAlgebra

/-! Entry and diagonal identities under increasing coordinate compression. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Inserting a one-coordinate vector gives the corresponding image coordinate. -/
theorem lpExtend_single (e : ℕ ↪ ℕ) (n : ℕ) (x : X) :
    lpExtend (𝕜 := 𝕜) p e (lp.single p n x) = lp.single p (e n) x := by
  ext m
  by_cases hm : m ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hm
    rw [lpExtend_apply_image]
    by_cases hj : j = n
    · subst j
      simp
    · have he : e j ≠ e n := fun h => hj (e.injective h)
      simp [hj, he]
  · have hmn : m ≠ e n := fun heq => hm ⟨n, heq.symm⟩
    simp [lpExtend_apply_off_range e _ hm, hmn]

theorem cZeroExtend_single (e : ℕ ↪ ℕ) (n : ℕ) (x : X) :
    cZeroExtend (𝕜 := 𝕜) e (cZeroSingle n x) = cZeroSingle (e n) x := by
  ext m
  by_cases hm : m ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hm
    rw [cZeroExtend_apply_image]
    simp only [cZeroSingle_apply, e.injective.eq_iff]
  · have hmn : m ≠ e n := fun heq => hm ⟨n, heq.symm⟩
    simp only [cZeroExtend_apply_off_range e _ hm, cZeroSingle_apply, if_neg hmn]

theorem lpPrefix_single {k n : ℕ} (hn : n ≤ k) (x : X) :
    lpPrefix k (lp.single p n x) = lp.single p n x := by
  ext m
  by_cases hm : m ≤ k
  · simp [hm]
  · have hmn : m ≠ n := by omega
    simp [hm, hmn]

theorem cZeroPrefix_single {k n : ℕ} (hn : n ≤ k) (x : X) :
    cZeroPrefix k (cZeroSingle n x) = cZeroSingle n x := by
  ext m
  by_cases hm : m ≤ k
  · simp [hm]
  · have hmn : m ≠ n := by omega
    simp [hm, hmn]

/-- Taking a lower part preserves every diagonal entry. -/
theorem IsLpLowerPart.diagonal_entry
    {S L : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p}
    (h : IsLpLowerPart S L) (n : ℕ) : lpEntry L n n = lpEntry S n n := by
  ext x
  change L (lp.single p n x) n = S (lp.single p n x) n
  rw [h, lpPrefix_single le_rfl]

theorem IsCZeroLowerPart.diagonal_entry {S L : CZeroSum X →L[𝕜] CZeroSum X}
    (h : IsCZeroLowerPart S L) (n : ℕ) : cZeroEntry L n n = cZeroEntry S n n := by
  ext x
  change L (cZeroSingle n x) n = S (cZeroSingle n x) n
  rw [h, cZeroPrefix_single le_rfl]

/-- Coordinate entries of a compression are the corresponding original entries. -/
theorem lpEntry_compression (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    (e : ℕ ↪ ℕ) (m n : ℕ) :
    lpEntry (((lpRestrict p e).comp T).comp (lpExtend p e)) m n = lpEntry T (e m) (e n) := by
  ext x
  change T (lpExtend (𝕜 := 𝕜) p e (lp.single p n x)) (e m) = T (lp.single p (e n) x) (e m)
  rw [lpExtend_single]

theorem cZeroEntry_compression (T : CZeroSum X →L[𝕜] CZeroSum X)
    (e : ℕ ↪ ℕ) (m n : ℕ) :
    cZeroEntry (((cZeroRestrict e).comp T).comp (cZeroExtend e)) m n = cZeroEntry T (e m) (e n) := by
  ext x
  change T (cZeroExtend (𝕜 := 𝕜) e (cZeroSingle n x)) (e m) = T (cZeroSingle (e n) x) (e m)
  rw [cZeroExtend_single]

/-- Nested coordinate compressions are the compression by the composed embedding. -/
theorem lpCompression_composition
    (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) (e f : ℕ ↪ ℕ) :
    ((lpRestrict p f).comp (((lpRestrict p e).comp T).comp (lpExtend p e))).comp
      (lpExtend p f) = ((lpRestrict p (f.trans e)).comp T).comp (lpExtend p (f.trans e)) := by
  ext x k
  exact congrArg (fun y => T y (e (f k)))
    (congrArg (fun A : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p => A x)
      (lpExtend_comp f e))

theorem cZeroCompression_composition (T : CZeroSum X →L[𝕜] CZeroSum X) (e f : ℕ ↪ ℕ) :
    ((cZeroRestrict f).comp (((cZeroRestrict e).comp T).comp (cZeroExtend e))).comp
      (cZeroExtend f) = ((cZeroRestrict (f.trans e)).comp T).comp (cZeroExtend (f.trans e)) := by
  ext x k
  exact congrArg (fun y => T y (e (f k)))
    (congrArg (fun A : CZeroSum X →L[𝕜] CZeroSum X => A x) (cZeroExtend_comp f e))

/-- A compression by contractions does not increase the operator norm. -/
theorem norm_contractive_compression (T A B : X →L[𝕜] X)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖(A.comp T).comp B‖ ≤ ‖T‖ := by
  have hAT : ‖A.comp T‖ ≤ ‖T‖ := calc
    _ ≤ ‖A‖ * ‖T‖ := A.opNorm_comp_le T
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg T)
    _ = ‖T‖ := one_mul _
  calc
    _ ≤ ‖A.comp T‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T‖ * 1 := mul_le_mul hAT hB (norm_nonneg B) (norm_nonneg T)
    _ = ‖T‖ := mul_one _

end ThesisCommon
