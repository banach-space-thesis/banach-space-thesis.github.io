import ThesisCommon.Analysis.LpUpperTriangularParts
import ThesisCommon.Analysis.SequenceBlockAlgebra

/-! Upper column support is preserved by increasing block compressions.
A genuine lower part of an operator with upper column support is diagonal.
The latter assertion is valid even at infinity, since the lower part is
specified on every input by finite-prefix action. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem isLpUpperPart_self_iff
    (U : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) :
    IsLpUpperPart U U ↔ ∀ i j, j < i → lpEntry U i j = 0 := by
  constructor
  · intro h i j hij
    simpa only [if_neg (by omega : ¬ i ≤ j)] using h.entry i j
  · intro h j x
    apply Subtype.ext
    funext i
    change U (lp.single p j x) i = if i ≤ j then U (lp.single p j x) i else 0
    by_cases hij : i ≤ j
    · rw [if_pos hij]
    · rw [if_neg hij]
      exact DFunLike.congr_fun (h i j (by omega)) x

theorem IsLpUpperPart.self_upperPart
    {S U : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p}
    (h : IsLpUpperPart S U) : IsLpUpperPart U U := by
  apply (isLpUpperPart_self_iff U).2
  intro i j hij
  simpa only [if_neg (by omega : ¬ i ≤ j)] using h.entry i j

theorem IsLpUpperPart.block_compression
    {U : lp (fun _ : ℕ => Y) p →L[𝕜] lp (fun _ : ℕ => Y) p}
    (h : IsLpUpperPart U U) (e : ℕ ↪ ℕ) (he : StrictMono e)
    (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) :
    let S := ((lpBlockRead p e F hF).comp U).comp (lpBlockInsert p e G hG)
    IsLpUpperPart S S := by
  apply (isLpUpperPart_self_iff _).2
  intro i j hij
  rw [lpEntry_block_compression, (isLpUpperPart_self_iff U).1 h _ _ (he hij)]
  simp

theorem IsLpLowerPart.eq_diagonal_of_upper
    {S L : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p}
    (hL : IsLpLowerPart S L) (hS : IsLpUpperPart S S) : L = lpDiagonalPart S := by
  ext x k
  change L x k = lpEntry S k k (x k)
  rw [hL.matrix_formula, Finset.sum_range_succ]
  have hz : (∑ j ∈ Finset.range k, S (lp.single p j (x j)) k) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact DFunLike.congr_fun ((isLpUpperPart_self_iff S).1 hS k j (Finset.mem_range.mp hj)) (x j)
  rw [hz, zero_add]
  rfl

end ThesisCommon
