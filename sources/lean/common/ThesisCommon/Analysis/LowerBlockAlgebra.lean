import ThesisCommon.Analysis.SequenceBlockAlgebra

/-! Increasing contractive block compressions preserve genuine lower
triangular action on all sequence spaces, including bounded sequences. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lpPrefix_diagonal (F : ℕ → X →L[𝕜] Y) (hF : ∀ k, ‖F k‖ ≤ 1)
    (k : ℕ) (x : lp (fun _ : ℕ => X) p) :
    lpPrefix k (lpDiagonal p F 1 zero_le_one hF x) =
      lpDiagonal p F 1 zero_le_one hF (lpPrefix k x) := by
  ext j
  by_cases hj : j ≤ k <;> simp [lpPrefix_apply, hj]

theorem lpPrefix_blockInsert (e : ℕ ↪ ℕ) (he : StrictMono e)
    (G : ℕ → X →L[𝕜] Y) (hG : ∀ k, ‖G k‖ ≤ 1)
    (k : ℕ) (x : lp (fun _ : ℕ => X) p) :
    lpPrefix (e k) (lpBlockInsert p e G hG x) =
      lpBlockInsert p e G hG (lpPrefix k x) := by
  change lpPrefix (e k) (lpExtend (𝕜 := 𝕜) p e (lpDiagonal p G 1 zero_le_one hG x)) = _
  rw [lpPrefix_extend e he, lpPrefix_diagonal]
  rfl

theorem IsLpLowerPart.block_compression
    {S L : lp (fun _ : ℕ => Y) p →L[𝕜] lp (fun _ : ℕ => Y) p}
    (h : IsLpLowerPart S L) (e : ℕ ↪ ℕ) (he : StrictMono e)
    (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) :
    let T := ((lpBlockRead p e F hF).comp L).comp (lpBlockInsert p e G hG)
    IsLpLowerPart T T := by
  dsimp only
  intro x k
  change F k (L (lpBlockInsert p e G hG x) (e k)) =
    F k (L (lpBlockInsert p e G hG (lpPrefix k x)) (e k))
  rw [h.self_lowerPart (lpBlockInsert p e G hG x) (e k), lpPrefix_blockInsert e he]

end ThesisCommon
