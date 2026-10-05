import ThesisCommon.Analysis.CZeroLpUpperSelection
import ThesisCommon.Analysis.LpSummableColumns
import ThesisCommon.Analysis.CZeroInnerPointRetractions
import ThesisCommon.Analysis.SequenceBlockColumnBounds

/-! The full LPCK Lemma 3.10. Both index sequences increase; the maps are
actual point restrictions and insertions, and the upper part is bounded. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_cZero_upper_triangular (hp : p ≠ ∞)
    (T : lp (fun _ : ℕ => CZeroSum X) p →L[𝕜] lp (fun _ : ℕ => CZeroSum X) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (m : ℕ → ℕ)
      (U : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p),
      StrictMono e ∧ StrictMono m ∧
      ‖((lpCZeroPointRead p e m).comp T).comp (lpCZeroPointInsert p e m) - U‖ < ε ∧
      IsLpUpperPart (((lpCZeroPointRead p e m).comp T).comp (lpCZeroPointInsert p e m)) U := by
  let δ : ℕ → ℝ := fun k => (ε/4) * (1/2 : ℝ)^k
  obtain ⟨e, m, he, hm, hs⟩ := lp_cZero_upper_selection hp T δ
    (fun _ => by dsimp [δ]; positivity)
  let S := ((lpCZeroPointRead p e m).comp T).comp (lpCZeroPointInsert p e m)
  have htail : ∀ j, ‖((lpRestrict p (coordinateTail (Function.Embedding.refl ℕ) j)).comp S).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p j)‖ ≤ δ j := by
    intro j
    exact (lpBlockCompression_column_tail_bound p T e
      (fun k => cZeroCoordinate (m k)) (fun k => cZeroSingleCLM (m k))
      (fun k => norm_cZeroCoordinate_le (m k)) (fun k => norm_cZeroSingleCLM_le (m k)) j).trans
        (hs j).le
  obtain ⟨U, hU, hpart⟩ := exists_lp_upper_part_of_summable_tails S
    (summable_geometric_two.mul_left (ε/4)) htail
  refine ⟨e, m, U, he, hm, ?_, hpart⟩
  apply hU.trans_lt
  change (∑' j, (ε/4) * (1/2 : ℝ)^j) < ε
  rw [(hasSum_geometric_two.mul_left (ε/4)).tsum_eq]
  linarith

end ThesisCommon
