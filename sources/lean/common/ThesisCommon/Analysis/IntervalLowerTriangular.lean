import ThesisCommon.Analysis.IntervalBackwardSelection
import ThesisCommon.Analysis.LpSummableRows
import ThesisCommon.Analysis.SequenceBlockAlgebra
import ThesisCommon.Analysis.DualCotypeDiagonalReduction

/-! LPCK Proposition 3.13 for C[0,1]. Closed subintervals are identified
isometrically with [0,1]. The actual bounded lower part has the finite-row
formula on every input, including all bounded sequences when p = infinity.
The selected rows also work after arbitrary contractive block insertions. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem interval_lp_lower_triangular_blocks (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → NondegenerateUnitSubinterval), StrictMono e ∧
      ∀ (G : ℕ → IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (hG : ∀ k, ‖G k‖ ≤ 1),
      ∃ L : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p,
        let S := ((lpBlockRead p e (fun k => intervalRead (𝕜 := 𝕜) (c k))
          (fun k => norm_intervalRead_le (𝕜 := 𝕜) (c k))).comp T).comp (lpBlockInsert p e G hG)
        ‖S-L‖ < ε ∧ IsLpLowerPart S L := by
  let δ : ℕ → ℝ := fun k => (ε/4) * (1/2 : ℝ)^k
  obtain ⟨e, c, he, hs⟩ := interval_lp_backward_selection hp T δ
    (fun _ => by dsimp [δ]; positivity)
  refine ⟨e, c, he, ?_⟩
  intro G hG
  let S := ((lpBlockRead p e (fun k => intervalRead (𝕜 := 𝕜) (c k))
    (fun k => norm_intervalRead_le (𝕜 := 𝕜) (c k))).comp T).comp (lpBlockInsert p e G hG)
  have htail : ∀ k, ‖((lpCoordinate p k).comp S).comp
      (lpExtend p (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ δ k := by
    intro k
    exact (lpBlockCompression_tail_bound p T e _ G _ hG k).trans (hs k)
  obtain ⟨L, hL, hpart⟩ := exists_lp_lower_part_of_summable_tails S
    (summable_geometric_two.mul_left (ε/4)) htail
  refine ⟨L, ?_, hpart⟩
  apply hL.trans_lt
  change (∑' k, (ε/4) * (1/2 : ℝ)^k) < ε
  rw [(hasSum_geometric_two.mul_left (ε/4)).tsum_eq]
  linarith

theorem interval_lp_lower_triangular (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → NondegenerateUnitSubinterval)
      (L : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p),
      StrictMono e ∧
      let S := ((lpBlockRead p e (fun k => intervalRead (𝕜 := 𝕜) (c k))
        (fun k => norm_intervalRead_le (𝕜 := 𝕜) (c k))).comp T).comp (lpExtend p e)
      ‖S-L‖ < ε ∧ IsLpLowerPart S L := by
  obtain ⟨e, c, he, hs⟩ := interval_lp_lower_triangular_blocks hp T hε
  obtain ⟨L, hL⟩ := hs (fun _ => ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜))
    (fun _ => ContinuousLinearMap.norm_id_le)
  exact ⟨e, c, L, he, by simpa only [lpBlockInsert_id] using hL⟩

theorem interval_lp_lower_retraction (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → NondegenerateUnitSubinterval)
      (L : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p),
      StrictMono e ∧
      let A := lpBlockRead p e (fun k => intervalRead (𝕜 := 𝕜) (c k)) (fun k => norm_intervalRead_le (𝕜 := 𝕜) (c k))
      let B := lpBlockInsert p e (fun k => intervalInsert (𝕜 := 𝕜) (c k)) (fun k => norm_intervalInsert_le (𝕜 := 𝕜) (c k))
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖(A.comp T).comp B-L‖ < ε ∧
        IsLpLowerPart ((A.comp T).comp B) L := by
  obtain ⟨e, c, he, hs⟩ := interval_lp_lower_triangular_blocks hp T hε
  obtain ⟨L, hL⟩ := hs (fun k => intervalInsert (𝕜 := 𝕜) (c k)) (fun k => norm_intervalInsert_le (𝕜 := 𝕜) (c k))
  exact ⟨e, c, L, he, lpBlockRead_comp_insert p e _ _ _ _
    (fun k => intervalRead_comp_insert (c k)), hL⟩

end ThesisCommon

