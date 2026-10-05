import ThesisCommon.Analysis.OrdinalBackwardSelection
import ThesisCommon.Analysis.LpSummableRows
import ThesisCommon.Analysis.SequenceBlockAlgebra
import ThesisCommon.Analysis.DualCotypeDiagonalReduction

/-! LPCK ordinal row selection and whole lower-part approximation on characteristic-one compact ordinal intervals, including infinity. -/
noncomputable section
open scoped ENNReal
universe u
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α η a : Ordinal.{u}}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem ordinal_lp_lower_triangular_blocks (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → OrdinalClosedCopy α α), StrictMono e ∧
      ∀ (G : ℕ → OrdinalContinuous 𝕜 α →L[𝕜] OrdinalContinuous 𝕜 α) (hG : ∀ k, ‖G k‖ ≤ 1),
      ∃ L : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p,
        let S := ((lpBlockRead p e (fun k => ordinalCopyRead (𝕜 := 𝕜) (c k))
          (fun k => norm_ordinalCopyRead_le (𝕜 := 𝕜) (c k))).comp T).comp (lpBlockInsert p e G hG)
        ‖S-L‖ < ε ∧ IsLpLowerPart S L := by
  let δ : ℕ → ℝ := fun k => (ε/4) * (1/2 : ℝ)^k
  obtain ⟨e, c, he, hs⟩ := ordinal_lp_backward_selection hD hp T δ
    (fun _ => by dsimp [δ]; positivity)
  refine ⟨e, c, he, ?_⟩
  intro G hG
  let S := ((lpBlockRead p e (fun k => ordinalCopyRead (𝕜 := 𝕜) (c k))
    (fun k => norm_ordinalCopyRead_le (𝕜 := 𝕜) (c k))).comp T).comp (lpBlockInsert p e G hG)
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

theorem ordinal_lp_lower_triangular (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → OrdinalClosedCopy α α)
      (L : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p),
      StrictMono e ∧
      let S := ((lpBlockRead p e (fun k => ordinalCopyRead (𝕜 := 𝕜) (c k))
        (fun k => norm_ordinalCopyRead_le (𝕜 := 𝕜) (c k))).comp T).comp (lpExtend p e)
      ‖S-L‖ < ε ∧ IsLpLowerPart S L := by
  obtain ⟨e, c, he, hs⟩ := ordinal_lp_lower_triangular_blocks hD hp T hε
  obtain ⟨L, hL⟩ := hs (fun _ => ContinuousLinearMap.id 𝕜 (OrdinalContinuous 𝕜 α))
    (fun _ => ContinuousLinearMap.norm_id_le)
  exact ⟨e, c, L, he, by simpa only [lpBlockInsert_id] using hL⟩

theorem ordinal_lp_lower_retraction (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → OrdinalClosedCopy α α)
      (L : lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p →L[𝕜] lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p),
      StrictMono e ∧
      let A := lpBlockRead p e (fun k => ordinalCopyRead (𝕜 := 𝕜) (c k)) (fun k => norm_ordinalCopyRead_le (𝕜 := 𝕜) (c k))
      let B := lpBlockInsert p e (fun k => ordinalCopyInsert (𝕜 := 𝕜) (c k)) (fun k => norm_ordinalCopyInsert_le (𝕜 := 𝕜) (c k))
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖(A.comp T).comp B-L‖ < ε ∧
        IsLpLowerPart ((A.comp T).comp B) L := by
  obtain ⟨e, c, he, hs⟩ := ordinal_lp_lower_triangular_blocks hD hp T hε
  obtain ⟨L, hL⟩ := hs (fun k => ordinalCopyInsert (𝕜 := 𝕜) (c k)) (fun k => norm_ordinalCopyInsert_le (𝕜 := 𝕜) (c k))
  exact ⟨e, c, L, he, lpBlockRead_comp_insert p e _ _ _ _
    (fun k => ordinalCopyRead_comp_insert (c k)), hL⟩

end ThesisCommon

