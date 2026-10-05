import ThesisCommon.Analysis.DualEllOneForwardSelection
import ThesisCommon.Analysis.LpUpperTriangularParts
import ThesisCommon.Analysis.SequenceEntryAlgebra

/-! The finite-p forward selection and upper-triangular construction from the proved Schur argument on an actual ell-one dual. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_upper_triangular_of_dual_equiv_ellOne (hp : p ≠ ∞)
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (U : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p),
      StrictMono e ∧ ‖((lpRestrict p e).comp T).comp (lpExtend p e) - U‖ < ε ∧
      IsLpUpperPart (((lpRestrict p e).comp T).comp (lpExtend p e)) U := by
  let δ : ℕ → ℝ := fun j => (ε/4) * (1/2 : ℝ)^j
  obtain ⟨e, he, hs⟩ := lp_forward_column_selection_of_dual_equiv_ellOne hp d T δ
    (fun _ => by dsimp [δ]; positivity)
  let S := ((lpRestrict p e).comp T).comp (lpExtend p e)
  have hcol : ∀ j, Summable (fun k => ‖lpEntry S (j+1+k) j‖) := by
    intro j
    simpa only [S, lpEntry_compression] using (hs j).1
  have hbound : ∀ j, (∑' k, ‖lpEntry S (j+1+k) j‖) ≤ δ j := by
    intro j
    simpa only [S, lpEntry_compression] using (hs j).2.le
  obtain ⟨U, hU, hpart⟩ := exists_lp_upper_part_of_summable_columns S
    (summable_geometric_two.mul_left (ε/4)) hcol hbound
  refine ⟨e, U, he, ?_, hpart⟩
  apply hU.trans_lt
  change (∑' j, (ε/4) * (1/2 : ℝ)^j) < ε
  rw [(hasSum_geometric_two.mul_left (ε/4)).tsum_eq]
  linarith

end ThesisCommon

