import ThesisCommon.Analysis.DualCotypeDiagonalReduction
import ThesisCommon.Analysis.EllOneTriangularParts

/-! Explicit bounded triangular operators for UPFP Propositions 3.1 and 4.3. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem HasFiniteCotype.dual_ellOne_upper_triangular
    (h : HasFiniteCotype (X →L[𝕜] 𝕜)) (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (U : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X), StrictMono e ∧
      ‖((lpRestrict 1 e).comp T).comp (lpExtend 1 e) - U‖ < ε ∧
      IsEllOneUpperPart (((lpRestrict 1 e).comp T).comp (lpExtend 1 e)) U := by
  obtain ⟨e, he, hs⟩ := h.dual_ellOne_forward_selection T (fun _ => ε/2) (fun _ => by positivity)
  let S := ((lpRestrict 1 e).comp T).comp (lpExtend 1 e)
  have htail : ∀ j, ‖((lpRestrict 1 (coordinateTail (Function.Embedding.refl ℕ) j)).comp S).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 j)‖ ≤ ε/2 :=
    fun j => (lpCompression_column_tail_bound T e j).trans (hs j).le
  obtain ⟨U, hU, hpart⟩ := exists_ellOne_upper_part S (show 0 ≤ ε/2 by positivity) htail
  exact ⟨e, U, he, hU.trans_lt (by linarith), hpart⟩

theorem HasFiniteCotype.dual_ellOne_lower_triangular
    (h : HasFiniteCotype (X →L[𝕜] 𝕜)) (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (L : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X), StrictMono e ∧
      ‖((lpRestrict 1 e).comp T).comp (lpExtend 1 e) - L‖ < ε ∧
      IsLpLowerPart (((lpRestrict 1 e).comp T).comp (lpExtend 1 e)) L := by
  obtain ⟨e, he, hs⟩ := h.dual_ellOne_backward_selection T
    (fun i => ((ε/2)/4) * (1/2 : ℝ)^i) (fun _ => by positivity)
  let S := ((lpRestrict 1 e).comp T).comp (lpExtend 1 e)
  have hentry : ∀ i j, i < j → ‖lpEntry S i j‖ < ((ε/2)/4) * (1/2 : ℝ)^i := by
    intro i j hij
    dsimp [S]
    rw [lpEntry_compression]
    exact hs i j hij
  have hearlier : ∀ j, (∑ i ∈ Finset.range j, ‖lpEntry S i j‖) ≤ ε/2 :=
    fun j => (sum_lt_of_geometric_entries (half_pos hε) _ hentry j).le
  obtain ⟨L, hL, hpart⟩ := exists_ellOne_lower_part S (show 0 ≤ ε/2 by positivity) hearlier
  exact ⟨e, L, he, hL.trans_lt (by linarith), hpart.isLpLowerPart⟩

end ThesisCommon
