import ThesisCommon.Analysis.DualCotypeSelection
import ThesisCommon.Analysis.SequenceBlockColumnBounds
import ThesisCommon.Analysis.EllOneColumnNorm
import ThesisCommon.Analysis.CotypeUpperTriangular

/-! UPFP Proposition 5.1. First select small earlier-row entries, then
small entire future-column tails, and bound the actual diagonal error.
The forward selection uses the direct adjoint proof documented separately. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lpBlockRead_id (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ) :
    lpBlockRead q e (fun _ => ContinuousLinearMap.id 𝕜 X) (fun _ => ContinuousLinearMap.norm_id_le) =
      lpRestrict q e := by
  ext x k
  rfl

theorem lpBlockInsert_id (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ) :
    lpBlockInsert q e (fun _ => ContinuousLinearMap.id 𝕜 X) (fun _ => ContinuousLinearMap.norm_id_le) =
      lpExtend q e := by
  ext x k
  rfl

theorem lpCompression_column_tail_bound {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (T : lp (fun _ : ℕ => X) q →L[𝕜] lp (fun _ : ℕ => X) q) (e : ℕ ↪ ℕ) (j : ℕ) :
    ‖((lpRestrict q (coordinateTail (Function.Embedding.refl ℕ) j)).comp
      (((lpRestrict q e).comp T).comp (lpExtend q e))).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) q j)‖ ≤
    ‖(lpRestrict q (coordinateTail e j)).comp
      (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) q (e j)))‖ := by
  simpa only [lpBlockRead_id, lpBlockInsert_id, ContinuousLinearMap.comp_id] using
    lpBlockCompression_column_tail_bound q T e
      (fun _ => ContinuousLinearMap.id 𝕜 X) (fun _ => ContinuousLinearMap.id 𝕜 X)
      (fun _ => ContinuousLinearMap.norm_id_le) (fun _ => ContinuousLinearMap.norm_id_le) j

/-- The actual diagonal of an increasing coordinate compression is arbitrarily close. -/
theorem HasFiniteCotype.dual_ellOne_diagonal_reduction
    (h : HasFiniteCotype (X →L[𝕜] 𝕜)) (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧
      ‖((lpRestrict 1 e).comp T).comp (lpExtend 1 e) -
        lpDiagonalPart (((lpRestrict 1 e).comp T).comp (lpExtend 1 e))‖ < ε := by
  obtain ⟨e, he, hb⟩ := h.dual_ellOne_backward_selection T
    (fun i => ((ε/4)/4) * (1/2 : ℝ)^i) (fun _ => by positivity)
  let S := ((lpRestrict 1 e).comp T).comp (lpExtend 1 e)
  have hS : ∀ i j, i < j → ‖lpEntry S i j‖ < ((ε/4)/4) * (1/2 : ℝ)^i := by
    intro i j hij
    dsimp [S]
    rw [lpEntry_compression]
    exact hb i j hij
  obtain ⟨f, hf, hfsmall⟩ := h.dual_ellOne_forward_selection S
    (fun _ => ε/4) (fun _ => by positivity)
  let R := ((lpRestrict 1 f).comp S).comp (lpExtend 1 f)
  have htail : ∀ j, ‖((lpRestrict 1 (coordinateTail (Function.Embedding.refl ℕ) j)).comp R).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 j)‖ ≤ ε/4 :=
    fun j => (lpCompression_column_tail_bound S f j).trans (hfsmall j).le
  have hid : ∀ i : ℕ, i ≤ f i := by
    intro i
    induction i with
    | zero => omega
    | succ i ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hf (Nat.lt_succ_self i)))
  have hentry : ∀ i j, i < j → ‖lpEntry R i j‖ < ((ε/4)/4) * (1/2 : ℝ)^i := by
    intro i j hij
    dsimp [R]
    rw [lpEntry_compression]
    apply (hS (f i) (f j) (hf hij)).trans_le
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) (hid i))
      (by positivity)
  have hearlier : ∀ j, (∑ i ∈ Finset.range j, ‖lpEntry R i j‖) ≤ ε/4 :=
    fun j => (sum_lt_of_geometric_entries (show 0 < ε/4 by positivity) _ hentry j).le
  have hsmall : ‖R - lpDiagonalPart R‖ < ε := by
    apply lt_of_le_of_lt (ellOne_norm_sub_diagonal_le_of_tail R
      (by positivity) (by positivity) hearlier htail)
    linarith
  refine ⟨f.trans e, he.comp hf, ?_⟩
  simpa only [R, S, lpCompression_composition] using hsmall

end ThesisCommon

