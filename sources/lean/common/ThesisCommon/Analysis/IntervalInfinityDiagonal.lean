import ThesisCommon.Analysis.IntervalInfinitySelection
import ThesisCommon.Analysis.LowerBlockAlgebra
import ThesisCommon.Analysis.SequenceOffDiagonal

/-! LPCK 4.4 for C[0,1]. Nested restrictions make every strict-lower
row sum small. Genuine lower action makes this an operator-norm estimate
on all bounded sequences. Contractive block insertions preserve the bound. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem interval_infinity_lower_diagonal_blocks
    (L : EllInfinitySum (IntervalContinuous 𝕜) →L[𝕜] EllInfinitySum (IntervalContinuous 𝕜))
    (hL : IsLpLowerPart L L) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → IntervalChain), StrictMono e ∧
      ∀ (G : ℕ → IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (hG : ∀ k, ‖G k‖ ≤ 1),
      let S := ((lpBlockRead ∞ e (fun k => intervalChainRead (𝕜 := 𝕜) (c k))
        (fun k => norm_intervalChainRead_le (𝕜 := 𝕜) (c k))).comp L).comp (lpBlockInsert ∞ e G hG)
      ‖S-lpDiagonalPart S‖ < ε := by
  let δ : ℕ → ℝ := fun i => (ε/4) * (1/2 : ℝ)^i
  obtain ⟨e, c, he, hs⟩ := interval_infinity_upper_selection L δ
    (fun _ => by dsimp [δ]; positivity)
  refine ⟨e, c, he, ?_⟩
  intro G hG
  let F : ℕ → IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 :=
    fun k => intervalChainRead (c k)
  have hF : ∀ k, ‖F k‖ ≤ 1 := fun k => norm_intervalChainRead_le (c k)
  let S := ((lpBlockRead ∞ e F hF).comp L).comp (lpBlockInsert ∞ e G hG)
  have hlower : IsLpLowerPart S S := hL.block_compression e he F G hF hG
  have hentry : ∀ i j, i < j → ‖lpEntry S j i‖ ≤ δ i := by
    intro i j hij
    change ‖lpEntry (((lpBlockRead ∞ e F hF).comp L).comp (lpBlockInsert ∞ e G hG)) j i‖ ≤ δ i
    rw [lpEntry_block_compression]
    apply (norm_comp_right_contraction _ (G i) (hG i)).trans
    simpa only [F, lpEntry, ContinuousLinearMap.comp_assoc] using hs i j hij
  have hsum : ∀ k, (∑ i ∈ Finset.range k, ‖lpEntry S k i‖) ≤ ε/2 := by
    intro k
    calc
      _ ≤ ∑ i ∈ Finset.range k, (ε/4) * (1/2 : ℝ)^i :=
        Finset.sum_le_sum (fun i hi => hentry i k (Finset.mem_range.mp hi))
      _ = (ε/4) * ∑ i ∈ Finset.range k, (1/2 : ℝ)^i := (Finset.mul_sum ..).symm
      _ ≤ (ε/4) * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (by positivity)
      _ = ε/2 := by ring
  exact (hlower.infinity_norm_sub_diagonal_le (by positivity) hsum).trans_lt (by linarith)

theorem interval_infinity_lower_diagonal_retraction
    (L : EllInfinitySum (IntervalContinuous 𝕜) →L[𝕜] EllInfinitySum (IntervalContinuous 𝕜))
    (hL : IsLpLowerPart L L) {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : EllInfinitySum (IntervalContinuous 𝕜) →L[𝕜] EllInfinitySum (IntervalContinuous 𝕜),
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ‖(A.comp L).comp B - lpDiagonalPart ((A.comp L).comp B)‖ < ε := by
  obtain ⟨e, c, _, hs⟩ := interval_infinity_lower_diagonal_blocks L hL hε
  let F : ℕ → IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 :=
    fun k => intervalChainRead (c k)
  let G : ℕ → IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 :=
    fun k => intervalChainInsert (c k)
  have hF : ∀ k, ‖F k‖ ≤ 1 := fun k => norm_intervalChainRead_le (c k)
  have hG : ∀ k, ‖G k‖ ≤ 1 := fun k => norm_intervalChainInsert_le (c k)
  exact ⟨lpBlockRead ∞ e F hF, lpBlockInsert ∞ e G hG,
    lpBlockRead_comp_insert ∞ e F G hF hG (fun k => intervalChainRead_comp_insert (c k)),
    norm_lpBlockRead_le ∞ e F hF, norm_lpBlockInsert_le ∞ e G hG, hs G hG⟩

end ThesisCommon
