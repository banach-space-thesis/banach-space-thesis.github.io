import ThesisCommon.Analysis.OrdinalInfinitySelection
import ThesisCommon.Analysis.LowerBlockAlgebra
import ThesisCommon.Analysis.SequenceOffDiagonal

/-! LPCK 4.4 on characteristic-one ordinal intervals. The strict-lower row sums give an operator-norm estimate on all bounded sequences. -/
noncomputable section
open scoped ENNReal BigOperators
universe u
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α η a : Ordinal.{u}}

theorem ordinal_infinity_lower_diagonal_blocks (hD : ordinalDerived (Set.Icc 0 α) η = {a})
    (L : EllInfinitySum ((OrdinalContinuous 𝕜 α)) →L[𝕜] EllInfinitySum ((OrdinalContinuous 𝕜 α)))
    (hL : IsLpLowerPart L L) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → OrdinalChain α), StrictMono e ∧
      ∀ (G : ℕ → (OrdinalContinuous 𝕜 α) →L[𝕜] (OrdinalContinuous 𝕜 α)) (hG : ∀ k, ‖G k‖ ≤ 1),
      let S := ((lpBlockRead ∞ e (fun k => ordinalChainRead (𝕜 := 𝕜) (c k))
        (fun k => norm_ordinalChainRead_le (𝕜 := 𝕜) (c k))).comp L).comp (lpBlockInsert ∞ e G hG)
      ‖S-lpDiagonalPart S‖ < ε := by
  let δ : ℕ → ℝ := fun i => (ε/4) * (1/2 : ℝ)^i
  obtain ⟨e, c, he, hs⟩ := ordinal_infinity_upper_selection hD L δ
    (fun _ => by dsimp [δ]; positivity)
  refine ⟨e, c, he, ?_⟩
  intro G hG
  let F : ℕ → (OrdinalContinuous 𝕜 α) →L[𝕜] (OrdinalContinuous 𝕜 α) :=
    fun k => ordinalChainRead (c k)
  have hF : ∀ k, ‖F k‖ ≤ 1 := fun k => norm_ordinalChainRead_le (c k)
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

theorem ordinal_infinity_lower_diagonal_retraction (hD : ordinalDerived (Set.Icc 0 α) η = {a})
    (L : EllInfinitySum ((OrdinalContinuous 𝕜 α)) →L[𝕜] EllInfinitySum ((OrdinalContinuous 𝕜 α)))
    (hL : IsLpLowerPart L L) {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : EllInfinitySum ((OrdinalContinuous 𝕜 α)) →L[𝕜] EllInfinitySum ((OrdinalContinuous 𝕜 α)),
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ‖(A.comp L).comp B - lpDiagonalPart ((A.comp L).comp B)‖ < ε := by
  obtain ⟨e, c, _, hs⟩ := ordinal_infinity_lower_diagonal_blocks hD L hL hε
  let F : ℕ → (OrdinalContinuous 𝕜 α) →L[𝕜] (OrdinalContinuous 𝕜 α) :=
    fun k => ordinalChainRead (c k)
  let G : ℕ → (OrdinalContinuous 𝕜 α) →L[𝕜] (OrdinalContinuous 𝕜 α) :=
    fun k => ordinalChainInsert (c k)
  have hF : ∀ k, ‖F k‖ ≤ 1 := fun k => norm_ordinalChainRead_le (c k)
  have hG : ∀ k, ‖G k‖ ≤ 1 := fun k => norm_ordinalChainInsert_le (c k)
  exact ⟨lpBlockRead ∞ e F hF, lpBlockInsert ∞ e G hG,
    lpBlockRead_comp_insert ∞ e F G hF hG (fun k => ordinalChainRead_comp_insert (c k)),
    norm_lpBlockRead_le ∞ e F hF, norm_lpBlockInsert_le ∞ e G hG, hs G hG⟩

end ThesisCommon

