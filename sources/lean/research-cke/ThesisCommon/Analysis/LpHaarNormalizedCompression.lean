import ThesisCommon.Analysis.LpHaarBlockCompression
import ThesisCommon.Analysis.LpHaarNormalizedBlockSelection

/-! Normalized matrix entries of the actual infinite block retraction. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal Classical
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

namespace LpHaarSequentialSplits
variable (F : LpHaarSequentialSplits)

theorem normalized_compression_coefficient
    (A B T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hA : ∀ f, Tendsto (fun m => F.toPartitionTree.backward 𝕜 p hp m f) atTop (𝓝 (A f)))
    (hB : ∀ f, Tendsto (fun m => F.toPartitionTree.forward 𝕜 p hp m f) atTop (𝓝 (B f)))
    (hiso : ∀ f, ‖B f‖ = ‖f‖)
    (n m : ℕ) (k : Fin (2 ^ n)) (l : Fin (2 ^ m)) :
    lpHaarNormalizedCoordinate 𝕜 p (some ⟨n, k⟩)
        (((A.comp T).comp B) (lpHaarNormalizedVector 𝕜 p (some ⟨m, l⟩))) =
      lpHaarNormalizedBlockEntry 𝕜 p T (F.node (lpHaarHeapIndex n k))
        (F.node (lpHaarHeapIndex m l)) := by
  simp only [lpHaarNormalizedCoordinate, lpHaarNormalizedVector,
    ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul, lpHaarRawCoordinate, lpHaarRawVector]
  rw [F.compression_coefficient 𝕜 p hp A B T hA hB]
  rw [lpHaarNormalizedBlockEntry, F.block_norm_eq 𝕜 p hp B hB hiso,
    F.block_norm_eq 𝕜 p hp B hB hiso]
  ring

end LpHaarSequentialSplits

theorem lpHaarHeapIndex_decode {j n : ℕ} {k : Fin (2 ^ n)}
    (h : lpHaarIndexEquiv j = some ⟨n, k⟩) : lpHaarHeapIndex n k + 1 = j := by
  have he := lpHaarEncode_decode j
  change lpHaarEncode (lpHaarIndexEquiv j) = j at he
  rw [h, lpHaarEncode_some] at he
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  unfold lpHaarHeapIndex
  omega

end ThesisCommon
