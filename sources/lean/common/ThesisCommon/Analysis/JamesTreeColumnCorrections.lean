import ThesisCommon.Analysis.JamesTreeCoordinates
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! An actual norm-convergent series of coordinate rank-one operators.
It changes each James-tree unit column by the prescribed summable vector. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeColumnCorrectionTerm
    (d : DyadicTreeNode → SegmentJamesTreeSpace 𝕜 p S) (t : DyadicTreeNode) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  (jamesTreeCoordinate t).smulRight (d t)

theorem norm_jamesTreeColumnCorrectionTerm
    (d : DyadicTreeNode → SegmentJamesTreeSpace 𝕜 p S) (t : DyadicTreeNode) :
    ‖jamesTreeColumnCorrectionTerm d t‖ = ‖d t‖ := by
  simp only [jamesTreeColumnCorrectionTerm, ContinuousLinearMap.norm_smulRight_apply,
    norm_jamesTreeCoordinate, one_mul]

theorem summable_jamesTreeColumnCorrectionTerm
    (d : DyadicTreeNode → SegmentJamesTreeSpace 𝕜 p S)
    (hd : Summable (fun t => ‖d t‖)) : Summable (jamesTreeColumnCorrectionTerm d) :=
  hd.of_norm_bounded (fun t => (norm_jamesTreeColumnCorrectionTerm d t).le)

def jamesTreeColumnCorrection (d : DyadicTreeNode → SegmentJamesTreeSpace 𝕜 p S) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ∑' t, jamesTreeColumnCorrectionTerm d t

theorem norm_jamesTreeColumnCorrection_le
    (d : DyadicTreeNode → SegmentJamesTreeSpace 𝕜 p S)
    (hd : Summable (fun t => ‖d t‖)) : ‖jamesTreeColumnCorrection d‖ ≤ ∑' t, ‖d t‖ := by
  have hn : Summable (fun t => ‖jamesTreeColumnCorrectionTerm d t‖) := by
    simpa only [norm_jamesTreeColumnCorrectionTerm] using hd
  simpa only [jamesTreeColumnCorrection, norm_jamesTreeColumnCorrectionTerm] using
    norm_tsum_le_tsum_norm hn

theorem jamesTreeColumnCorrection_unit
    (d : DyadicTreeNode → SegmentJamesTreeSpace 𝕜 p S)
    (hd : Summable (fun t => ‖d t‖)) (u : DyadicTreeNode) :
    jamesTreeColumnCorrection d (jamesTreeUnit u) = d u := by
  let ev := ContinuousLinearMap.apply 𝕜 (SegmentJamesTreeSpace 𝕜 p S)
    (jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) u)
  change ev (∑' t, jamesTreeColumnCorrectionTerm d t) = _
  rw [ev.map_tsum (summable_jamesTreeColumnCorrectionTerm d hd), tsum_eq_single u]
  · simp [ev, jamesTreeColumnCorrectionTerm, jamesTreeCoordinate_unit]
  · intro t htu
    simp [ev, jamesTreeColumnCorrectionTerm, jamesTreeCoordinate_unit, htu]

end ThesisCommon
