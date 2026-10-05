import ThesisCommon.Analysis.SchauderSummableColumnBounds
import ThesisCommon.Analysis.JamesTreeSchauderBasis
import ThesisCommon.Analysis.ContractiveCompressionFactorization
import ThesisCommon.Analysis.JamesTreeDelayedCoordinates

/-! Summable actual unit-column errors control an operator on either completed
James-tree model. The ordered basis suffices even for the consecutive norm.
The final factor bound follows from the proved reciprocal and Neumann step. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 Y : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem norm_jamesTree_operator_le_of_summable_columns
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode))
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] Y)
    {a : DyadicTreeNode → ℝ} (ha : Summable a)
    (hcol : ∀ t, ‖T (jamesTreeUnit t)‖ ≤ a t) : ‖T‖ ≤ ∑' t, a t := by
  have han : Summable (fun n => a (dyadicTreeEnumeration n)) :=
    dyadicTreeEnumeration.summable_iff.mpr ha
  have h := (jamesTreeSchauderBasis (𝕜 := 𝕜) (p := p) hS).norm_operator_le_of_summable_columns T (K := 1)
      (fun n => (norm_jamesTreeCoordinate (dyadicTreeEnumeration n)).le) han
      (fun n => hcol (dyadicTreeEnumeration n))
  rw [dyadicTreeEnumeration.tsum_eq a] at h
  simpa only [one_mul] using h

theorem norm_jamesTree_sub_le_of_summable_columns
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode))
    (T U : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] Y)
    {a : DyadicTreeNode → ℝ} (ha : Summable a)
    (hcol : ∀ t, ‖T (jamesTreeUnit t) - U (jamesTreeUnit t)‖ ≤ a t) :
    ‖T - U‖ ≤ ∑' t, a t := by
  apply norm_jamesTree_operator_le_of_summable_columns hS (T - U) ha
  simpa only [ContinuousLinearMap.sub_apply] using hcol

theorem jamesTree_delayed_compression_factors_six
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicEnumerationInitial N : Set DyadicTreeNode))
    (e : DyadicDelayedFork) (he : JamesTreeDelayedForkClosure S e)
    (Q D R : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (hRD : R.comp D = ContinuousLinearMap.id 𝕜 _) (hR : ‖R‖ ≤ 3)
    {a : DyadicTreeNode → ℝ} (ha : Summable a) (hsum : (∑' t, a t) ≤ 1/6)
    (hcol : ∀ t, ‖jamesTreeDelayedRead e he (Q (jamesTreeUnit (e.node t))) -
      D (jamesTreeUnit t)‖ ≤ a t) : FactorsIdentityWith Q (SegmentJamesTreeSpace 𝕜 p S) 6 := by
  apply factorsIdentityWith_six_of_near_compression_left_inverse Q
    (jamesTreeDelayedRead e he) (jamesTreeDelayedInsert e he) D R hRD hR
    (norm_jamesTreeDelayedRead_le e he) (norm_jamesTreeDelayedInsert_le e he)
  apply (norm_jamesTree_sub_le_of_summable_columns hS
    ((jamesTreeDelayedRead e he).comp Q |>.comp (jamesTreeDelayedInsert e he)) D ha ?_).trans hsum
  intro t
  simpa only [ContinuousLinearMap.comp_apply, jamesTreeDelayedInsert_unit] using hcol t

end ThesisCommon
