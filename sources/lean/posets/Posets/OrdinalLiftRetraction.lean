import Posets.OrdinalLiftRows

/-! Every bounded-below embedding of C[0,ω^α] into a separable normed space
contains a further closed ordinal copy with an explicitly constructed left
inverse. This is the complemented-subcopy step, not an assumed projection. -/
noncomputable section
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_ordinal_subcopy_retraction [SeparableSpace E] {α : Ordinal.{0}}
    (hα : α ≠ 0) (hcα : α.card ≤ Cardinal.aleph0)
    (J : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    ∃ e : OrdinalClosedCopy (ω ^ α) (ω ^ α),
    ∃ R : E →L[𝕜] OrdinalContinuous 𝕜 (ω ^ α),
      R.comp (J.comp (ordinalCopyInsert e)) = ContinuousLinearMap.id 𝕜 _ ∧
      ‖R‖ ≤ 1 / c := by
  obtain ⟨e, μ, hμ, heval⟩ := exists_ordinalLiftRows hα hcα J hc hlower
  let R := ordinalLiftRowsOperator μ (show 0 ≤ 1 / c by positivity) hμ
  refine ⟨e, R, ?_, norm_ordinalLiftRowsOperator_le μ (by positivity) hμ⟩
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousMap.ext
  intro t
  change μ t (J (ordinalCopyInsert e a)) = a t
  rw [heval]
  change a (ordinalCopyRetraction e (e.val t)) = a t
  rw [ordinalCopyRetraction_apply]

theorem exists_ordinal_embedding_identity_factors [SeparableSpace E] {α : Ordinal.{0}}
    (hα : α ≠ 0) (hcα : α.card ≤ Cardinal.aleph0)
    (J : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    ∃ S : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] OrdinalContinuous 𝕜 (ω ^ α),
    ∃ R : E →L[𝕜] OrdinalContinuous 𝕜 (ω ^ α),
      R.comp (J.comp S) = ContinuousLinearMap.id 𝕜 _ ∧ ‖S‖ ≤ 1 ∧ ‖R‖ ≤ 1 / c := by
  obtain ⟨e, R, hR, hn⟩ := exists_ordinal_subcopy_retraction hα hcα J hc hlower
  exact ⟨ordinalCopyInsert e, R, hR, norm_ordinalCopyInsert_le e, hn⟩

end Posets
