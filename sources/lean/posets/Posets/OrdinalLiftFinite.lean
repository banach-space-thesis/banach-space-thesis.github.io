import Posets.OrdinalLiftRetraction
import JLMS.OrdinalSpaceFinite

/-! Finite compact domains require no subselection: their point-evaluation
lifts are automatically continuous. This includes exponent zero. -/
noncomputable section
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 E K : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace K] [CompactSpace K] [T2Space K] [Finite K]

theorem exists_finiteContinuous_retraction (J : C(K, 𝕜) →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    ∃ R : E →L[𝕜] C(K, 𝕜), R.comp J = ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 1 / c := by
  classical
  have hs := ordinalLiftGraphProjection_surjective J hc hlower
  let z (x : K) := (hs x).choose
  have hz (x : K) : ordinalLiftGraphProjection J (1 / c) (z x) = x := (hs x).choose_spec
  let μ : C(K, WeakDual 𝕜 E) := ⟨fun x => (z x).val.2.val, continuous_of_discreteTopology⟩
  have hμ (x : K) : ‖WeakDual.toStrongDual (μ x)‖ ≤ 1 / c := (z x).val.2.property
  let R := ordinalLiftRowsOperator μ (show 0 ≤ 1 / c by positivity) hμ
  refine ⟨R, ?_, norm_ordinalLiftRowsOperator_le μ (by positivity) hμ⟩
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousMap.ext
  intro x
  change (z x).val.2.val (J a) = a x
  exact ((z x).property a).trans (congrArg a (hz x))

end Posets

namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_countable_ordinal_embedding_identity_factors [SeparableSpace E]
    {α : Ordinal.{0}} (hcα : α.card ≤ Cardinal.aleph0)
    (J : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    ∃ S : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] OrdinalContinuous 𝕜 (ω ^ α),
    ∃ R : E →L[𝕜] OrdinalContinuous 𝕜 (ω ^ α),
      R.comp (J.comp S) = ContinuousLinearMap.id 𝕜 _ ∧ ‖S‖ ≤ 1 ∧ ‖R‖ ≤ 1 / c := by
  by_cases hα : α = 0
  · subst α
    letI instFiniteOrdinal : Finite (OrdinalInterval ((ω : Ordinal.{0}) ^ (0 : Ordinal.{0}))) :=
      JLMS.finite_ordinalInterval_of_lt_omega0 (by simp)
    obtain ⟨R, hR, hn⟩ := exists_finiteContinuous_retraction J hc hlower
    exact ⟨ContinuousLinearMap.id 𝕜 _, R, by simpa using hR,
      ContinuousLinearMap.norm_id_le, hn⟩
  · exact exists_ordinal_embedding_identity_factors hα hcα J hc hlower

end Posets


