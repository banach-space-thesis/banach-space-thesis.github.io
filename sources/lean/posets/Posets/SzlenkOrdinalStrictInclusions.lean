import Posets.SzlenkStrictInclusions
import Posets.SzlenkOrdinalBoundsOmegaOmega
import Posets.OrdinalInitialRetraction
import JFA.CZeroIdeals

/-! The first two strict inclusions of Proposition 3.4 on the actual
ordinal continuous-function space, with explicit complemented projections. -/

noncomputable section
open Set ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem ordinalOmega_identity_not_compact :
    ¬ IsCompactOperator (ContinuousLinearMap.id 𝕜 (OrdinalSpace 𝕜 (ω : Ordinal.{0}))) := by
  intro h
  let e := ordinalOmegaCZeroEquiv (𝕜 := 𝕜)
  have hc := (h.comp_clm e.symm.toContinuousLinearMap).clm_comp e.toContinuousLinearMap
  have he : e.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id 𝕜 (OrdinalSpace 𝕜 (ω : Ordinal.{0}))).comp
        e.symm.toContinuousLinearMap) = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  change IsCompactOperator (e.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id 𝕜 (OrdinalSpace 𝕜 (ω : Ordinal.{0}))).comp
        e.symm.toContinuousLinearMap)) at hc
  rw [he] at hc
  exact JLMS.cZero_not_finiteDimensional 𝕜 (JLMS.finiteDimensional_of_compact_identity hc)

theorem ordinal_compact_ssubset_szlenk_one {α : Ordinal.{0}} (hα : ω ≤ α) :
    {T : OrdinalSpace 𝕜 α →L[𝕜] OrdinalSpace 𝕜 α | IsCompactOperator T} ⊂
      SzlenkOperatorClass (1 : Ordinal.{0}) := by
  apply compact_ssubset_szlenk_one_of_retract
    (ordinalInitialSegmentExtension ω α) (ordinalInitialSegmentRestriction hα)
    (ordinalInitialSegment_retraction hα)
  · exact cZero_szlenkBound_omega0.id_of_equiv ordinalOmegaCZeroEquiv
  · exact ordinalOmega_identity_not_compact

theorem ordinal_szlenk_one_ssubset_two {α : Ordinal.{0}} (hα : ω ^ ω ≤ α) :
    SzlenkOperatorClass (𝕜 := 𝕜) (E := OrdinalSpace 𝕜 α) (F := OrdinalSpace 𝕜 α)
      (1 : Ordinal.{0}) ⊂ SzlenkOperatorClass (2 : Ordinal.{0}) :=
  szlenk_one_ssubset_two_of_retract
    (ordinalInitialSegmentExtension (ω ^ ω) α) (ordinalInitialSegmentRestriction hα)
    (ordinalInitialSegment_retraction hα)
    ordinalOmegaOmega_szlenkBound_omega0_sq (ordinalOmegaOmega_not_szlenkBound_omega 𝕜)

theorem omegaOmega_le_omegaOmegaSq :
    (ω ^ ω : Ordinal.{0}) ≤ ω ^ (ω ^ (2 : Ordinal.{0})) := by
  apply Ordinal.opow_le_opow_right Ordinal.omega0_pos
  simpa only [Ordinal.opow_one] using
    (Ordinal.opow_le_opow_right Ordinal.omega0_pos (by norm_num : (1 : Ordinal.{0}) ≤ 2))

theorem ordinalOmegaOmegaSq_first_strict_inclusions :
    {T : OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) →L[𝕜]
        OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) | IsCompactOperator T} ⊂
      SzlenkOperatorClass (1 : Ordinal.{0}) ∧
    SzlenkOperatorClass (𝕜 := 𝕜) (E := OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))))
      (F := OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0})))) (1 : Ordinal.{0}) ⊂
      SzlenkOperatorClass (2 : Ordinal.{0}) := by
  refine ⟨ordinal_compact_ssubset_szlenk_one ?_,
    ordinal_szlenk_one_ssubset_two omegaOmega_le_omegaOmegaSq⟩
  have h : (ω : Ordinal.{0}) ≤ ω ^ ω := by
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right Ordinal.omega0_pos Ordinal.one_lt_omega0.le
  exact h.trans omegaOmega_le_omegaOmegaSq

end Posets
