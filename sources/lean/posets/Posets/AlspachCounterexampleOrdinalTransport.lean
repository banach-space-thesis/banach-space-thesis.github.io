import Posets.AlspachCounterexampleOrdinalWolfe
import Posets.WolfeTransportOperators

/-! Put the Alspach operator on an actual ordinal C₀-domain, retaining
the quantitative Wolfe upper bounds at every positive threshold. -/

noncomputable section
open Set Topology ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

abbrev AlspachOrdinalCompact := OrdinalInterval ((ω : Ordinal.{0}) ^ (ω ^ (2 : Ordinal)))

def alspachOrdinalDomainOperator : JLMS.CZero 𝕜 AlspachOrdinalCompact →L[𝕜]
    JLMS.CZero 𝕜 (alspachOrdinalRows 𝕜).Index :=
  (alspachOrdinalRows 𝕜).evaluation.comp
    (cZeroHomeomorphPull (alspachOmegaCompactRows_pointHomeomorph AlspachOrdinalBase
      alspachOrdinalBasePoint alspachOrdinalBase_ordinalDerived))

theorem alspachOrdinalPointIsometry_symm_apply
    (f : OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0})))) :
    (alspachOrdinalPointIsometry (𝕜 := 𝕜)).symm f =
      cZeroHomeomorphPull (alspachOmegaCompactRows_pointHomeomorph AlspachOrdinalBase
        alspachOrdinalBasePoint alspachOrdinalBase_ordinalDerived)
        ((JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := AlspachOrdinalCompact)) f) := by
  ext x
  rfl

theorem alspachOrdinalOperator_domain_transport :
    alspachOrdinalOperator (𝕜 := 𝕜) =
      alspachOrdinalIndexIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (alspachOrdinalDomainOperator.comp
          JLMS.compactContinuousCZeroEquiv.toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext f x
  change (alspachOrdinalIndexIsometry (𝕜 := 𝕜))
      ((alspachOrdinalRows 𝕜).evaluation ((alspachOrdinalPointIsometry (𝕜 := 𝕜)).symm f)) x = _
  rw [alspachOrdinalPointIsometry_symm_apply]
  rfl

theorem alspachOrdinalDomainOperator_wolfe_empty_below_omega_sq
    (M : JLMS.AtomicDualModel 𝕜 AlspachOrdinalCompact) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : Ordinal.{0}, γ < ω ^ (2 : Ordinal) ∧
      wolfeFamily M ε (adjointUnitBall (alspachOrdinalDomainOperator (𝕜 := 𝕜))) γ = ∅ := by
  obtain ⟨γ, hγ, hempty⟩ := alspachOrdinalEvaluation_wolfe_empty_below_omega_sq (𝕜 := 𝕜) hε
  refine ⟨γ, hγ, Set.not_nonempty_iff_eq_empty.mp ?_⟩
  intro hn
  have ht := (wolfeFamily_homeomorph_nonempty_iff (alspachOrdinalRows 𝕜).pointAtomicModel M
    (alspach_countable_compact_scattered (alspachOrdinalRows 𝕜).Point)
    (JLMS.scattered_subtype JLMS.scattered_ordinal _)
    (alspachOmegaCompactRows_pointHomeomorph AlspachOrdinalBase
      alspachOrdinalBasePoint alspachOrdinalBase_ordinalDerived)
    ε (adjointUnitBall (alspachOrdinalRows 𝕜).evaluation) γ).mp
      (by simpa only [alspachOrdinalDomainOperator, adjointUnitBall_comp] using hn)
  rw [hempty] at ht
  exact Set.not_nonempty_empty ht

end Posets
