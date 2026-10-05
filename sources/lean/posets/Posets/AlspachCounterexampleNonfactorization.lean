import Posets.AlspachCounterexampleOrdinalTransport
import Posets.WolfePreservationNecessary
import ThesisCommon.Analysis.OrdinalBakerLocality

/-! The actual Alspach surjection does not factor the identity on its
domain. The proof compares the necessary uniform Wolfe scale with the
quantitative upper bounds proved from the explicit probability rows. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem alspachOrdinalDomainOperator_no_factorization :
    ¬ ∃ S : JLMS.CZero 𝕜 AlspachOrdinalCompact →L[𝕜] JLMS.CZero 𝕜 AlspachOrdinalCompact,
      ∃ R : JLMS.CZero 𝕜 (alspachOrdinalRows 𝕜).Index →L[𝕜] JLMS.CZero 𝕜 AlspachOrdinalCompact,
        R.comp (alspachOrdinalDomainOperator.comp S) =
          ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 AlspachOrdinalCompact) := by
  letI : Countable AlspachOrdinalCompact := separableCountReference_countable
  letI : MetrizableSpace AlspachOrdinalCompact := alspach_countable_compact_metrizable _
  letI : MetricSpace AlspachOrdinalCompact := TopologicalSpace.metrizableSpaceMetric _
  intro ⟨S, R, hfactor⟩
  have hK : JLMS.IsScattered AlspachOrdinalCompact :=
    JLMS.scattered_subtype JLMS.scattered_ordinal _
  have hKL : JLMS.IsScattered (AlspachOrdinalCompact × AlspachOrdinalCompact) :=
    alspach_countable_compact_scattered _
  let M : JLMS.AtomicDualModel 𝕜 AlspachOrdinalCompact := (JLMS.exists_atomicDualModel hK).some
  let P : JLMS.AtomicDualModel 𝕜 (AlspachOrdinalCompact × AlspachOrdinalCompact) :=
    (JLMS.exists_atomicDualModel hKL).some
  have hcut (a : AlspachOrdinalCompact) : IsClopen (Iic a) :=
    (ordinal_isClopen_Iic a.val).preimage continuous_subtype_val
  have hrank : (ordinalDerived (univ : Set AlspachOrdinalCompact)
      ((ω : Ordinal.{0}) ^ (2 : Ordinal))).Nonempty := by
    rw [alspach_ordinalInterval_power_ordinalDerived _
      (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)]
    exact singleton_nonempty _
  obtain ⟨ε, hε, hnecessary⟩ := wolfe_ordinal_factorization_necessary_omega_sq
    M M P hKL hcut (alspachOrdinalDomainOperator (𝕜 := 𝕜)) R S hfactor isClosed_univ hrank
  obtain ⟨γ, hγ, hempty⟩ := alspachOrdinalDomainOperator_wolfe_empty_below_omega_sq M hε
  have hnonempty : (wolfeFamily M ε (adjointUnitBall (alspachOrdinalDomainOperator (𝕜 := 𝕜))) γ).Nonempty := by
    exact hnecessary γ hγ
  rw [hempty] at hnonempty
  exact Set.not_nonempty_empty hnonempty

theorem alspachOrdinalOperator_doesNotFactorIdentity :
    DoesNotFactorIdentity 𝕜 (alspachOrdinalOperator (𝕜 := 𝕜))
      (OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0})))) := by
  intro ⟨A, B, hfactor⟩
  let eC := JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := AlspachOrdinalCompact)
  let eI := alspachOrdinalIndexIsometry (𝕜 := 𝕜)
  let S := eC.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp eC.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let R := eC.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (B.comp eI.toContinuousLinearEquiv.toContinuousLinearMap)
  apply alspachOrdinalDomainOperator_no_factorization (𝕜 := 𝕜)
  refine ⟨S, R, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  have he (g : OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0})))) :
      eI (alspachOrdinalDomainOperator (eC g)) = alspachOrdinalOperator g :=
    (DFunLike.congr_fun alspachOrdinalOperator_domain_transport g).symm
  have hf := DFunLike.congr_fun hfactor (eC.symm f)
  change B (alspachOrdinalOperator (A (eC.symm f))) = eC.symm f at hf
  change eC (B (eI (alspachOrdinalDomainOperator (eC (A (eC.symm f)))))) = f
  rw [he, hf, eC.apply_symm_apply]

end Posets
