import Posets.AlspachCounterexampleOrdinal
import Posets.AlspachCounterexampleCompactOperator
import Posets.SeparableMissingIdealCountEmbedding
import JLMS.CompactCZeroEquiv

/-! The actual surjective contraction on C[0, ω^(ω²)] supplied by Alspach's
probability rows. The separate Wolfe estimate is needed to prove that this
operator does not preserve a copy of its domain. -/

noncomputable section
open Set Topology ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def alspachContinuousHomeomorphIsometry {K L : Type*}
    [TopologicalSpace K] [TopologicalSpace L] [CompactSpace K] [CompactSpace L]
    (e : K ≃ₜ L) : C(K, 𝕜) ≃ₗᵢ[𝕜] C(L, 𝕜) where
  __ := (continuousMapHomeomorphEquiv e).toLinearEquiv
  norm_map' f := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      exact f.norm_coe_le_norm (e.symm x)
    · apply (ContinuousMap.norm_le f (norm_nonneg _)).mpr
      intro x
      have h := (continuousMapHomeomorphEquiv (𝕜 := 𝕜) e f).norm_coe_le_norm (e x)
      change ‖f (e.symm (e x))‖ ≤ _ at h
      simpa only [e.symm_apply_apply] using h

abbrev AlspachOrdinalBase := OrdinalInterval ((ω : Ordinal.{0}) ^ ω)

def alspachOrdinalBasePoint : AlspachOrdinalBase := ⟨ω ^ ω, Ordinal.zero_le _, le_rfl⟩

instance alspachOrdinalBase_countable : Countable AlspachOrdinalBase :=
  ordinalInterval_countable_of_card (omega_power_card_le_aleph0 (by simp))

theorem alspachOrdinalBase_ordinalDerived :
    ordinalDerived (univ : Set AlspachOrdinalBase) (ω : Ordinal.{0}) = {alspachOrdinalBasePoint} :=
  alspach_ordinalInterval_power_ordinalDerived ω Ordinal.omega0_ne_zero

abbrev alspachOrdinalRows (𝕜 : Type) [RCLike 𝕜] : AlspachCompactRows.{1, 0} 𝕜 :=
  alspachOmegaCompactRows AlspachOrdinalBase alspachOrdinalBasePoint

def alspachOrdinalPointIsometry :
    JLMS.CZero 𝕜 (alspachOrdinalRows 𝕜).Point ≃ₗᵢ[𝕜]
      OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) :=
  JLMS.compactContinuousCZeroEquiv.symm.trans
    (alspachContinuousHomeomorphIsometry (alspachOmegaCompactRows_pointHomeomorph
      AlspachOrdinalBase alspachOrdinalBasePoint alspachOrdinalBase_ordinalDerived))

def alspachOrdinalIndexIsometry :
    JLMS.CZero 𝕜 (alspachOrdinalRows 𝕜).Index ≃ₗᵢ[𝕜]
      OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) :=
  JLMS.compactContinuousCZeroEquiv.symm.trans
    (alspachContinuousHomeomorphIsometry (alspachOmegaCompactRows_indexHomeomorph
      AlspachOrdinalBase alspachOrdinalBasePoint alspachOrdinalBase_ordinalDerived))

def alspachOrdinalOperator :
    OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) →L[𝕜]
      OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) :=
  alspachOrdinalIndexIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((alspachOrdinalRows 𝕜).evaluation.comp
      alspachOrdinalPointIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem alspachOrdinalOperator_surjective :
    Function.Surjective (alspachOrdinalOperator (𝕜 := 𝕜)) :=
  alspachOrdinalIndexIsometry.surjective.comp
    ((alspachOrdinalRows 𝕜).evaluation_surjective.comp alspachOrdinalPointIsometry.symm.surjective)

theorem alspachOrdinalOperator_norm_le : ‖alspachOrdinalOperator (𝕜 := 𝕜)‖ ≤ 1 := by
  let eP := alspachOrdinalPointIsometry (𝕜 := 𝕜)
  let eI := alspachOrdinalIndexIsometry (𝕜 := 𝕜)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖eI ((alspachOrdinalRows 𝕜).evaluation (eP.symm f))‖ ≤ 1 * ‖f‖
  rw [eI.norm_map]
  have h := ((alspachOrdinalRows 𝕜).evaluation.le_opNorm (eP.symm f)).trans
    (mul_le_mul_of_nonneg_right (alspachOrdinalRows 𝕜).evaluation_norm_le
      (norm_nonneg (eP.symm f)))
  simpa only [eP.symm.norm_map] using h

theorem alspachOrdinalOperator_transport :
    alspachOrdinalIndexIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((alspachOrdinalOperator (𝕜 := 𝕜)).comp
        alspachOrdinalPointIsometry.toContinuousLinearEquiv.toContinuousLinearMap) =
      (alspachOrdinalRows 𝕜).evaluation := by
  let eP := alspachOrdinalPointIsometry (𝕜 := 𝕜)
  let eI := alspachOrdinalIndexIsometry (𝕜 := 𝕜)
  apply ContinuousLinearMap.ext
  intro f
  change eI.symm (eI ((alspachOrdinalRows 𝕜).evaluation (eP.symm (eP f)))) = _
  rw [eP.symm_apply_apply, eI.symm_apply_apply]

end Posets
