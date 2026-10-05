import JFA.ProjectionFactorization
import JLMS.IdentityEssentialNorm
import JLMS.FiniteRank

/-! A bounded projection has closed range and is compact precisely when that
range is finite-dimensional. Restriction to its range is the actual identity. -/

noncomputable section
open TopologicalSpace Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem projection_range_isClosed (P : E →L[𝕜] E) (hP : P.comp P = P) :
    IsClosed (LinearMap.range P.toLinearMap : Set E) := by
  have heq : (LinearMap.range P.toLinearMap : Set E) = {x | P x = x} := by
    ext x
    constructor
    · intro hx
      exact projection_fix_range P hP ⟨x, hx⟩
    · intro hx
      exact ⟨x, hx⟩
  rw [heq]
  exact isClosed_eq P.continuous continuous_id

theorem projection_compact_iff_finiteDimensional (P : E →L[𝕜] E) (hP : P.comp P = P) :
    IsCompactOperator P ↔ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap) := by
  constructor
  · intro hc
    have hcR := hc.codRestrict (fun x => (⟨x, rfl⟩ : P x ∈ LinearMap.range P.toLinearMap))
      (projection_range_isClosed P hP)
    change IsCompactOperator P.rangeRestrict at hcR
    have hcI := hcR.comp_clm (LinearMap.range P.toLinearMap).subtypeL
    have heq : P.rangeRestrict.comp (LinearMap.range P.toLinearMap).subtypeL =
        ContinuousLinearMap.id 𝕜 (LinearMap.range P.toLinearMap) := by
      apply ContinuousLinearMap.ext
      intro z
      exact Subtype.ext (projection_fix_range P hP z)
    change IsCompactOperator (P.rangeRestrict.comp (LinearMap.range P.toLinearMap).subtypeL) at hcI
    rw [heq] at hcI
    exact JLMS.finiteDimensional_of_compact_identity hcI
  · exact JLMS.isCompactOperator_of_finiteRank P

end JFA
