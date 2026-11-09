import PL1.ProjectionTransport
import PL1.RNPBridge

/-! # Transporting a projection through a contractive retraction

An isometric embedding with a contractive left inverse suffices to put the
constructed projection on interval L1 while preserving its norm bound and range.
No isomorphism of the entire ambient spaces is required.
-/

noncomputable section
namespace PL1

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

structure ContractiveRetract where
  embedding : E →ₗᵢ[𝕜] F
  retraction : F →L[𝕜] E
  left_inv : ∀ x, retraction (embedding x) = x
  norm_retraction_le : ‖retraction‖ ≤ 1

namespace ContractiveRetract
variable {𝕜 E F} (R : ContractiveRetract 𝕜 E F)

def transport (P : E →L[𝕜] E) : F →L[𝕜] F :=
  R.embedding.toContinuousLinearMap.comp (P.comp R.retraction)

@[simp] theorem transport_apply (P : E →L[𝕜] E) (x : F) :
    R.transport P x = R.embedding (P (R.retraction x)) := rfl

theorem norm_transport_le (P : E →L[𝕜] E) : ‖R.transport P‖ ≤ ‖P‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P)
  intro x
  change ‖R.embedding (P (R.retraction x))‖ ≤ ‖P‖ * ‖x‖
  rw [R.embedding.norm_map]
  exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((R.retraction.le_opNorm x).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right R.norm_retraction_le (norm_nonneg x)))
    (norm_nonneg P))

theorem isProjection {P : E →L[𝕜] E} (hP : IsProjection P) :
    IsProjection (R.transport P) := by
  ext x
  have h := DFunLike.congr_fun hP (R.retraction x)
  change P (P (R.retraction x)) = P (R.retraction x) at h
  change R.embedding (P (R.retraction (R.embedding (P (R.retraction x))))) = _
  rw [R.left_inv, h]
  rfl

theorem isDunfordPettis {P : E →L[𝕜] E} (hP : IsDunfordPettis P) :
    IsDunfordPettis (R.transport P) :=
  (hP.comp_right R.retraction).comp_left R.embedding.toContinuousLinearMap

def rangeForward (P : E →L[𝕜] E) : P.range →L[𝕜] (R.transport P).range :=
  (R.embedding.toContinuousLinearMap.comp P.range.subtypeL).codRestrict _ (by
    rintro ⟨x, y, hy⟩
    refine ⟨R.embedding y, ?_⟩
    change R.embedding (P (R.retraction (R.embedding y))) = R.embedding x
    rw [R.left_inv]
    exact congrArg R.embedding hy)

def rangeBackward (P : E →L[𝕜] E) : (R.transport P).range →L[𝕜] P.range :=
  (R.retraction.comp (R.transport P).range.subtypeL).codRestrict _ (by
    rintro ⟨x, y, hy⟩
    refine ⟨R.retraction y, ?_⟩
    change P (R.retraction y) = R.retraction x
    rw [← hy]
    exact (R.left_inv _).symm)

def rangeEquiv (P : E →L[𝕜] E) : P.range ≃L[𝕜] (R.transport P).range :=
  ContinuousLinearEquiv.equivOfInverse (R.rangeForward P) (R.rangeBackward P)
    (by
      intro x
      apply Subtype.ext
      exact R.left_inv x)
    (by
      rintro ⟨x, y, hy⟩
      apply Subtype.ext
      change R.embedding (R.retraction x) = x
      rw [← hy]
      change R.embedding (R.retraction (R.embedding (P (R.retraction y)))) = _
      rw [R.left_inv]
      rfl)

theorem rangeEquiv_norm (P : E →L[𝕜] E) (x : P.range) :
    ‖R.rangeEquiv P x‖ = ‖x‖ := R.embedding.norm_map x

theorem hasSchurProperty_range_iff (P : E →L[𝕜] E) :
    HasSchurProperty 𝕜 (R.transport P).range ↔ HasSchurProperty 𝕜 P.range :=
  (hasSchurProperty_equiv_iff (R.rangeEquiv P)).symm

theorem containsIsomorphicCopy_range_iff
    {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D] (P : E →L[𝕜] E) :
    ContainsIsomorphicCopy 𝕜 D (R.transport P).range ↔ ContainsIsomorphicCopy 𝕜 D P.range :=
  (containsIsomorphicCopy_equiv_iff (D := D) (R.rangeEquiv P)).symm

theorem finiteDimensional_range_iff (P : E →L[𝕜] E) :
    FiniteDimensional 𝕜 (R.transport P).range ↔ FiniteDimensional 𝕜 P.range := by
  constructor
  · intro h
    let := h
    exact (R.rangeEquiv P).symm.toLinearEquiv.finiteDimensional
  · intro h
    let := h
    exact (R.rangeEquiv P).toLinearEquiv.finiteDimensional

end ContractiveRetract
end PL1
