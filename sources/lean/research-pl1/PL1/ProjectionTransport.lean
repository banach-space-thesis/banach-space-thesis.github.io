import PL1.WeakSchur
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Transport of projection properties along Banach-space isomorphisms

This is the abstract transport step needed after constructing the projection on
an auxiliary space and identifying that space with the actual interval L1.
An arbitrary continuous linear equivalence transports the range properties;
a linear isometry equivalence additionally preserves the exact operator norm.
-/

noncomputable section

namespace PL1

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]

/-- Conjugating an operator by a continuous linear equivalence. -/
def conjugateOperator (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) : F →L[𝕜] F :=
  e.toContinuousLinearMap.comp (P.comp e.symm.toContinuousLinearMap)

@[simp]
theorem conjugateOperator_apply (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) (x : F) :
    conjugateOperator e P x = e (P (e.symm x)) := rfl

@[simp]
theorem conjugateOperator_symm (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) :
    conjugateOperator e.symm (conjugateOperator e P) = P := by
  ext x
  simp

/-- Conjugating a projection produces a projection. -/
theorem IsProjection.conjugate {P : E →L[𝕜] E} (hP : IsProjection P)
    (e : E ≃L[𝕜] F) : IsProjection (conjugateOperator e P) := by
  ext x
  have h := DFunLike.congr_fun hP (e.symm x)
  change P (P (e.symm x)) = P (e.symm x) at h
  simp only [ContinuousLinearMap.comp_apply, conjugateOperator_apply,
    ContinuousLinearEquiv.symm_apply_apply, h]

theorem isProjection_conjugate_iff (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) :
    IsProjection (conjugateOperator e P) ↔ IsProjection P := by
  constructor
  · intro h
    simpa using h.conjugate e.symm
  · exact fun h => h.conjugate e

/-- Conjugation preserves the Dunford–Pettis property. -/
theorem IsDunfordPettis.conjugate {P : E →L[𝕜] E} (hP : IsDunfordPettis P)
    (e : E ≃L[𝕜] F) : IsDunfordPettis (conjugateOperator e P) :=
  (hP.comp_right e.symm.toContinuousLinearMap).comp_left e.toContinuousLinearMap

theorem isDunfordPettis_conjugate_iff (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) :
    IsDunfordPettis (conjugateOperator e P) ↔ IsDunfordPettis P := by
  constructor
  · intro h
    simpa using h.conjugate e.symm
  · exact fun h => h.conjugate e

/-- The range of the transported operator is exactly the image of the old range. -/
theorem conjugateOperator_range (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) :
    P.range.map e.toLinearMap = (conjugateOperator e P).range := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz⟩, hy⟩
    change P z = y at hz
    change e y = x at hy
    refine ⟨e z, ?_⟩
    change e (P (e.symm (e z))) = x
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hz] using hy
  · rintro ⟨z, hz⟩
    refine ⟨P (e.symm z), ⟨e.symm z, rfl⟩, ?_⟩
    exact hz

/-- The original and transported ranges are continuously linearly equivalent. -/
def conjugateRangeEquiv (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) :
    P.range ≃L[𝕜] (conjugateOperator e P).range :=
  e.ofSubmodules _ _ (conjugateOperator_range e P)

theorem hasSchurProperty_conjugate_range_iff (e : E ≃L[𝕜] F)
    (P : E →L[𝕜] E) :
    HasSchurProperty 𝕜 (conjugateOperator e P).range ↔
      HasSchurProperty 𝕜 P.range :=
  (hasSchurProperty_equiv_iff (conjugateRangeEquiv e P)).symm

theorem isClosed_conjugate_range_iff (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) :
    IsClosed ((conjugateOperator e P).range : Set F) ↔
      IsClosed (P.range : Set E) := by
  rw [← conjugateOperator_range, Submodule.map_coe]
  exact e.isClosed_image

/-- Finite dimensionality of the actual range is unchanged by conjugation. -/
theorem finiteDimensional_conjugate_range_iff (e : E ≃L[𝕜] F)
    (P : E →L[𝕜] E) :
    FiniteDimensional 𝕜 (conjugateOperator e P).range ↔
      FiniteDimensional 𝕜 P.range := by
  constructor
  · intro h
    let := h
    exact (conjugateRangeEquiv e P).symm.toLinearEquiv.finiteDimensional
  · intro h
    let := h
    exact (conjugateRangeEquiv e P).toLinearEquiv.finiteDimensional

/-- Isomorphic-copy containment is invariant under an isomorphism of ambient spaces. -/
theorem ContainsIsomorphicCopy.map (h : ContainsIsomorphicCopy 𝕜 D E)
    (e : E ≃L[𝕜] F) : ContainsIsomorphicCopy 𝕜 D F := by
  obtain ⟨V, hclosed, ⟨f⟩⟩ := h
  refine ⟨V.map e.toLinearMap, ?_, ⟨f.trans (e.submoduleMap V)⟩⟩
  rw [Submodule.map_coe]
  exact e.isClosed_image.mpr hclosed

theorem containsIsomorphicCopy_equiv_iff (e : E ≃L[𝕜] F) :
    ContainsIsomorphicCopy 𝕜 D E ↔ ContainsIsomorphicCopy 𝕜 D F :=
  ⟨fun h => h.map e, fun h => h.map e.symm⟩

theorem containsIsomorphicCopy_conjugate_range_iff (e : E ≃L[𝕜] F)
    (P : E →L[𝕜] E) :
    ContainsIsomorphicCopy 𝕜 D (conjugateOperator e P).range ↔
      ContainsIsomorphicCopy 𝕜 D P.range :=
  (containsIsomorphicCopy_equiv_iff (D := D) (conjugateRangeEquiv e P)).symm

/-- Isometric conjugation preserves the exact operator norm, including on the zero space. -/
theorem norm_conjugateOperator_isometry (e : E ≃ₗᵢ[𝕜] F) (P : E →L[𝕜] E) :
    ‖conjugateOperator e.toContinuousLinearEquiv P‖ = ‖P‖ := by
  change ‖(e : E →L[𝕜] F).comp (P.comp (e.symm : F →L[𝕜] E))‖ = ‖P‖
  simp only [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end PL1
