import SurveyStatements.P4BaireAdjoint
import SurveyStatements.P4BaireDugundji
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Analysis.Normed.Operator.Completeness

/-! A continuous inverse extension for the adjoint's isometric realization.
The raw adjoint range need not be closed. We first complete that range and
embed its completion isometrically in C(W), whose image is closed. -/

noncomputable section
set_option autoImplicit false

open Set Topology UniformSpace

namespace SurveyStatements.P4

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def adjointImageRestriction (T : X →L[𝕜] Y)
    (η : Set.range (banachAdjoint T)) : C(weakClosureImage T, 𝕜) :=
  weakClosureRestriction T η.property.choose

theorem adjointImageRestriction_isometry (T : X →L[𝕜] Y)
    (hT : IsWeaklyCompactOperator 𝕜 T) :
    letI : CompactSpace (weakClosureImage T) := isCompact_iff_compactSpace.mp hT
    Isometry (adjointImageRestriction T) := by
  letI : CompactSpace (weakClosureImage T) := isCompact_iff_compactSpace.mp hT
  apply Isometry.of_dist_eq
  intro η ζ
  rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  have hsub : adjointImageRestriction T η - adjointImageRestriction T ζ =
      weakClosureRestriction T (η.property.choose - ζ.property.choose) := by
    ext y
    rfl
  rw [hsub, weakClosureRestriction_norm T hT, map_sub,
    η.property.choose_spec, ζ.property.choose_spec]

theorem adjointImageRestriction_apply (T : X →L[𝕜] Y)
    (hT : IsWeaklyCompactOperator 𝕜 T) (φ : StrongDual 𝕜 Y) :
    adjointImageRestriction T ⟨banachAdjoint T φ, φ, rfl⟩ =
      weakClosureRestriction T φ := by
  letI : CompactSpace (weakClosureImage T) := isCompact_iff_compactSpace.mp hT
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  let η : Set.range (banachAdjoint T) := ⟨banachAdjoint T φ, φ, rfl⟩
  have heq : adjointImageRestriction T η - weakClosureRestriction T φ =
      weakClosureRestriction T (η.property.choose - φ) := by
    ext y
    rfl
  change ‖adjointImageRestriction T η - weakClosureRestriction T φ‖ = 0
  rw [heq, weakClosureRestriction_norm T hT, map_sub, η.property.choose_spec]
  simp only [η, sub_self, norm_zero]

/-- The inverse on the adjoint image extends continuously to the whole C(W).
No closedness of the original adjoint range is assumed. -/
theorem weaklyCompact_adjoint_inverse_extension (T : X →L[𝕜] Y)
    (hT : IsWeaklyCompactOperator 𝕜 T) :
    ∃ G : C(C(weakClosureImage T, 𝕜), StrongDual 𝕜 X),
      ∀ φ : StrongDual 𝕜 Y,
        G (weakClosureRestriction T φ) = banachAdjoint T φ := by
  classical
  letI : CompactSpace (weakClosureImage T) := isCompact_iff_compactSpace.mp hT
  let R := Set.range (banachAdjoint T)
  let I : Completion R → C(weakClosureImage T, 𝕜) :=
    Completion.extension (adjointImageRestriction T)
  let J : Completion R → StrongDual 𝕜 X :=
    Completion.extension ((↑) : R → StrongDual 𝕜 X)
  have hI : Isometry I := (adjointImageRestriction_isometry T hT).completion_extension
  have hJ : Isometry J := (isometry_subtype_coe (s := R)).completion_extension
  let A := Set.range I
  have hA : IsClosed A := hI.isClosedEmbedding.isClosed_range
  let e : Completion R ≃ᵢ A := hI.isometryEquivOnRange
  let q : A → StrongDual 𝕜 X := fun a => J (e.symm a)
  have hq : Isometry q := hJ.comp e.symm.isometry
  obtain ⟨G, hG⟩ := exists_continuous_extension_of_isometry_closed A hA q hq
  refine ⟨G, ?_⟩
  intro φ
  let η : R := ⟨banachAdjoint T φ, φ, rfl⟩
  have hη := hG (e (η : Completion R))
  change G (I (η : Completion R)) = J (e.symm (e (η : Completion R))) at hη
  rw [e.symm_apply_apply] at hη
  dsimp only [I, J] at hη
  rw [Completion.extension_coe (adjointImageRestriction_isometry T hT).uniformContinuous,
    Completion.extension_coe (isometry_subtype_coe (s := R)).uniformContinuous] at hη
  rw [adjointImageRestriction_apply T hT φ] at hη
  exact hη

end SurveyStatements.P4
