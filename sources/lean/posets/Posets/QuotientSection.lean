import Posets.CommonQuotientSection
import Posets.ScalarQuotientNorm
import PosetsCommon.SeparableOperatorIdeal

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

variable {P : Type} [PartialOrder P] [Countable P] [Nonempty P]
  {X : BoundedExtension P → Type} [∀ p, NormedAddCommGroup (X p)]
  [∀ p, NormedSpace 𝕜 (X p)] [∀ p, CompleteSpace (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)

theorem scalarQuotientMap_rightInverse :
    Function.RightInverse (incidenceLift (middleFewOperators h)) (scalarQuotientMap h) :=
  commonScalarQuotientMap_rightInverse (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h)

theorem norm_incidenceLift (T : oppositeIncidenceSubalgebra 𝕜 P) :
    ‖incidenceLift (middleFewOperators h) T‖ = ‖T‖ :=
  common_norm_incidenceLift (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h) T

theorem incidenceLift_isometry : Isometry (incidenceLift (middleFewOperators h)) :=
  common_incidenceLift_isometry (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h)

theorem scalarQuotientMap_mul
    (S T : DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) :
    scalarQuotientMap h (S * T) = scalarQuotientMap h S * scalarQuotientMap h T :=
  commonScalarQuotientMap_mul (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h) S T

def scalarQuotientHom : BoundedHom 𝕜
    (DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) (oppositeIncidenceSubalgebra 𝕜 P) where
  toContinuousLinearMap := scalarQuotientMap h
  map_mul' := scalarQuotientMap_mul h

theorem lemma_6_17_proof (𝕜 : Type) [RCLike 𝕜] (P : Type) [PartialOrder P]
    [Countable P] [Infinite P] (X : BoundedExtension P → Type)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] (ι : ∀ s t, X s →L[𝕜] X t) : Lemma_6_17 𝕜 P X ι := by
  intro h
  exact ⟨oppositeIncidenceSubalgebra 𝕜 P, rfl, incidenceLiftHom (middleFewOperators h),
    incidenceLift_isometry h, incidenceLift_block (middleFewOperators h)⟩

theorem lemma_6_21_proof (𝕜 : Type) [RCLike 𝕜] (P : Type) [PartialOrder P]
    [Countable P] [Infinite P] (X : BoundedExtension P → Type)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] (ι : ∀ s t, X s →L[𝕜] X t) : Lemma_6_21 𝕜 P X ι := by
  intro h
  exact ⟨oppositeIncidenceSubalgebra 𝕜 P, rfl, scalarQuotientHom h,
    norm_scalarQuotientMap h, scalarQuotientMap_eq_zero_iff h, scalarQuotientMap_remainder h⟩

end Posets
