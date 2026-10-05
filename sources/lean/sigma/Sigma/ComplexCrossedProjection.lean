import Sigma.ComplexFinalChargeAgreement
import Sigma.ComplexFlipJL

/-! Contractive projections from the final ComplexJL product onto its two crossed
summands, and the induced extensions of their continuous linear functionals. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup

abbrev ComplexFinalCandidate (D : ComplexEnumeratedConstruction) (side : Bool) :=
  ComplexCandidateX (D.family side) (cylinderFamily (D.baseSets (!side)))

local instance complexFinalCandidateGroup (D : ComplexEnumeratedConstruction) (side : Bool) :
    NormedAddCommGroup (ComplexFinalCandidate D side) := inferInstance
local instance complexFinalCandidateSpace (D : ComplexEnumeratedConstruction) (side : Bool) :
    NormedSpace ℂ (ComplexFinalCandidate D side) := inferInstance

def ComplexEnumeratedConstruction.sideProjection (D : ComplexEnumeratedConstruction) :
    (side : Bool) → ComplexFinalJLProduct D →L[ℂ] ComplexJL (D.family side)
  | false => ContinuousLinearMap.fst ℂ _ _
  | true => ContinuousLinearMap.snd ℂ _ _

def ComplexEnumeratedConstruction.sideInjection (D : ComplexEnumeratedConstruction) :
    (side : Bool) → ComplexJL (D.family side) →L[ℂ] ComplexFinalJLProduct D
  | false => ContinuousLinearMap.inl ℂ _ _
  | true => ContinuousLinearMap.inr ℂ _ _

theorem ComplexEnumeratedConstruction.sideProjection_norm_le (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexFinalJLProduct D) : ‖D.sideProjection side f‖ ≤ ‖f‖ := by
  cases side
  · exact le_max_left _ _
  · exact le_max_right _ _

@[simp] theorem ComplexEnumeratedConstruction.sideProjection_injection (D : ComplexEnumeratedConstruction)
    (side : Bool) (f : ComplexJL (D.family side)) : D.sideProjection side (D.sideInjection side f) = f := by
  cases side <;> rfl

@[simp] theorem ComplexEnumeratedConstruction.otherProjection_injection (D : ComplexEnumeratedConstruction)
    (side : Bool) (f : ComplexJL (D.family side)) : D.sideProjection (!side) (D.sideInjection side f) = 0 := by
  cases side <;> rfl

def ComplexEnumeratedConstruction.cylinderProjection (D : ComplexEnumeratedConstruction) (side : Bool) :
    ComplexJL (D.family side) →L[ℂ] ComplexCylinderJL (cylinderFamily (D.baseSets side)) :=
  (ContinuousLinearMap.fst ℂ _ _).comp
    (complexSplitJLEquiv (D.baseSets side) (D.splitSets side) (D.splits side)).toContinuousLinearMap

def ComplexEnumeratedConstruction.antisymmetricProjection (D : ComplexEnumeratedConstruction) (side : Bool) :
    ComplexJL (D.family side) →L[ℂ] complexAntisymmetricJL (D.family side) :=
  (ContinuousLinearMap.snd ℂ _ _).comp
    (complexSplitJLEquiv (D.baseSets side) (D.splitSets side) (D.splits side)).toContinuousLinearMap

@[simp] theorem ComplexEnumeratedConstruction.cylinderProjection_val (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexJL (D.family side)) : (D.cylinderProjection side f).val = complexAverage f.val := rfl

@[simp] theorem ComplexEnumeratedConstruction.antisymmetricProjection_val (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexJL (D.family side)) : (D.antisymmetricProjection side f).val = complexAntiAverage f.val := rfl

theorem ComplexEnumeratedConstruction.antisymmetricProjection_flip (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexJL (D.family side)) : D.antisymmetricProjection side (D.flipJL side f) =
      -D.antisymmetricProjection side f := by
  apply Subtype.ext
  change complexAntiAverage (complexFlip f.val) = -complexAntiAverage f.val
  ext p
  simp only [complexAntiAverage_apply,complexFlip_apply,Bool.not_not,BoundedContinuousFunction.neg_apply]
  ring

def ComplexEnumeratedConstruction.crossedProjection (D : ComplexEnumeratedConstruction) (side : Bool) :
    ComplexFinalJLProduct D →L[ℂ] ComplexFinalCandidate D side :=
  ((D.cylinderProjection (!side)).comp (D.sideProjection (!side))).prod
    ((D.antisymmetricProjection side).comp (D.sideProjection side))

theorem ComplexEnumeratedConstruction.crossedProjection_norm_le (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexFinalJLProduct D) : ‖D.crossedProjection side f‖ ≤ ‖f‖ := by
  change max ‖complexAverage (D.sideProjection (!side) f).val‖
    ‖complexAntiAverage (D.sideProjection side f).val‖ ≤ ‖f‖
  exact max_le ((complexAverage_norm_le _).trans (D.sideProjection_norm_le (!side) f))
    ((complexAntiAverage_norm_le _).trans (D.sideProjection_norm_le side f))

@[simp] theorem ComplexEnumeratedConstruction.crossedProjection_injection (D : ComplexEnumeratedConstruction)
    (side : Bool) (f : ComplexJL (D.family side)) :
    D.crossedProjection side (D.sideInjection side f) = (0,D.antisymmetricProjection side f) := by
  change (D.cylinderProjection (!side) (D.sideProjection (!side) (D.sideInjection side f)),
    D.antisymmetricProjection side (D.sideProjection side (D.sideInjection side f))) = _
  simp only [D.sideProjection_injection,D.otherProjection_injection,map_zero]

def ComplexEnumeratedConstruction.extendCrossedFunctional (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) : ComplexFinalJLProduct D →L[ℂ] ℂ :=
  φ.comp (D.crossedProjection side)

theorem ComplexEnumeratedConstruction.extendCrossedFunctional_norm_le (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) : ‖D.extendCrossedFunctional side φ‖ ≤ ‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
  intro f
  exact (φ.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (D.crossedProjection_norm_le side f) (norm_nonneg φ))

theorem ComplexEnumeratedConstruction.extendCrossedFunctional_antisymmetric (D : ComplexEnumeratedConstruction)
    (side : Bool) (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) :
    ((D.extendCrossedFunctional side φ).comp (D.sideInjection side)).comp (D.flipJL side) =
      -(D.extendCrossedFunctional side φ).comp (D.sideInjection side) := by
  apply ContinuousLinearMap.ext
  intro f
  change φ (D.crossedProjection side (D.sideInjection side (D.flipJL side f))) =
    -φ (D.crossedProjection side (D.sideInjection side f))
  rw [D.crossedProjection_injection,D.crossedProjection_injection,D.antisymmetricProjection_flip]
  simpa only [Prod.neg_mk,neg_zero] using (map_neg φ (0,D.antisymmetricProjection side f))

theorem ComplexEnumeratedConstruction.coefficients_side (D : ComplexEnumeratedConstruction)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) (side : Bool) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients φ (side,p) =
      complexIndexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side)
        (φ.comp (D.sideInjection side)) p := by
  cases side <;> rfl

end SigmaNonprimarity


