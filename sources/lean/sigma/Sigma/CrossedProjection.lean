import Sigma.FinalChargeAgreement
import Sigma.FlipJL

/-! Contractive projections from the final JL product onto its two crossed
summands, and the induced extensions of their continuous linear functionals. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup

abbrev FinalCandidate (D : EnumeratedConstruction) (side : Bool) :=
  CandidateX (D.family side) (cylinderFamily (D.baseSets (!side)))

local instance finalCandidateGroup (D : EnumeratedConstruction) (side : Bool) :
    NormedAddCommGroup (FinalCandidate D side) := inferInstance
local instance finalCandidateSpace (D : EnumeratedConstruction) (side : Bool) :
    NormedSpace ℝ (FinalCandidate D side) := inferInstance

def EnumeratedConstruction.sideProjection (D : EnumeratedConstruction) :
    (side : Bool) → FinalJLProduct D →L[ℝ] JL (D.family side)
  | false => ContinuousLinearMap.fst ℝ _ _
  | true => ContinuousLinearMap.snd ℝ _ _

def EnumeratedConstruction.sideInjection (D : EnumeratedConstruction) :
    (side : Bool) → JL (D.family side) →L[ℝ] FinalJLProduct D
  | false => ContinuousLinearMap.inl ℝ _ _
  | true => ContinuousLinearMap.inr ℝ _ _

theorem EnumeratedConstruction.sideProjection_norm_le (D : EnumeratedConstruction) (side : Bool)
    (f : FinalJLProduct D) : ‖D.sideProjection side f‖ ≤ ‖f‖ := by
  cases side
  · exact le_max_left _ _
  · exact le_max_right _ _

@[simp] theorem EnumeratedConstruction.sideProjection_injection (D : EnumeratedConstruction)
    (side : Bool) (f : JL (D.family side)) : D.sideProjection side (D.sideInjection side f) = f := by
  cases side <;> rfl

@[simp] theorem EnumeratedConstruction.otherProjection_injection (D : EnumeratedConstruction)
    (side : Bool) (f : JL (D.family side)) : D.sideProjection (!side) (D.sideInjection side f) = 0 := by
  cases side <;> rfl

def EnumeratedConstruction.cylinderProjection (D : EnumeratedConstruction) (side : Bool) :
    JL (D.family side) →L[ℝ] CylinderJL (cylinderFamily (D.baseSets side)) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    (splitJLEquiv (D.baseSets side) (D.splitSets side) (D.splits side)).toContinuousLinearMap

def EnumeratedConstruction.antisymmetricProjection (D : EnumeratedConstruction) (side : Bool) :
    JL (D.family side) →L[ℝ] antisymmetricJL (D.family side) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    (splitJLEquiv (D.baseSets side) (D.splitSets side) (D.splits side)).toContinuousLinearMap

@[simp] theorem EnumeratedConstruction.cylinderProjection_val (D : EnumeratedConstruction) (side : Bool)
    (f : JL (D.family side)) : (D.cylinderProjection side f).val = average f.val := rfl

@[simp] theorem EnumeratedConstruction.antisymmetricProjection_val (D : EnumeratedConstruction) (side : Bool)
    (f : JL (D.family side)) : (D.antisymmetricProjection side f).val = antiAverage f.val := rfl

theorem EnumeratedConstruction.antisymmetricProjection_flip (D : EnumeratedConstruction) (side : Bool)
    (f : JL (D.family side)) : D.antisymmetricProjection side (D.flipJL side f) =
      -D.antisymmetricProjection side f := by
  apply Subtype.ext
  change antiAverage (flip f.val) = -antiAverage f.val
  ext p
  simp only [antiAverage_apply,flip_apply,Bool.not_not,BoundedContinuousFunction.neg_apply]
  ring

def EnumeratedConstruction.crossedProjection (D : EnumeratedConstruction) (side : Bool) :
    FinalJLProduct D →L[ℝ] FinalCandidate D side :=
  ((D.cylinderProjection (!side)).comp (D.sideProjection (!side))).prod
    ((D.antisymmetricProjection side).comp (D.sideProjection side))

theorem EnumeratedConstruction.crossedProjection_norm_le (D : EnumeratedConstruction) (side : Bool)
    (f : FinalJLProduct D) : ‖D.crossedProjection side f‖ ≤ ‖f‖ := by
  change max ‖average (D.sideProjection (!side) f).val‖
    ‖antiAverage (D.sideProjection side f).val‖ ≤ ‖f‖
  exact max_le ((average_norm_le _).trans (D.sideProjection_norm_le (!side) f))
    ((antiAverage_norm_le _).trans (D.sideProjection_norm_le side f))

@[simp] theorem EnumeratedConstruction.crossedProjection_injection (D : EnumeratedConstruction)
    (side : Bool) (f : JL (D.family side)) :
    D.crossedProjection side (D.sideInjection side f) = (0,D.antisymmetricProjection side f) := by
  change (D.cylinderProjection (!side) (D.sideProjection (!side) (D.sideInjection side f)),
    D.antisymmetricProjection side (D.sideProjection side (D.sideInjection side f))) = _
  simp only [D.sideProjection_injection,D.otherProjection_injection,map_zero]

def EnumeratedConstruction.extendCrossedFunctional (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) : FinalJLProduct D →L[ℝ] ℝ :=
  φ.comp (D.crossedProjection side)

theorem EnumeratedConstruction.extendCrossedFunctional_norm_le (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) : ‖D.extendCrossedFunctional side φ‖ ≤ ‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
  intro f
  exact (φ.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (D.crossedProjection_norm_le side f) (norm_nonneg φ))

theorem EnumeratedConstruction.extendCrossedFunctional_antisymmetric (D : EnumeratedConstruction)
    (side : Bool) (φ : FinalCandidate D side →L[ℝ] ℝ) :
    ((D.extendCrossedFunctional side φ).comp (D.sideInjection side)).comp (D.flipJL side) =
      -(D.extendCrossedFunctional side φ).comp (D.sideInjection side) := by
  apply ContinuousLinearMap.ext
  intro f
  change φ (D.crossedProjection side (D.sideInjection side (D.flipJL side f))) =
    -φ (D.crossedProjection side (D.sideInjection side f))
  rw [D.crossedProjection_injection,D.crossedProjection_injection,D.antisymmetricProjection_flip]
  rw [← map_neg]
  apply congrArg φ
  apply Prod.ext
  · apply Subtype.ext
    ext p
    change (0 : ℝ) = -0
    norm_num
  · rfl

theorem EnumeratedConstruction.coefficients_side (D : EnumeratedConstruction)
    (φ : FinalJLProduct D →L[ℝ] ℝ) (side : Bool) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients φ (side,p) =
      indexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side)
        (φ.comp (D.sideInjection side)) p := by
  cases side <;> rfl

end SigmaNonprimarity
