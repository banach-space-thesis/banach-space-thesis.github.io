import Posets.BoundedFewOperators
import Posets.CommonScalarQuotientMap
import Posets.CountableSeparableBlocks
import Posets.IncidenceNorms

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P] [Countable P] [Nonempty P]
  {X : BoundedExtension P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)

local instance middleFamily_normedAddCommGroup :
    ∀ p : P, NormedAddCommGroup (X (middle p)) := fun _ => inferInstance

local instance middleFamily_normedSpace :
    ∀ p : P, NormedSpace 𝕜 (X (middle p)) := fun _ => inferInstance

def scalarQuotientValue
    (T : DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) : oppositeIncidenceSubalgebra 𝕜 P :=
  commonScalarQuotientValue (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h) T

theorem scalarMatrix_scalarQuotientValue
    (T : DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) :
    scalarMatrix 𝕜 (scalarQuotientValue h T).val = blockScalarMatrix (middleFewOperators h) T :=
  scalarMatrix_commonScalarQuotientValue (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h) T

theorem scalarQuotientValue_norm_le
    (T : DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) : ‖scalarQuotientValue h T‖ ≤ ‖T‖ :=
  commonScalarQuotientValue_norm_le (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h) T

/-- The contractive linear scalar-extraction map of Lemma 6.21, before proving
its multiplicativity using the section in Lemma 6.17. -/
def scalarQuotientLinear :
    (DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) →ₗ[𝕜] oppositeIncidenceSubalgebra 𝕜 P :=
  commonScalarQuotientLinear (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h)

def scalarQuotientMap :
    (DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) →L[𝕜] oppositeIncidenceSubalgebra 𝕜 P :=
  commonScalarQuotientMap (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h)

theorem scalarQuotientMap_eq_zero_iff
    (T : DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) :
    scalarQuotientMap h T = 0 ↔
      HasSeparableRange 𝕜 (DependentCZeroSum 𝕜 (fun p : P => X (middle p)))
        (DependentCZeroSum 𝕜 (fun p : P => X (middle p))) T :=
  commonScalarQuotientMap_eq_zero_iff (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h) T

theorem norm_scalarQuotientMap_le : ‖scalarQuotientMap (𝕜 := 𝕜) (P := P) h‖ ≤ 1 :=
  norm_commonScalarQuotientMap_le (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h)

theorem scalarQuotientMap_remainder
    (T : DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) (s t : P) :
    HasSeparableRange 𝕜 (X (middle t)) (X (middle s))
      (operatorBlock 𝕜 (fun p : P => X (middle p)) (fun p : P => X (middle p)) T s t -
        scalarMatrix 𝕜 (scalarQuotientMap h T).val s t • ι (middle t) (middle s)) :=
  commonScalarQuotientMap_remainder (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h) T s t

end Posets
