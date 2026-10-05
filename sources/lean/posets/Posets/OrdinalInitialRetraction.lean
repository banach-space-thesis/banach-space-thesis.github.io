import Posets.TopologyStatements
import ThesisCommon.Analysis.ContinuousMapPullback
import JLMS.OrdinalTailConstancy

/-! Every smaller ordinal interval supplies an actual complemented C(K)
subspace through restriction and constant extension past its endpoint. -/

noncomputable section
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def ordinalInitialSegmentInclusion {β α : Ordinal.{0}} (h : β ≤ α) :
    C(OrdinalInterval β, OrdinalInterval α) :=
  ⟨fun x => ⟨x.val, x.property.1, x.property.2.trans h⟩,
    continuous_subtype_val.subtype_mk _⟩

def ordinalInitialSegmentClamp (β α : Ordinal.{0}) :
    C(OrdinalInterval α, OrdinalInterval β) :=
  (JLMS.ordinalIntervalClamp β).comp ⟨Subtype.val, continuous_subtype_val⟩

def ordinalInitialSegmentExtension (β α : Ordinal.{0}) :
    OrdinalSpace 𝕜 β →L[𝕜] OrdinalSpace 𝕜 α :=
  continuousMapPullback (ordinalInitialSegmentClamp β α)

def ordinalInitialSegmentRestriction {β α : Ordinal.{0}} (h : β ≤ α) :
    OrdinalSpace 𝕜 α →L[𝕜] OrdinalSpace 𝕜 β :=
  continuousMapPullback (ordinalInitialSegmentInclusion h)

theorem ordinalInitialSegment_retraction {β α : Ordinal.{0}} (h : β ≤ α) :
    (ordinalInitialSegmentRestriction (𝕜 := 𝕜) h).comp
      (ordinalInitialSegmentExtension β α) = ContinuousLinearMap.id 𝕜 (OrdinalSpace 𝕜 β) := by
  ext f x
  change f (JLMS.ordinalIntervalClamp β x.val) = f x
  congr 1
  apply Subtype.ext
  exact min_eq_left x.property.2

end Posets
