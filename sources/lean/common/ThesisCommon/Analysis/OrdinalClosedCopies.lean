import ThesisCommon.Analysis.OrdinalExtension

/-! Contractive read/insert pairs for actual closed copies of ordinal
intervals. A continuous injection has closed image by compactness, and its
inverse on that image extends by the continuous ordinal ceiling retraction. -/
noncomputable section
open Set Topology
universe u
namespace ThesisCommon

abbrev OrdinalClosedCopy (α β : Ordinal.{u}) :=
  {f : C(OrdinalInterval β, OrdinalInterval α) // Function.Injective f}

def ordinalCopyRetraction {α β : Ordinal.{u}} (f : OrdinalClosedCopy α β) :
    C(OrdinalInterval α, OrdinalInterval β) := by
  letI : Nonempty (OrdinalInterval β) := ⟨⟨0, le_rfl, bot_le⟩⟩
  let g : OrdinalInterval β → Ordinal.{u} := fun t => (f.val t).val
  have hg : IsEmbedding g := IsEmbedding.subtypeVal.comp
    (f.val.continuous.isClosedEmbedding f.property).isEmbedding
  exact (ordinalEmbeddedRetraction hg).comp ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem ordinalCopyRetraction_apply {α β : Ordinal.{u}}
    (f : OrdinalClosedCopy α β) (t : OrdinalInterval β) :
    ordinalCopyRetraction f (f.val t) = t := by
  letI : Nonempty (OrdinalInterval β) := ⟨⟨0, le_rfl, bot_le⟩⟩
  exact ordinalEmbeddedRetraction_apply _ t

theorem isClosed_range_ordinalCopy {α β : Ordinal.{u}} (f : OrdinalClosedCopy α β) :
    IsClosed (range f.val) := (isCompact_range f.val.continuous).isClosed

variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalCopyRead {α β : Ordinal.{u}} (f : OrdinalClosedCopy α β) :
    OrdinalContinuous 𝕜 α →L[𝕜] OrdinalContinuous 𝕜 β := continuousMapPullback f.val

def ordinalCopyInsert {α β : Ordinal.{u}} (f : OrdinalClosedCopy α β) :
    OrdinalContinuous 𝕜 β →L[𝕜] OrdinalContinuous 𝕜 α :=
  continuousMapPullback (ordinalCopyRetraction f)

theorem norm_ordinalCopyRead_le {α β : Ordinal.{u}} (f : OrdinalClosedCopy α β) :
    ‖ordinalCopyRead (𝕜 := 𝕜) f‖ ≤ 1 := norm_continuousMapPullback_le _

theorem norm_ordinalCopyInsert_le {α β : Ordinal.{u}} (f : OrdinalClosedCopy α β) :
    ‖ordinalCopyInsert (𝕜 := 𝕜) f‖ ≤ 1 := norm_continuousMapPullback_le _

theorem ordinalCopyRead_comp_insert {α β : Ordinal.{u}} (f : OrdinalClosedCopy α β) :
    (ordinalCopyRead (𝕜 := 𝕜) f).comp (ordinalCopyInsert f) =
      ContinuousLinearMap.id 𝕜 (OrdinalContinuous 𝕜 β) := by
  ext g t
  change g (ordinalCopyRetraction f (f.val t)) = g t
  rw [ordinalCopyRetraction_apply]

end ThesisCommon
